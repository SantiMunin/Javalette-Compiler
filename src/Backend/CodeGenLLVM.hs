{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | LLVM code generator.
module Backend.CodeGenLLVM (genCode) where

import Javalette.Abs
import Javalette.ErrM
import Backend.LLVM

import Control.Monad                    (when, void)
import qualified Control.Monad.Identity as CMI
import qualified Control.Monad.State    as CMS
import qualified Data.Map               as M

import           Data.List              (intersperse)

-- | State of code generator (addresses, labels, variables, 
-- functions, global definitions, code generated...)
data Env = E { nextAddr  :: Int
             , nextLabel :: Int
             , localvar  :: [M.Map Id (Register,Ty)]
             , functions :: M.Map Id (Ty, [Ty])
             , code      :: [Instr]
             , globalvar :: Int
             , globalDef :: [String]}

-- | Creates an initial environment.
initialEnv :: Program -> Env
initialEnv (Prog defs) = E { nextAddr  = 0
                           , nextLabel = 0
                           , localvar = [M.empty]
                           , functions = collectFunDefs defs
                           , code      = []
                           , globalDef = []
                           , globalvar = 0 }      

-- | Searches all function definitions, so they can be used regardless 
-- of the definition ordering (this allows mutual recursion).
collectFunDefs :: [TopDef] -> M.Map String (Ty, [Ty])
collectFunDefs =
  foldl (\m (FnDef ret_t (Ident id) args _) ->
    M.insert id (toPrimTy ret_t,
                 map (\(Argument t _) -> toPrimTy t) args) m) M.empty

-- | Returns the type of a function.
lookUpFunTypes :: String -> GenCode (Ty, [Ty])
lookUpFunTypes "printInt"    = return (V, [I32])
lookUpFunTypes "printDouble" = return (V,[D])
lookUpFunTypes "printString" = return (V,[Ptr I8])
lookUpFunTypes "readInt"     = return (I32,[])
lookUpFunTypes "readDouble"  = return (D,[])
lookUpFunTypes id = do
  funs <- CMS.gets functions
  case M.lookup id funs of
    Nothing -> fail $ "Function " ++ show id ++ " does not exist."
    Just  v -> return v

-- | Definition of the code generator monad. 
newtype GenCode a = GenCode { runGC :: CMS.StateT Env CMI.Identity a }
    deriving (Monad, Functor, CMS.MonadState Env)

-- | Unwraps the monad.
runGenCode :: Program -> GenCode a -> (a,Env)
runGenCode p = CMI.runIdentity . (flip CMS.runStateT) (initialEnv p) . runGC

-- | Headers of built-in functions and types. 
-- They will be written before the rest of the program.
headers :: String
headers = unlines [ "declare void @printInt(i32)"
                  , "declare void @printDouble(double)"
                  , "declare void @printString(i8*)"
                  , "declare i32 @readInt()"
                  , "declare double @readDouble()"
                  , "declare i8* @calloc(i32,i32)"
                  , ""
                  , "%arrayi32 = type {i32, i32*}"
                  , "%arraydouble = type {i32, double*}"
                  , "%arrayi1 = type {i32, i1*}"
                  , "" ]

-- | Main function, generates the program's LLVM code. 
genCode :: String -> Program -> Err String
genCode str p@(Prog defs) = do
  let (funs,s) =  runGenCode p (mapM genCodeFunction defs)
  return $ headers ++ unlines (globalDef s) ++ concatMap show funs

-- | Emits an intruction.
emit :: Instr -> GenCode ()
emit instruction = 
  CMS.modify (\env -> env { code = instruction : code env })

-- | Adds the definition of a string (which has to be global 
-- due to the LLVM's rules).
addGlobalStr :: Register -> String -> GenCode ()
addGlobalStr (Register r) s = addGlobalDef $ concat ["@",r, " = internal constant [", show $ length s + 1, "x i8] c\"", s,"\\00\""]

-- | Adds a global definition (useful for arrays).
addGlobalDef :: String -> GenCode ()
addGlobalDef s = CMS.modify (\env -> env { globalDef = globalDef env ++ [s]})
                
-- | Creates a new local register name.
freshLocal:: GenCode Register
freshLocal= do
  env <- CMS.get
  let freshR = nextAddr env
  CMS.modify (\env -> env { nextAddr = freshR + 1})
  return (Register $ show freshR)

-- | Creates a new local variable name. 
freshVar :: Ident -> Type -> GenCode Register
freshVar (Ident name) t = do
  id <- freshLocal
  env <- CMS.get
  let (x:xs) = localvar env
  CMS.modify (\env -> env { localvar = M.insert name (id, toPrimTy t) x : xs})
  return id
    where
      ty = case t of
            Array _ -> Ptr $ toPrimTy t
            _       -> toPrimTy t

-- | Creates a new global variable name.
freshGlobal :: GenCode Register
freshGlobal = do
  env <- CMS.get
  let freshR = globalvar env
  CMS.modify (\env -> env { globalvar = freshR + 1})
  return (Register (show freshR))

-- | Looks the register related to a variable.
lookUpVar :: Ident -> GenCode (Register, Ty)
lookUpVar (Ident name) = do
  localvar <- CMS.gets localvar
  search name localvar
    where
      search name [] = fail $ name ++ " was not found."
      search name (x:xs) =
        case M.lookup name x of
          Nothing -> search name xs
          Just  x -> return x

-- | Converts between a LLVM type and a code generator type.
toPrimTy :: Type -> Ty
toPrimTy t = case t of
               Int        -> I32
               Doub       -> D
               Void       -> V
               Bool       -> I1
               Array t'   -> ArrayT (toPrimTy t')

-- | Creates a new label.
freshLabel :: GenCode Label
freshLabel = do
  env <- CMS.get
  let next = nextLabel env
  CMS.modify (\env -> env { nextLabel = next + 1})
  return (IntLab next)

-- | Adds a function to the environment.
newFunction :: [Arg] -> GenCode ()
newFunction args = do
  env <- CMS.get
  CMS.modify (\env -> env { localvar = [M.empty], code = [], nextLabel = 0 })

-- | New block implies new scope of variables.
newBlock :: GenCode ()
newBlock = do
  vars <- CMS.gets localvar
  CMS.modify (\env -> env { localvar = M.empty : vars })

-- | Exiting a block implies removing the top-most scope of variables.
removeBlock :: GenCode ()
removeBlock = do
  (x:xs) <- CMS.gets localvar
  CMS.modify (\env -> env { localvar = xs })

-- | Generates the code of a function.
genCodeFunction :: TopDef -> GenCode Function
genCodeFunction (FnDef t (Ident id) args block) = do
  newFunction args
  mapM_ (\(Argument t ident@(Ident id)) -> do
           addr <- freshVar ident t
           emit $ NonTerm (IAlloc (toPrimTy t)) (Just addr)
           emit $ NonTerm (IStore addr (Reg $ Register id) (toPrimTy t)) Nothing) args 
  genCodeBlock block
  when (t == Void) (emit (Term IVRet))
  instr <- CMS.gets code       
  return $ mkFun id (toPrimTy t) (toPrimArgs args) (reverse instr)
    where
      -- | Translates a list of args to a more suitable type.
      toPrimArgs :: [Arg] -> [(Id, Ty)]
      toPrimArgs = map (\(Argument t (Ident id)) -> (id,toPrimTy t))

-- | Generates a block of statements.
genCodeBlock :: Block -> GenCode ()
genCodeBlock (SBlock stmts) = mapM_ genCodeStmt stmts

-- | Generates the code of an item (an item is a variable declaration w/without initialization).
genCodeItem :: Type -> Item -> GenCode ()
genCodeItem rawtype (NoInit id)    = do
  addr <- freshVar id rawtype
  emit $ NonTerm (IAlloc t) (Just addr)
  case rawtype of
    Int       -> emit $ NonTerm (IStore addr (Const (CI32 0))   t) Nothing
    Doub      -> emit $ NonTerm (IStore addr (Const (CD 0))     t) Nothing
    Bool      -> emit $ NonTerm (IStore addr (Const (CI1 True)) t) Nothing
    Array _   -> emit $ NonTerm (IStore addr (Const Null)       t) Nothing
    where
      t = toPrimTy rawtype

genCodeItem rawtype (Init id expr) = do
  val         <- genCodeExpr expr
  addr        <- freshVar id rawtype
  emit $ NonTerm (IAlloc t) (Just addr)
  emit $ NonTerm (IStore addr val t) Nothing
    where
      t = toPrimTy rawtype

-- | Generates the code of an statement.
genCodeStmt :: Stmt -> GenCode ()
genCodeStmt stmt = case stmt of
  Empty        -> return ()

  BStmt block  -> do
    newBlock
    genCodeBlock block
    removeBlock
  Decl type' items  -> mapM_ (genCodeItem type') items

  Ass (VarI id) expr  -> do
    (addr,ty) <- lookUpVar id
    val       <- genCodeExpr expr
    emit $ NonTerm (IStore addr val ty) Nothing 
  
  Ass (VarArr id index) expr -> do
    value    <- genCodeExpr expr
    (addr,ty@(ArrayT innerType)) <- lookUpVar id
    index'    <- genCodeExpr index
    strAddr  <- freshLocal
    arrAddr  <- freshLocal
    array    <- freshLocal
    elemAddr <- freshLocal
    element  <- freshLocal
    emit $ NonTerm (ILoad addr (Ptr ty)) (Just strAddr)
    emit $ NonTerm (GetElementPtr (Ptr ty) (Reg strAddr) [ (I32, Const (CI32 0))
                                                         , (I32, Const (CI32 1))])
                    (Just arrAddr)
    
    emit $ NonTerm (ILoad arrAddr (Ptr innerType)) (Just array)
    emit $ NonTerm (GetElementPtr (Ptr innerType) (Reg array) [(I32, index')])
                   (Just elemAddr)
    emit $ NonTerm (IStore elemAddr value innerType) Nothing

  Incr id       -> do
    (addr,ty) <- lookUpVar id
    rt   <- freshLocal
    rt2  <- freshLocal
    let  cnst = Const $ case ty of
                          D   -> CD 1
                          I32 -> CI32 1
    emit $ NonTerm (ILoad addr ty)            (Just rt)
    emit $ NonTerm (IAdd (Reg rt) cnst ty)    (Just rt2)
    emit $ NonTerm (IStore addr (Reg rt2) ty) Nothing
                           
  Decr id       -> do
    (addr,ty) <- lookUpVar id
    rt   <- freshLocal
    rt2  <- freshLocal
    let  cnst = Const $ case ty of
                          D   -> CD   (-1)
                          I32 -> CI32 (-1)
    emit $ NonTerm (ILoad addr ty)            (Just rt)
    emit $ NonTerm (IAdd (Reg rt) cnst ty)    (Just rt2)
    emit $ NonTerm (IStore addr (Reg rt2) ty) Nothing

  Ret expr@(ETyped _ t)      -> do
    e <- genCodeExpr expr
    emit $ Term (IRet e (toPrimTy t))
    
  VRet          -> emit $ Term IVRet

  Cond expr stmt  -> genCodeStmt (CondElse expr stmt Empty)
    
  CondElse expr@(ETyped e _) stmt1 stmt2  ->
      case e of
        ELitTrue  -> genCodeStmt stmt1
        ELitFalse -> genCodeStmt stmt2
        _        -> do 
               cond  <- genCodeExpr expr
               true  <- freshLabel
               false <- freshLabel
               end <- freshLabel
               emit $ Term (BrC cond true false)
               emit $ Label true
               genCodeStmt stmt1
               emit $ Term (BrU end)
               emit $ Label false
               genCodeStmt stmt2
               emit $ Term (BrU end)
               emit $ Label end

  While expr stmt  -> do
    loop <- freshLabel
    true <- freshLabel 
    end  <- freshLabel
    emit $ Term (BrU loop)
    emit $ Label loop
    cond <- genCodeExpr expr 
    emit $ Term (BrC cond true end)
    emit $ Label true
    genCodeStmt stmt
    emit $ Term (BrU loop)
    emit $ Label end

  SExp expr  -> void $ genCodeExpr expr
  For idecl expr stmt  -> undefined

-- | Generates the code of an expression.
genCodeExpr :: Expr -> GenCode Operand
genCodeExpr (ETyped expr t) = case expr of
  EVar id  -> do
    (addr,ty) <- lookUpVar id
    rr <- freshLocal
    emit $ NonTerm (ILoad addr ty) (Just rr)
    return (Reg rr)
           
  EVarArr id expr    -> do
    (addr,ty@(ArrayT innerType)) <- lookUpVar id
    index    <- genCodeExpr expr
    strAddr  <- freshLocal
    arrAddr  <- freshLocal
    array    <- freshLocal
    elemAddr <- freshLocal
    element  <- freshLocal
    emit $ NonTerm (ILoad addr (Ptr ty)) (Just strAddr)
    emit $ NonTerm (GetElementPtr (Ptr ty) (Reg strAddr) [ (I32, Const (CI32 0))
                                                         , (I32, Const (CI32 1))])
                    (Just arrAddr)
    
    emit $ NonTerm (ILoad arrAddr (Ptr innerType)) (Just array)
    emit $ NonTerm (GetElementPtr (Ptr innerType) (Reg array) [(I32, index)])
                   (Just elemAddr)
    emit $ NonTerm (ILoad elemAddr innerType) (Just element)
    return (Reg element)
    
  EArrL id           -> do
    (addr,ty) <- lookUpVar id
    rr        <- freshLocal
    strAddr   <- freshLocal
    lenAddr   <- freshLocal
    emit $ NonTerm (ILoad addr (Ptr ty)) (Just strAddr)
    emit $ NonTerm (GetElementPtr (Ptr ty) (Reg strAddr) [ (I32, Const (CI32 0))
                                                         , (I32, Const (CI32 0))])
                    (Just lenAddr)
    emit $ NonTerm (ILoad lenAddr I32) (Just rr)
    return (Reg rr)
           
  EArrI type' expr -> do
    length <- genCodeExpr expr
              
    pointerS      <- freshLocal
    sizeS         <- freshLocal
    -- %pointerS = getelementptr %str* null, i32 1
    emit $ NonTerm (GetElementPtr (Ptr (ArrayT ty')) (Const Null) [(I32, Const (CI32 1))])
           (Just pointerS)
    -- %sizeS    = ptrtoint i32* %pointerS to i32
    emit $ NonTerm (PtrToInt (Ptr ty) pointerS I32) (Just sizeS)

    voids     <- freshLocal
    str       <- freshLocal
    -- %void.s = call i8* @calloc(i32 1, i32 %sizeS)
    emit $ NonTerm (ICall (Ptr I8) "calloc" [(I32, Const (CI32 1)),(I32, Reg sizeS)]) (Just voids)
    -- %str    = bitcast i8* %void.s to str*
    emit $ NonTerm (BitCast (Ptr I8) voids (Ptr (ArrayT ty'))) (Just str)

    lenAddr <- freshLocal
    -- %lenAddr = getelementptr %array* %str, i32 0, i32 0
    emit $ NonTerm (GetElementPtr (Ptr (ArrayT ty')) (Reg str) [(I32, Const (CI32 0))
                                                              ,(I32, Const (CI32 0))])
                                                              (Just lenAddr)
    -- store i32 %length, i32* %lenAddr
    emit $ NonTerm (IStore lenAddr length I32) Nothing

         
    pointerE       <- freshLocal
    sizeE          <- freshLocal
    -- %pointerE = getelementptr ty* null, i32 1
    emit $ NonTerm (GetElementPtr (Ptr ty') (Const Null) [(I32, Const (CI32 1))]) (Just pointerE)
    -- %sizeE    = ptrtoint ty* %pointerE to i32
    emit $ NonTerm (PtrToInt (Ptr ty') pointerE I32) (Just sizeE)

    voida          <- freshLocal
    array          <- freshLocal
    -- %void.s = call i8* @calloc(i32 1, i32 %sizeE)
    emit $ NonTerm (ICall (Ptr I8) "calloc" [(I32, length),(I32, Reg sizeE)]) (Just voida)
    -- %array    = bitcast i8* %void.s to ty*
    emit $ NonTerm (BitCast (Ptr I8) voida (Ptr ty')) (Just array)
    
    arrAddr <- freshLocal
    -- %lenAddr = getelementptr %array* %str, i32 0, i32 0
    emit $ NonTerm (GetElementPtr (Ptr (ArrayT ty')) (Reg str) [(I32, Const (CI32 0))
                                                              ,(I32, Const (CI32 1))])
                                                              (Just arrAddr)
    -- store ty* %array, ty** %arrAddr
    emit $ NonTerm (IStore arrAddr (Reg array) (Ptr ty')) Nothing

    return (Reg str)
      where
        ty' = toPrimTy type'
     
  ELitInt n        -> return $ Const (CI32 n)
  ELitDoub d       -> return $ Const (CD d)
  ELitTrue         -> return $ Const (CI1 True)
  ELitFalse        -> return $ Const (CI1 False)
  EApp (Ident id) exprs    -> do
    evExprs <- mapM genCodeExpr exprs
    types  <- lookUpFunTypes id
    case t of
      Void -> do
        emit $ NonTerm (ICall (fst types) id (zip (snd types) evExprs)) Nothing
        return Emp
      t'   -> do
        rr <- freshLocal
        emit $ NonTerm (ICall (fst types) id (zip (snd types) evExprs)) (Just rr)
        return (Reg rr)

  EString str      -> do
    tmp             <- freshLocal
    loc@(Register r)             <- freshGlobal
    addGlobalStr loc str
    emit $ NonTerm (Lit (concat ["getelementptr [", show (length str + 1), "x i8]*"
                                        , " @", r ,", i32 0, i32 0"])) (Just tmp)
    
    return (Reg tmp)
  Neg expr1         -> do
    r1 <- genCodeExpr expr1
    rr <- freshLocal
    emit $ NonTerm (INeg r1 ty) (Just rr)
    return (Reg rr)

  Not expr1     -> do
    r1 <- genCodeExpr expr1
    rr <- freshLocal
    emit $ NonTerm (INot r1 I1) (Just rr)
    return (Reg rr)

  EMul expr1 mulop expr2  -> do
    r1 <- genCodeExpr expr1
    r2 <- genCodeExpr expr2
    rr <- freshLocal
    case mulop of
      Times  -> emit $ NonTerm (IMul  r1 r2 ty) (Just rr)
      Div    -> emit $ NonTerm (IDiv r1 r2 ty)  (Just rr)
      Mod    -> emit $ NonTerm (IMod  r1 r2 ty) (Just rr)
    return (Reg rr)

  EAdd expr1 addop expr2  -> do
    r1 <- genCodeExpr expr1
    r2 <- genCodeExpr expr2
    rr <- freshLocal
    case addop of
      Plus   -> emit $ NonTerm (IAdd r1 r2 ty) (Just rr)
      Minus  -> emit $ NonTerm (ISub r1 r2 ty) (Just rr)
    return (Reg rr)

  ERel expr1@(ETyped _ t') relop expr2  -> do
    r1 <- genCodeExpr expr1
    r2 <- genCodeExpr expr2
    rr <- freshLocal
    case relop of
        LTH  -> emit $ NonTerm (ILth r1 r2 (toPrimTy t')) (Just rr)
        LE   -> emit $ NonTerm (ILe  r1 r2 (toPrimTy t')) (Just rr)
        GTH  -> emit $ NonTerm (IGth r1 r2 (toPrimTy t')) (Just rr)
        GE   -> emit $ NonTerm (IGe  r1 r2 (toPrimTy t')) (Just rr)
        EQU  -> emit $ NonTerm (IEq  r1 r2 (toPrimTy t')) (Just rr)
        NE   -> emit $ NonTerm (INEq r1 r2 (toPrimTy t')) (Just rr)
    return (Reg rr)

  EAnd expr1 expr2  -> do
    r1   <- genCodeExpr expr1
    cond <- freshLocal
    emit $ NonTerm (IAlloc I1) (Just cond)
    emit $ NonTerm (IStore cond r1 I1) Nothing
    true  <- freshLabel
    end <- freshLabel
    bool <- freshLocal
    emit $ NonTerm (ILoad cond I1) (Just bool)
    emit $ Term (BrC (Reg bool) true end)
    emit $ Label true
    r2 <- genCodeExpr expr2
    emit $ NonTerm (IStore cond r2 I1) Nothing
    emit $ Term (BrU end)
    emit $ Label end
    rr <- freshLocal
    emit $ NonTerm (ILoad cond I1) (Just rr) 
    return (Reg rr)
    
  EOr expr1 expr2   -> do
    r1   <- genCodeExpr expr1
    cond <- freshLocal
    emit $ NonTerm (IAlloc I1) (Just cond)
    emit $ NonTerm (IStore cond r1 I1) Nothing
    true  <- freshLabel
    end   <- freshLabel
    bool  <- freshLocal
    emit $ NonTerm (ILoad cond I1) (Just bool)
    emit $ Term (BrC (Reg bool) end true)
    emit $ Label true
    r2 <- genCodeExpr expr2
    emit $ NonTerm (IStore cond r2 I1) Nothing
    emit $ Term (BrU end)
    emit $ Label end
    rr <- freshLocal
    emit $ NonTerm (ILoad cond I1) (Just rr) 
    return (Reg rr)

  typedExpr         -> genCodeExpr typedExpr
  where
    ty = toPrimTy t

genCodeExpr expr = error $ show expr
