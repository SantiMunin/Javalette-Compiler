{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | LLVM code generator.
module Backend.CodeGenLLVM (genCode) where

import           Backend.LLVM
  
import           Javalette.Abs
import           Javalette.ErrM
import           Internal.Types

import           Control.Monad          (foldM, forM, void, when)
import qualified Control.Monad.State    as CMS

import           Data.List              (elemIndex, intersperse, intercalate)
import qualified Data.Map               as M
import           Data.Maybe             (fromJust)

import           Data.Hashable

-- | Debugging utils.
debug  :: Bool
debug  =  True

debugger :: String -> GenCode ()
debugger str = when debug (emit $ NonTerm (Lit ("\n;; " ++ str ++ "\n")) Nothing)

-- | State of code generator (addresses, labels, variables,
-- functions, global definitions, code generated...)
data Env = E { nextAddr  :: Int
             , nextLabel :: Int
             , localvar  :: [M.Map Id (Register,Ty)]
             , code      :: [Instr]
             , globalvar :: Int
             , globalDef :: [String]
             , structs   :: M.Map Id [(Id,Ty)]
             , classes   :: M.Map Id [(Id,Ty)] }

-- | Creates an initial environment.
initialEnv :: Structs -> Classes -> Env
initialEnv structs classes =
  E { nextAddr  = 0
    , nextLabel = 0
    , localvar  = [M.empty]
    , code      = []
    , globalDef = []
    , globalvar = 0
    , structs   =
      M.foldWithKey
         (\(Ident id) fields accum
            -> M.insert id (map (\(StrField type' (Ident field))
                                   -> (field,toPrimTy type')) fields) accum) M.empty structs
    , classes   =
      M.foldWithKey
         (\(Ident id) (_,(pF,fields),_) accum
            -> M.insert id (map (\(StrField type' (Ident field))
                                   -> (field,toPrimTy type')) (pF ++ fields)) accum) M.empty classes }
-- | Definition of the code generator monad.
type GenCode a = CMS.State Env a

-- | Headers of built-in functions and types.
-- They will be written before the rest of the program.
headers :: [TopLevel]
headers = [ FunDecl V "printInt" [I32]
          , FunDecl V "printDouble" [D]
          , FunDecl V "printString" [Ptr I8]
          , FunDecl I32  "readInt" []
          , FunDecl D "readDouble" []
          , FunDecl (Ptr I8) "calloc" [I32,I32]
          , FunDecl (Ptr I8) "memcpy" [Ptr I8, Ptr I8, I32]
          , TypeDecl "arrayi32" [I32, I32, Ptr I32, Ptr I32]
          , TypeDecl "arraydouble" [I32, I32, Ptr I32, Ptr D]
          , TypeDecl "arrayi1" [I32, I32, Ptr I32, Ptr I1]
          , FunDecl (Ptr I8) "dispatcher" [I64 , Ptr (Def "ClassDescriptor")]
          , TypeDecl "ClassDescriptor" [Ptr (Def "ClassDescriptor"), Ptr (Def "ClassMethod")]
          , TypeDecl "ClassMethod" [I64, Ptr (Def "ClassMethod"), Ptr I8]]

-- | Main function, generates the program's LLVM code.
genCode :: String -> (Structs, Classes, [FnDef]) -> Err String
genCode str (structs, classes, defs) = do
  let (funs,s) =  CMS.runState (mapM genCodeFunction defs) (initialEnv structs classes)
  return $ concat [ unlines $ map show $ headers ++ userStructs ++ userClasses
                  , unlines (globalDef s)
                  , concatMap show funs ]
    where userStructs  =
            M.foldWithKey
               (\(Ident name) fields accum
                  -> accum ++ [TypeDecl name $
                               map (toPrimTy . (\(StrField t _) -> t)) fields])
               [] structs
          userClasses = 
            M.foldWithKey
              (\(Ident className) (superT, (parentFields,fields), methods) classList
                  -> concat [ classList
                            , [TypeDecl className $ Ptr (Def "ClassDescriptor"):map (toPrimTy . (\(StrField t _) -> t)) (parentFields ++ fields)] 
                            , genClassDescriptor className superT methods ]
              ) [] classes
            where genClassDescriptor className parent methods = 
                    [GlobalDecl (Def "ClassDescriptor") ("ClassDescriptor." ++ className) 
                      [(Ptr (Def "ClassDescriptor"), getParent parent)
                      , (Ptr (Def "ClassMethod"), getMethod methods)]]
                    ++ genMethodChain methods
                  getParent [] = Const Null 
                  getParent ((Ident x):_) = Global $ "ClassDescriptor." ++ x
                  getMethod [] = Const Null
                  getMethod ((MethodDef _ (Ident mName) _ _ _):_) = 
                    Global ("ClassMethod." ++ mName)
                  genMethodChain [] = []
                  genMethodChain [method] = [genMethodEntry  method Nothing]
                  genMethodChain (method:tail@((MethodDef _ (Ident next) _ _ _):_)) = genMethodChain tail ++ [genMethodEntry method (Just next)]
                  genMethodEntry (MethodDef ret_type (Ident mName) obj args _) next =
                    GlobalDecl (Def "ClassMethod") ("ClassMethod." ++ mName)
                                 [(I64, Const $ CI64 $ fromIntegral $ (hash ((tail . dropWhile (/='.')) mName))), 
                                  (Ptr (Def "ClassMethod")
                                  , case next of 
                                      Nothing -> Const Null 
                                      Just x -> Global $ ("ClassMethod."++x)),
                                  ( Ptr I8
                                  , Const (LitCode $
                                           concat ["bitcast ("
                                                  ,show (toPrimTy ret_type)
                                                  , " ("
                                                  , intercalate "," $ "i8*" : map
                                                   (show . toPrimTy . (\(Argument t _) -> t)) args
                                                  , ")* @"
                                                  , mName
                                                  , " to i8*)"]))]




-- | Emits an intruction.
emit :: Instr -> GenCode ()
emit instruction =
  CMS.modify (\env -> env { code = instruction : code env })

-- | Adds the definition of a string (which has to be global
-- due to the LLVM's rules).
addGlobalStr :: Register -> String -> GenCode ()
addGlobalStr (Register r) s =
  addGlobalDef $ concat ["@"
                        ,r
                        , " = internal constant ["
                        , show $ length s + 1
                        , "x i8] c\""
                        , s
                        ,"\\00\""]

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
               DimT ty 0  -> toPrimTy ty
               DimT ty n  -> ArrayT (toPrimTy ty) n
               Pointer (Ident id)  -> Ptr (Def id)
               Object (Ident name) objtype -> Ptr (Def name) 
               String     -> Ptr I8
-- | Creates a new label.
freshLabel :: GenCode Label
freshLabel = do
  env <- CMS.get
  let next = nextLabel env
  CMS.modify (\env -> env { nextLabel = next + 1})
  return (IntLab next)

-- | Adds a function to the environment.
newFunction :: GenCode ()
newFunction = CMS.modify
              (\env -> env { localvar = [M.empty], code = [], nextLabel = 0
                           , nextAddr = 0})

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
genCodeFunction :: FnDef -> GenCode Function
genCodeFunction (FunDef t (Ident id) args block) = do
  newFunction 
  mapM_ (\(Argument t ident@(Ident id)) -> do
           addr <- freshVar ident t
           emit $ NonTerm (IAlloc (toPrimTy t)) (Just addr)
           emit $ NonTerm (IStore addr (Reg $ Register id) (toPrimTy t)) Nothing) args
  genCodeBlock block
  when (t == Void) (emit (Term IVRet))
  instr <- CMS.gets code
  return $ mkFun id (toPrimTy t) (toPrimArgs args) (reverse instr)

genCodeFunction (MethodDef t (Ident id) (Argument objType _) args block) = do
  newFunction  
  addr <- freshVar (Ident "self") objType
  emit $ NonTerm (IAlloc (toPrimTy objType)) (Just addr)
  castedAddr <- freshLocal
  emit $ NonTerm (BitCast (Ptr I8) (Register "self") (toPrimTy objType)) (Just castedAddr)
  emit $ NonTerm (IStore addr (Reg castedAddr) (toPrimTy objType)) Nothing
  mapM_ (\(Argument t ident@(Ident id)) -> do
           addr <- freshVar ident t
           emit $ NonTerm (IAlloc (toPrimTy t)) (Just addr)
           emit $ NonTerm (IStore addr (Reg $ Register id) (toPrimTy t)) Nothing) args
  genCodeBlock block
  when (t == Void) (emit (Term IVRet))
  instr <- CMS.gets code
  return $ mkFun id (toPrimTy t) (("self", Ptr I8):toPrimArgs args) (reverse instr)

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
    DimT _ _  -> emit $ NonTerm (IStore addr (Const Undef)      t) Nothing
    Pointer _ -> emit $ NonTerm (IStore addr (Const Null)       t) Nothing
    Object name _ -> emit $ NonTerm (IStore addr (Const Null) t) Nothing
    where
      t = toPrimTy rawtype

genCodeItem rawtype (Init id expr@(ETyped innerExpr innerType)) = do
  val         <- genCodeExpr expr
  addr        <- freshVar id rawtype
  emit $ NonTerm (IAlloc ty) (Just addr)
  case ty of
    Ptr (Def name) ->
      do if innerExpr == NullC then
           emit $ NonTerm (IStore addr val ty) Nothing
         else
           do let Reg valPtr        = val
              castedPtr <- freshLocal
              emit $ NonTerm (BitCast (toPrimTy innerType) valPtr ty)
                     (Just castedPtr)
              emit $ NonTerm (IStore addr (Reg castedPtr) ty) Nothing

    _ ->  emit $ NonTerm (IStore addr val ty) Nothing

    where
      ty = toPrimTy rawtype

-- | Generate code for an LVal but only if this is a field referencing or a variable.
--   Arrays are manipulated in the calleer function.
genCodeLVal :: LVal -> GenCode Register
genCodeLVal lval  =
  case lval of
    LValVar id exprDims -> 
      do (addr,ty) <- lookUpVar id
         return addr

    LValStr var (Ident field) ->
        do (addr,ptr@(Ptr (Def name))) <- lookUpVar var
           strFields <- CMS.gets (M.lookup name . structs)
           classAttr <- CMS.gets (M.lookup name  . classes)
           let Just indx =
                 case strFields of
                   Nothing -> fmap ((+1) . fromIntegral) . elemIndex field . map fst $ (fromJust classAttr)
                   Just fields  -> fmap fromIntegral . elemIndex field . map fst $ fields
                              
           str <- freshLocal
           emit $ NonTerm (ILoad addr ptr) (Just str)

           debugger  "Calculate the address of the field"
           fieldAddr <- freshLocal
           emit $ NonTerm (GetElementPtr ptr (Reg str) [(I32, Const (CI32 0))
                                                       ,(I32, Const (CI32 indx))])
                  (Just fieldAddr)
           return fieldAddr
    _ -> error $ show lval
         
-- | Generates the code of an statement.
genCodeStmt :: Stmt -> GenCode ()
genCodeStmt stmt = case stmt of
  Empty        -> return ()

  BStmt block  -> do
    newBlock
    genCodeBlock block
    removeBlock
  Decl type' items  -> mapM_ (genCodeItem type') items

  Ass (LValTyped lval t) expr@(ETyped innerExpr innerType)  ->
       case lval of
         LValVar id exprDims ->
           do value <- genCodeExpr expr
              (addr,ty) <- lookUpVar id
              case ty of
                ArrayT ty' nDim ->
                  if null exprDims then
                    emit $ NonTerm (IStore addr value ty) Nothing
                  else
                    if length exprDims == fromIntegral nDim then
                      do elemAddr <- findArrIndex ty addr exprDims
                         emit $ NonTerm (IStore elemAddr value ty') Nothing
                    else
                      do elemAddr  <- findArrIndex ty addr exprDims
                                      
                         debugger "Set up the source array"
                         sourceStr  <- freshLocal
                         emit $ NonTerm (IAlloc ty) (Just sourceStr)
                         emit $ NonTerm (IStore sourceStr value ty) Nothing
                         
                         debugger "Get the source array of elements"
                         arrayAddr <- freshLocal
                         emit $ NonTerm (GetElementPtr (Ptr ty) (Reg sourceStr)
                                                         [(I32, Const (CI32 0))
                                                         ,(I32, Const (CI32 3))])
                                (Just arrayAddr)
                           
                         array <- freshLocal
                         emit $ NonTerm (ILoad arrayAddr (Ptr ty')) (Just array)
                         
                         debugger "Get the source length of the array"
                         lenAddr <- freshLocal
                         emit $ NonTerm (GetElementPtr (Ptr ty) (Reg sourceStr)
                                                         [(I32, Const (CI32 0))
                                                         ,(I32, Const (CI32 0))])
                                (Just lenAddr)
                           
                         len <- freshLocal
                         emit $ NonTerm (ILoad lenAddr I32) (Just len)
                         
                         debugger "Calculate the size of element"
                         pointerE       <- freshLocal
                         sizeE          <- freshLocal
                         emit $ NonTerm (GetElementPtr (Ptr ty') (Const Null)
                                                         [(I32, Const (CI32 1))])
                                (Just pointerE)
                         emit $ NonTerm (PtrToInt (Ptr ty') pointerE I32) (Just sizeE)

                         debugger "Calculate the total number of elements"
                         sizeTotal     <- freshLocal
                         emit $ NonTerm (IMul (Reg sizeE) (Reg len) I32) (Just sizeTotal)
                         
                         castArray1    <- freshLocal
                         castArray2    <- freshLocal
                         debugger "Copying memory"
                         emit $ NonTerm (BitCast (Ptr ty') array    (Ptr I8))
                                (Just castArray1)
                         emit $ NonTerm (BitCast (Ptr ty') elemAddr (Ptr I8))
                                (Just castArray2)
                         dummy <- freshLocal
                         emit $ NonTerm (ICall (Ptr I8) "@memcpy"
                                                 [(Ptr I8, Reg castArray2)
                                                 ,(Ptr I8, Reg castArray1)
                                                 ,(I32,Reg sizeTotal)])
                                (Just dummy)
                       
                Ptr (Def var)  ->
                  if  innerExpr == NullC then
                    emit $ NonTerm (IStore addr value ty) Nothing
                  else
                    do let Reg valPtr        = value
                       castedPtr <- freshLocal
                       emit $ NonTerm (BitCast (toPrimTy innerType) valPtr ty)
                              (Just castedPtr)
                       emit $ NonTerm (IStore addr (Reg castedPtr) ty) Nothing
                       
                _     ->  emit $ NonTerm (IStore addr value ty) Nothing

         LValStr _ _ ->
           do value <- genCodeExpr expr
              addr  <- genCodeLVal lval
              emit $ NonTerm (IStore addr value (toPrimTy t)) Nothing
                      
  Incr (LValTyped lval t) ->
    do addr      <- genCodeLVal lval      
       rt   <- freshLocal
       rt2  <- freshLocal
       let ty = toPrimTy t
           cnst = Const $ case ty of
                            D   -> CD   1
                            I32 -> CI32 1
       emit $ NonTerm (ILoad addr ty)            (Just rt)
       emit $ NonTerm (IAdd (Reg rt) cnst ty)    (Just rt2)
       emit $ NonTerm (IStore addr (Reg rt2) ty) Nothing

  Decr (LValTyped lval t) ->
    do addr      <- genCodeLVal lval      
       rt   <- freshLocal
       rt2  <- freshLocal
       let ty = toPrimTy t
           cnst = Const $ case ty of
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
  For idecl expr stmt  -> error "Error for not declared"

-- | Generates the code of an expression.
genCodeExpr :: Expr -> GenCode Operand
genCodeExpr (ETyped expr t) = case expr of
  Var id index -> do
    (addr,ty) <- lookUpVar id
    case ty of
      ArrayT ty' nDim ->
        if (null index) then
          do
            elem  <- freshLocal
            emit $ NonTerm (ILoad addr ty) (Just elem)
            return (Reg elem)
         else
            if length index == fromIntegral nDim then
              do
                elemAddr <- findArrIndex ty addr index
                elem <- freshLocal
                emit $ NonTerm (ILoad elemAddr ty') (Just elem)
                return (Reg elem)
            else
              do
                elemAddr <- findArrIndex ty addr index
                strAddr <- freshLocal
                emit $ NonTerm (IAlloc ty) (Just strAddr)

                debugger " Point new dimension array to old one"

                dimsArrayAddr <- freshLocal
                emit $ NonTerm (GetElementPtr (Ptr ty) (Reg addr)
                                                [(I32, Const (CI32 0))
                                                , (I32, Const(CI32 2))])
                                (Just dimsArrayAddr)
                dimsArray <- freshLocal
                emit $ NonTerm (ILoad dimsArrayAddr (Ptr I32)) (Just dimsArray)

                newDims   <- freshLocal
                emit $ NonTerm (GetElementPtr (Ptr I32) (Reg dimsArray)
                                                [(I32, Const . CI32 . fromIntegral . length $ index)])
                                (Just newDims)

                newDimsAddr <- freshLocal
                emit $ NonTerm (GetElementPtr (Ptr ty) (Reg strAddr)
                                [(I32, Const (CI32 0)), (I32, Const (CI32 2))])
                       (Just newDimsAddr)

                emit $ NonTerm (IStore newDimsAddr (Reg newDims) (Ptr I32)) Nothing
                debugger " Calculating the total length"
                arrLength <- foldM
                  (\accum idx -> do
                    dimAddr <- freshLocal
                    emit $ NonTerm (GetElementPtr (Ptr I32) (Reg dimsArray)
                                                    [(I32, idx)])
                           (Just dimAddr)
                    currentDimLen <- freshLocal
                    emit $ NonTerm (ILoad dimAddr I32) (Just currentDimLen)
                    newAccum <- freshLocal
                    emit $ NonTerm (IMul accum (Reg currentDimLen) I32)
                           (Just newAccum)
                    return (Reg newAccum)
                  ) (Const (CI32 1))
                               (map (Const . CI32) [(fromIntegral . length) index..nDim-1])
                newLengthAddr <- freshLocal
                emit $ NonTerm (GetElementPtr (Ptr ty) (Reg strAddr)
                                                [(I32, Const (CI32 0))
                                                , (I32, Const(CI32 0))])
                       (Just newLengthAddr)
                emit $ NonTerm (IStore newLengthAddr arrLength I32) Nothing
                debugger " Setting new pointer to element in old array"
                newElemAddr <- freshLocal
                emit $ NonTerm (GetElementPtr (Ptr ty) (Reg strAddr)
                                                [(I32, Const (CI32 0))
                                                , (I32, Const(CI32 3))])
                       (Just newElemAddr)
                emit $ NonTerm (IStore newElemAddr (Reg elemAddr) (Ptr ty')) Nothing
                str <- freshLocal
                emit $ NonTerm (ILoad strAddr ty) (Just str)
                return (Reg str)

      _ -> do
            elem  <- freshLocal
            emit $ NonTerm (ILoad addr ty) (Just elem)
            return (Reg elem)

  Method (Var id exprDims) (Var (Ident "length") []) -> do
    (addr, ty) <- lookUpVar id
    let indexedDims = fromIntegral $ length exprDims

    debugger "Calculating the address of the indexed dimension"
    dimArrayAddr <- freshLocal
    emit $ NonTerm (GetElementPtr (Ptr ty) (Reg addr) [(I32, Const (CI32 0))
                                                      ,(I32, Const (CI32 2))])
           (Just dimArrayAddr)

    dimArray <- freshLocal
    emit $ NonTerm (ILoad dimArrayAddr (Ptr I32)) (Just dimArray)
    dimAddr  <- freshLocal
    emit $ NonTerm (GetElementPtr (Ptr I32) (Reg dimArray)
                                    [(I32, Const (CI32 indexedDims))])
           (Just dimAddr)

    len <- freshLocal
    emit $ NonTerm (ILoad dimAddr  I32) (Just len)
    return (Reg len)

  ENew _ exprDims ->
    if null exprDims then
      case t of
        (Pointer (Ident name)) -> 
         do debugger "Allocate memory for the structure in the heap"
            pointerE       <- freshLocal
            sizeE          <- freshLocal
            emit $ NonTerm (GetElementPtr (Ptr (Def name)) (Const Null) [(I32, Const (CI32 1))])
                 (Just pointerE)
            emit $ NonTerm (PtrToInt (Ptr (Def name)) pointerE I32) (Just sizeE)

            voida         <- freshLocal
            newStr        <- freshLocal
            emit $ NonTerm (ICall (Ptr I8) "@calloc" [(I32, Const (CI32 1)),(I32, Reg sizeE)])
                                                   (Just voida)
            emit $ NonTerm (BitCast (Ptr I8) voida (Ptr (Def name))) (Just newStr)
            return (Reg newStr)
        (Object (Ident name) _) ->
         do debugger "Allocate memory for the structure (object) in the heap"
            pointerE       <- freshLocal
            sizeE          <- freshLocal
            emit $ NonTerm (GetElementPtr (Ptr (Def name)) (Const Null) [(I32, Const (CI32 1))])
                 (Just pointerE)
            emit $ NonTerm (PtrToInt (Ptr (Def name)) pointerE I32) (Just sizeE)

            voida         <- freshLocal
            newStr        <- freshLocal
            emit $ NonTerm (ICall (Ptr I8) "@calloc" [(I32, Const (CI32 1)),(I32, Reg sizeE)])
                                                   (Just voida)
            emit $ NonTerm (BitCast (Ptr I8) voida (Ptr (Def name))) (Just newStr)
            classDescriptorAddr <- freshLocal
            emit $ NonTerm (GetElementPtr (Ptr (Def name)) (Reg newStr) [(I32, Const (CI32 0)), (I32, Const (CI32 0))]) (Just classDescriptorAddr)
            emit $ NonTerm (IStore classDescriptorAddr (Global ("ClassDescriptor." ++ name)) (Ptr (Def "ClassDescriptor"))) Nothing
            return (Reg newStr)
    else do
      str <- freshLocal
      emit $ NonTerm (IAlloc type') (Just str)

      debugger "Calculation of total length and partial dimensions"
      initialLength <- freshLocal
      emit $ NonTerm (IAdd (Const (CI32 0)) (Const (CI32 1)) I32) (Just initialLength)
      (length,operands) <- foldM
                            (\(len,reg) expr -> do
                               dimension <- genCodeExpr expr
                               newLen    <- freshLocal
                               emit $ NonTerm (IMul (Reg len) dimension I32) (Just newLen)
                               return (newLen,reg ++ [dimension]))
                                                (initialLength,[])
                                                (map (\(DimAddr e) -> e) exprDims)

      debugger "Saving the length in the structure"
      lenAddr <- freshLocal
      emit $ NonTerm (GetElementPtr (Ptr type') (Reg str) [(I32, Const (CI32 0))
                                                       ,(I32, Const (CI32 0))])
             (Just lenAddr)
      emit $ NonTerm (IStore lenAddr (Reg length) I32) Nothing

      debugger "Saving the number of dimensions"
      numDimAddr <- freshLocal
      emit $ NonTerm (GetElementPtr (Ptr type') (Reg str) [(I32, Const (CI32 0))
                                                       ,(I32, Const (CI32 1))])
             (Just numDimAddr)
      emit $ NonTerm (IStore numDimAddr (Const (CI32 nDim)) I32) Nothing

      debugger "Allocation of array for holding partial dimensions"
      pointerI32       <- freshLocal
      sizeI32          <- freshLocal
      emit $ NonTerm (GetElementPtr (Ptr I32) (Const Null) [(I32, Const (CI32 1))])
             (Just pointerI32)
      emit $ NonTerm (PtrToInt (Ptr I32) pointerI32 I32) (Just sizeI32)

      voidi32        <- freshLocal
      dimArray       <- freshLocal
      emit $ NonTerm (ICall (Ptr I8) "@calloc" [(I32, (Const (CI32 nDim))),(I32, Reg sizeI32)])
                              (Just voidi32)
      emit $ NonTerm (BitCast (Ptr I8) voidi32 (Ptr I32)) (Just dimArray)

      debugger "Save the dimension array in the structure"
      dimArrayAddr <- freshLocal
      emit $ NonTerm (GetElementPtr (Ptr type') (Reg str) [(I32, Const (CI32 0))
                                                      ,(I32, Const (CI32 2))])
             (Just dimArrayAddr)
      emit $ NonTerm (IStore dimArrayAddr (Reg dimArray) (Ptr I32)) Nothing

      debugger "Initialization of dimension array"
      foldM (\index dimExpr ->
               do
                 elemAddr          <- freshLocal
                 emit $ NonTerm (GetElementPtr (Ptr I32) (Reg dimArray)
                                                 [(I32, Const (CI32 index))])
                        (Just elemAddr)
                 emit $ NonTerm (IStore elemAddr dimExpr I32) Nothing
                 return (index + 1)) 0 operands

      debugger "Allocate memory for the array of elements"
      pointerE       <- freshLocal
      sizeE          <- freshLocal
      emit $ NonTerm (GetElementPtr (Ptr ty) (Const Null) [(I32, Const (CI32 1))])
             (Just pointerE)
      emit $ NonTerm (PtrToInt (Ptr ty) pointerE I32) (Just sizeE)

      voida         <- freshLocal
      elemArray     <- freshLocal
      emit $ NonTerm (ICall (Ptr I8) "@calloc" [(I32, (Reg length)),(I32, Reg sizeE)]) (Just voida)
      emit $ NonTerm (BitCast (Ptr I8) voida (Ptr ty)) (Just elemArray)

      debugger  "Store the array of elements"
      elemArrayAddr <- freshLocal
      emit $ NonTerm (GetElementPtr (Ptr type') (Reg str) [(I32, Const (CI32 0))
                                                       ,(I32, Const (CI32 3))])
             (Just elemArrayAddr)
      emit $ NonTerm (IStore elemArrayAddr (Reg elemArray) (Ptr ty)) Nothing

      ret_str <- freshLocal
      emit $ NonTerm (ILoad str type') (Just ret_str)

      return (Reg ret_str)
      where
        type'@(ArrayT ty nDim) = toPrimTy t

  PtrDeRef var field ->
    do fieldAddr <- genCodeLVal (LValStr var field)
       field     <- freshLocal
       emit $ NonTerm (ILoad fieldAddr (toPrimTy t)) (Just field)
       return (Reg field)
              
  NullC  -> return (Const Null)

  ELitInt n        -> return $ Const (CI32 n)
  ELitDoub d       -> return $ Const (CD d)
  ELitTrue         -> return $ Const (CI1 True)
  ELitFalse        -> return $ Const (CI1 False)
  EApp (Ident id) exprs    ->
    do let ret_type  = toPrimTy t
           args_type = map getTypeExpr exprs
       args          <- fmap (zip args_type) $ mapM genCodeExpr exprs
       case ret_type of
         V ->
           do emit $ NonTerm (ICall ret_type ("@" ++ id) args) Nothing
              return Emp
         _   ->
           do rr <- freshLocal
              emit $ NonTerm (ICall ret_type ("@" ++ id) args) (Just rr)
              return (Reg rr)
  MApp (Ident id) obj exprs  ->
    do let retTy  = toPrimTy t
           objTy  = getTypeExpr obj
           argsTy = map getTypeExpr exprs
                       
       Reg evObj     <- genCodeExpr obj
       evArgs        <- mapM genCodeExpr exprs

       debugger "Get class descriptor from object"

       classDescrAddr    <- freshLocal
       emit $ NonTerm (GetElementPtr objTy (Reg evObj) [(I32, Const (CI32 0))
                                                       ,(I32, Const (CI32 0))])
                                                       
              (Just classDescrAddr)

       classDescr    <- freshLocal
       emit $ NonTerm (ILoad classDescrAddr (Ptr (Def "ClassDescriptor")))
              (Just classDescr)

       debugger "Get method from dispatcher"
                
       methodPtr     <- freshLocal
       emit $ NonTerm (ICall (Ptr I8) "@dispatcher" [(I64
                                                    , Const (CI32 .
                                                             fromIntegral .
                                                             hash $  id))
                                                   ,(Ptr $ Def "ClassDescriptor"
                                                    , Reg classDescr)])
              (Just methodPtr)
            
       debugger "Cast method to its actual type"

       castedMethod  <- freshLocal
       emit $ NonTerm (BitCast (Ptr I8) methodPtr (F retTy (Ptr I8 : argsTy)))
              (Just castedMethod)
                
       debugger "Cast object to i8*"
                
       castedAddr <- freshLocal
       emit $ NonTerm (BitCast objTy evObj (Ptr I8))
              (Just castedAddr)

       let args = (Ptr I8,Reg castedAddr) : zip argsTy evArgs
           fun  = show castedMethod
                  
       case retTy of
         V ->
           do emit $ NonTerm (ICall retTy  fun args) Nothing
              return Emp
         _   ->
           do rr <- freshLocal
              emit $ NonTerm (ICall retTy fun args) (Just rr)
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


findArrIndex :: Ty -> Register -> [DimA] -> GenCode Register
findArrIndex ty@(ArrayT ty' nDim) addr index = do
    debugger "findArrIndex"
    debugger "Generate register for indexing expressions"
    indexes  <- mapM (genCodeExpr . (\(DimAddr e) -> e)) index

    debugger "Load array of dimensions"
    dimArrayAddr <- freshLocal
    emit $ NonTerm (GetElementPtr (Ptr ty) (Reg addr) [(I32, Const (CI32 0))
                                                      ,(I32, Const (CI32 2))])
           (Just dimArrayAddr)

    dimArray     <- freshLocal
    emit $ NonTerm (ILoad dimArrayAddr (Ptr I32)) (Just dimArray)

    debugger "Calculate the total position of an element in the array"
    elemIndex <- fmap fst $
      foldM
      (\(accum,dim) indx -> do
         partialSum  <-
           foldM (\partial idx ->
                    do
                      indexAddr <- freshLocal
                      emit $ NonTerm (GetElementPtr (Ptr I32) (Reg dimArray)
                                                      [(I32, idx)])
                             (Just indexAddr)
                      dimension <- freshLocal
                      emit $ NonTerm (ILoad indexAddr I32) (Just dimension)
                      newPartial <- freshLocal
                      emit $ NonTerm (IMul partial (Reg dimension) I32) (Just newPartial)
                      return (Reg newPartial)
                 ) (Const (CI32 1)) (map (Const . CI32) [dim .. nDim-1])
         newTmp   <- freshLocal
         emit $ NonTerm (IMul indx partialSum I32) (Just newTmp)
         newAccum <- freshLocal
         emit $ NonTerm (IAdd accum (Reg newTmp) I32) (Just newAccum)
         return (Reg newAccum,dim+1)) (Const (CI32 0),1) indexes

    debugger "Get the array of elements"
    elemArrayAddr <- freshLocal
    emit $ NonTerm (GetElementPtr (Ptr ty) (Reg addr) [(I32, Const (CI32 0))
                                                      ,(I32, Const (CI32 3))])
           (Just elemArrayAddr)
    elemArray     <- freshLocal
    emit $ NonTerm (ILoad elemArrayAddr (Ptr ty')) (Just elemArray)

    debugger "Get the address of the element"
    elemAddr      <- freshLocal
    emit $ NonTerm (GetElementPtr (Ptr ty') (Reg elemArray) [(I32, elemIndex)])
           (Just elemAddr)
    return elemAddr

getTypeExpr :: Expr -> Ty
getTypeExpr (ETyped _ t) = toPrimTy t
