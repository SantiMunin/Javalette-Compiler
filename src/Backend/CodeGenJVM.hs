{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections #-}
module Backend.CodeGenJVM (genCode) where

import Javalette.Abs
import Javalette.ErrM
    
import Control.Monad.State as CMS
import Control.Monad.Identity
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe

type Address = Int
type Label   = Int

-- | Contains an intermediate code and 
-- holds data useful to address variables.
data Env = E {
      addresses   :: [Map Ident (Address,Type)],
      nextLabel   :: Label,
      nextAddress :: Address,
      maxAddress  :: Address,
      stackSize   :: Int,
      maxSize     :: Int,
      code        :: [Instruction]
    } deriving (Show)

-- | Creates a new environment.
initEnv :: Env
initEnv = E {
      addresses   = [M.empty],
      nextLabel   = 0,
      nextAddress = 1,
      maxAddress  = 0,
      stackSize   = 0,
      maxSize     = 0,
      code        = []
    }

-- | When entering a new function, the addresses need to be reset.
resetAddresses :: Env -> Env
resetAddresses env = env { addresses = [M.empty], nextAddress = 0 }

-- | Creates a new, unique label identifier.
newLabel :: GenCode Label
newLabel = do
  env <- CMS.get
  let label = nextLabel env
  CMS.modify (\env -> env { nextLabel = 1 + nextLabel env })
  return label

-- | Creates a label given an identifier.
createLabel :: Int -> String
createLabel n = "label_" ++ show n

-- | Creates a new block (scope) of variables.
newBlock :: GenCode ()
newBlock = CMS.modify 
  (\env -> env { addresses =  M.empty : addresses env })

-- | Removes a block of variables.
remBlock :: GenCode ()
remBlock = CMS.modify (\env -> env { addresses = tail $ addresses env })

-- | Creates a new var giving it an address.
newVar :: Bool -> Type -> Ident -> GenCode Address
newVar init t id  = do
  env <- CMS.get
  let addr = nextAddress env
      incr = case t of
               Doub -> 2
               _           -> 1
  CMS.modify (\env -> 
    env { nextAddress = addr + incr, 
          addresses = let (x:xs) = addresses env
                      in M.insert id (addr,t) x : xs})
  when init $ case t of
    Doub -> do
           emit DCONST_0
           emit $ DSTORE addr
    Int  -> do
           emit ICONST_0
           emit $ ISTORE addr
    Bool -> do
           emit ICONST_0
           emit $ ISTORE addr
    _    -> return ()
  return addr

-- | Looks the address of a given variable.
lookId :: Ident -> GenCode (Address,Type)
lookId id =
  gets $ lookFor id . addresses
    where
      lookFor id [] = error $ "GenCoder error: variable " ++ show id ++ " not found"
      lookFor id (x:xs) = 
        case M.lookup id x of
          Nothing -> lookFor id xs
          Just v -> v

-- | Intermediate representation of Jasmin instructions.
data Instruction
    = LDC Integer
    | LDC_2W Double
    | ILOAD  Address
    | DLOAD  Address
    | ISTORE Address
    | DSTORE Address
    | DADD
    | IADD
    | DMUL
    | IMUL
    | DDIV
    | IDIV
    | DSUB
    | ISUB
    | INEG
    | IREM
    | DNEG
    | GOTO Label
    | DUP
    | DUP2
    | POP
    | POP2
    | ICONST_0
    | ICONST_1
    | DCONST_0
    | DCONST_1
    | IF_ICMP Label
    | IF_IEQ Label
    | IF_INE Label
    | IF_ILT Label
    | IF_IGE Label
    | IF_IGT Label
    | IF_ILE Label
    | IF_EQ Label
    | DCMPL
    | IOR
    | IAND
    | RETURN
    | IRETURN
    | DRETURN
      
    -- Array
    | NEWARRAY Type
    | ARRAYLEN
    | ALOAD Address
    | ASTORE Address
    | IALOAD 
    | IASTORE
    | DALOAD 
    | DASTORE
    | ARETURN
      
    -- Special 
    | PUTLABEL Label
    | INVOKE Ident [Type] Type
    | DEF Ident [Type] Type
    | LOCALS Int
    | STACK Int
    | LNEG
    | END
    | NOP
    | LIT String

instance Show Instruction
    where
      show = toString ""
             
-- | Translates a Intruction to a Jasmin's one.
toString :: String -> Instruction -> String
toString name instr = 
        case instr of
          LDC x    -> "ldc "   ++ show x
          LDC_2W x -> "ldc2_w "  ++ show x
          ILOAD  x -> "iload " ++ show x
          DLOAD  x -> "dload " ++ show x
          ISTORE x -> "istore " ++ show x
          DSTORE x -> "dstore " ++ show x
          DADD     -> "dadd"      
          IADD     -> "iadd"           
          DMUL     -> "dmul"      
          IMUL     -> "imul"      
          DDIV     -> "ddiv"
          IDIV     -> "idiv"
          DSUB     -> "dsub"
          ISUB     -> "isub"
          INEG     -> "ineg"
          DNEG     -> "dneg"
          IREM     -> "irem"
          GOTO l   -> "goto " ++ createLabel l
          DUP      -> "dup"
          DUP2     -> "dup2"
          POP      -> "pop"
          POP2     -> "pop2"
          ICONST_0 -> "iconst_0"
          ICONST_1 -> "iconst_1"
          DCONST_0 -> "dconst_0"
          DCONST_1 -> "dconst_1"
          IF_ICMP l -> "if_icmp " ++ createLabel l
          IF_IEQ  l -> "if_icmpeq " ++ createLabel l
          IF_INE  l -> "if_icmpne " ++ createLabel l
          IF_ILT  l -> "if_icmplt " ++ createLabel l
          IF_IGE  l -> "if_icmpge " ++ createLabel l
          IF_IGT  l -> "if_icmpgt " ++ createLabel l
          IF_ILE  l -> "if_icmple " ++ createLabel l
          IF_EQ   l -> "ifeq " ++ createLabel l
          DCMPL     -> "dcmpl"
          IOR       -> "ior"
          IAND      -> "iand"
          RETURN    -> "return"
          IRETURN   -> "ireturn"
          DRETURN   -> "dreturn"
          
          -- Array
          ALOAD x    -> "aload " ++ show x
          ASTORE x   -> "astore " ++ show x
          NEWARRAY t -> "newarray " ++ toT t
              where
                toT Int  = "int"
                toT Doub = "double"
                toT Bool = "int"

          ARRAYLEN   -> "arraylength"
          IALOAD  -> "iaload"
          IASTORE -> "iastore"
          DALOAD  -> "daload"
          DASTORE -> "dastore"
          ARETURN -> "areturn"
                     
          -- Special 
          PUTLABEL l -> createLabel l ++ ":"
          INVOKE (Ident id) types t ->
              let n' = if id `elem` [ "printInt"
                                    , "printDouble"
                                    , "readInt"
                                    , "readDouble"
                                    , "printString" ]
                       then "Runtime" else name
              in "invokestatic "++ n' ++ "/" ++
                               bodyFun id types t
          DEF (Ident id) types t -> ".method public static "
                                      ++ bodyFun id types t 
          LOCALS x -> ".limit locals " ++ show x
          STACK x  -> ".limit stack " ++ show x
          END      -> ".end method"
          LNEG     -> "iconst_1\nisub"
          NOP      -> "nop"
          -- Literal
          LIT s -> s

-- | Creates a Jasmin's function representation.
bodyFun :: String -> [Type] -> Type -> String
bodyFun id types t = concat [
                      id
                     , "("
                     , concatMap toT types
                     ,")"
                     , toT t ]
    where
      toT Doub   = "D"
      toT Int    = "I"
      toT Bool   = "Z"
      toT Void   = "V"
      toT String = "Ljava/lang/String;"
      toT (Array t) = "[" ++ toT t
                    
-- | Emits an instruction.
emit :: Instruction -> GenCode ()
emit instr = CMS.modify (\env -> env { code = instr : code env })

-- | The genCode monad. It holds a state where we put variable 
-- addresses and the code generated so far.
newtype GenCode a = GenCode { runGC :: StateT Env Err a }
    deriving (Monad,MonadState Env)

-- | GenCodes a program.
genCode :: String -> Program -> Err String
genCode name (Prog defs) =
    case execStateT (runGC $ mapM_ genCodeDef defs) initEnv of
      Bad err -> fail err
      Ok s -> return $ unlines [ ".class public " ++ classname
                               , ".super java/lang/Object\n"
                               , ".method public <init>()V"
                               , "aload_0"
                               , "invokenonvirtual java/lang/Object/<init>()V"
                               , "return"
                               , ".end method"
                               ,".method public static main([Ljava/lang/String;)V"
                               , ".limit stack 100"
                               , "invokestatic " ++ classname ++ "/mainr()I"
                               , "return"
                               , ".end method"
                               ] ++
              (unlines . map (toString classname) . reverse) (code s)
                  where
                    classname = (reverse . takeWhile (/='/') . reverse) name
        
-- | GenCodes a function definition.
genCodeDef :: TopDef -> GenCode ()
genCodeDef (FnDef t (Ident id) args block) = do
    CMS.modify resetAddresses 
    let args' = map (\(Argument t id) -> (t,id)) args
    if id == "main" then
       emit $ DEF (Ident "mainr") (map fst args') t
    else
      emit $ DEF  (Ident id) (map fst args') t
    emit $ LOCALS 100
    emit $ STACK  1000
    addr <- mapM (uncurry $ newVar False) args'
    genCodeBlock block
    when (t == Void) (emit RETURN)
    emit END

-- | GenCode a block
genCodeBlock :: Block -> GenCode ()
genCodeBlock block = case block of
  SBlock stmts  -> mapM_ genCodeStm stmts

-- | GenCode a Item
genCodeItem :: Type -> Item -> GenCode ()
genCodeItem t item = case item of
  NoInit id    -> newVar True t id >> return ()
  Init id expr -> do
    genCodeExpr expr
    addr <- newVar False t id                
    emit $ case t of
      Doub    -> DSTORE addr
      Int     -> ISTORE addr
      Bool    -> ISTORE addr
      Array _ -> ASTORE addr

-- | GenCodes a statement.
genCodeStm :: Stmt -> GenCode ()
genCodeStm stm = case stm of
  Empty        -> return ()
  BStmt block  -> do
    newBlock
    genCodeBlock block
    remBlock

  Decl type' items  -> mapM_ (genCodeItem type') items
                       
  Ass var expr  -> do
    case var of
      VarArr id indx -> do
                     (addr,Array t) <- lookId id
                     emit $ ALOAD addr
                     genCodeExpr indx
                     genCodeExpr expr
                     case t of
                       Doub -> emit DASTORE
                       _    -> emit IASTORE
                               
      VarI  id      -> do
                     (addr,t) <- lookId id
                     genCodeExpr expr
                     case t of
                       Doub -> emit $ DSTORE addr
                       _    -> emit $ ISTORE addr

  Incr id  -> do
        (addr,t) <- lookId id
        case t of
          Int -> do
                 emit (ILOAD addr)
                 emit ICONST_1
                 emit IADD
                 emit (ISTORE addr)
          Doub -> do
                 emit (DLOAD addr)
                 emit DCONST_1
                 emit DADD
                 emit (DSTORE addr)
          
          
  Decr id  -> do
        (addr,t) <- lookId id
        case t of
          Int -> do
                 emit $ ILOAD addr
                 emit ICONST_1
                 emit ISUB
                 emit $ ISTORE addr
          Doub -> do
                 emit $ DLOAD addr
                 emit DCONST_1
                 emit DSUB
                 emit $ DSTORE addr
          
  Ret e@(ETyped _ t)  ->
      do
        genCodeExpr e
        case t of
          Doub -> emit DRETURN
          Void -> emit RETURN
          Int  -> emit IRETURN
          Bool -> emit IRETURN
          Array _ -> emit ARETURN
                     
  VRet  -> emit RETURN
           
  Cond exp@(ETyped expr _) stmt  ->
      case expr of
        ELitTrue  -> genCodeStm stmt     
        ELitFalse -> return ()
        _ -> do
          false <- newLabel 
          genCodeExpr exp
          emit $ IF_EQ false
          genCodeStm stmt
          emit $ PUTLABEL false
          emit NOP
                     
  CondElse exp@(ETyped expr _) stmt1 stmt2  ->
      case expr of
        ELitTrue  -> genCodeStm stmt1
        ELitFalse -> genCodeStm stmt2
        _ -> do
          false <- newLabel 
          end   <- newLabel
          genCodeExpr exp
          emit $ IF_EQ false
          genCodeStm stmt1
          emit $ GOTO end
          emit $ PUTLABEL false
          genCodeStm stmt2
          emit $ PUTLABEL end
          emit NOP
 

  While expr stmt  -> 
      do
        test <- newLabel
        end  <- newLabel
        emit $ PUTLABEL test
        genCodeExpr expr
        emit $ IF_EQ end
        genCodeStm stmt
        emit $ GOTO test
        emit $ PUTLABEL end
        emit NOP
                 
  SExp e@(ETyped exp t) ->
      do
        genCodeExpr e
        case t of
          Doub   -> emit POP2
          Int    -> emit POP
          Bool   -> emit POP 
          _           -> return ()
                         
  -- For (t var : arrayref) stmt
  For (ForDecl t id) (ETyped (EVar arr) _) stmt ->
      do
        indx <- newVar True Int (Ident "indx")
        var  <- newVar True t   id
        len  <- newVar False Int (Ident "len")
        (arrAddr,_) <- lookId arr
        for  <- newLabel
        end  <- newLabel
        emit $ ALOAD arrAddr
        emit $ ARRAYLEN
        emit $ ISTORE len
             
        emit $ PUTLABEL for
        emit $ ILOAD len
        emit $ ILOAD indx
        emit ISUB
        emit $ IF_EQ end
        emit $ ALOAD arrAddr
        emit $ ILOAD indx
        case t of
          Doub -> do
                 emit DALOAD
                 emit $ DSTORE var
          _    ->do
                 emit IALOAD
                 emit $ ISTORE var
        genCodeStm stmt
        emit $ ILOAD indx
        emit ICONST_1
        emit IADD
        emit $ ISTORE indx
        emit $ GOTO for
        emit $ PUTLABEL end
        emit NOP
        
-- | GenCodes an expression.
genCodeExpr :: Expr -> GenCode ()
genCodeExpr (ETyped expr t) = do
  case expr of
      EVar id     -> do
             (addr,_) <- lookId id
             case t of
               Int     -> emit $ ILOAD addr
               Doub    -> emit $ DLOAD addr
               Bool    -> emit $ ILOAD addr
               Array t' -> emit $ ALOAD addr

      ELitInt n   -> emit (LDC n)
      ELitDoub d  -> emit (LDC_2W d)
      ELitTrue    -> emit (ICONST_1)
      ELitFalse   -> emit (ICONST_0)
      EApp id exprs  -> do
              mapM_ genCodeExpr exprs
              let fArgs = map (\(ETyped _ t) -> t) exprs
              emit (INVOKE id fArgs t)

      EString str  -> emit (LIT $ "ldc " ++ "\"" ++ str ++ "\"")
      Neg expr     -> do
              genCodeExpr expr
              case t of
                Int  -> emit INEG
                Doub -> emit DNEG
                
      Not expr  -> do
              end <- newLabel
              emit ICONST_1
              genCodeExpr expr
              emit $ IF_EQ end
              emit POP
              emit ICONST_0
              emit $ PUTLABEL end
              emit NOP
              
      EMul expr1 mulop expr2  -> genCodeArithMul t mulop expr1 expr2
      EAdd expr1 addop expr2  -> genCodeArithAdd t addop expr1 expr2
      ERel expr1@(ETyped _ t') relop expr2  ->
          case t' of
            Doub -> case relop of
                      LTH  -> do
                        end <- newLabel
                        true <- newLabel
                        genCodeExpr expr2
                        genCodeExpr expr1
                        emit DCMPL
                        emit ICONST_1
                        emit $ IF_IEQ true
                        emit $ ICONST_0
                        emit $ GOTO end
                        emit $ PUTLABEL true
                        emit $ ICONST_1
                        emit $ PUTLABEL end
                      LE   -> genCodeExpr (ETyped
                                            (EOr (ETyped (ERel expr1 EQU expr2) Bool)
                                                 (ETyped (ERel expr1 LTH expr2) Bool)) Bool)
                      GTH  -> genCodeExpr (ETyped
                                            (ETyped (Not
                                                    (ETyped (ERel expr1 LE expr2) Bool)) Bool) Bool)
                                                 
                      GE   -> genCodeExpr (ETyped
                                            (ETyped (Not
                                                    (ETyped (ERel expr1 LTH expr2) Bool)) Bool) Bool)
                                                 
                      EQU  -> do
                            eq0_l <- newLabel
                            eq1_l <- newLabel
                            genCodeExpr expr1
                            genCodeExpr expr2
                            emit DCMPL
                            emit $ IF_EQ eq0_l
                            emit ICONST_0
                            emit $ GOTO eq1_l
                            emit $ PUTLABEL eq0_l
                            emit ICONST_1
                            emit $ PUTLABEL eq1_l
                            emit NOP
                                 
                      NE   -> genCodeExpr (ETyped (ETyped
                                                   (Not (ETyped
                                                         (ERel expr1 EQU expr2) Bool)) Bool) Bool)
                          

            _ -> genCodeRelInt instr expr1 expr2
                where
                  instr = case relop of
                            LTH  -> IF_ILT
                            LE   -> IF_ILE
                            GTH  -> IF_IGT
                            GE   -> IF_IGE
                            EQU  -> IF_IEQ
                            NE   -> IF_INE

      EAnd expr1 expr2  -> do
          end   <- newLabel
          emit ICONST_0 
          genCodeExpr expr1
          emit $ IF_EQ end
          emit POP
          genCodeExpr expr2
          emit $ PUTLABEL end
          emit NOP
               
      EOr expr1 expr2        -> do
          end <- newLabel
          emit ICONST_1
          genCodeExpr expr1
          emit LNEG
          emit $ IF_EQ end
          emit POP
          genCodeExpr expr2
          emit $ PUTLABEL end
          emit NOP
               
      e@(ETyped exp type')     -> genCodeExpr e

      EVarArr id expr -> do
              (addr,Array t') <- lookId id
              emit $ ALOAD addr
              genCodeExpr expr
              emit $ case t' of
                       Doub -> DALOAD
                       _    -> IALOAD
      EArrL id     -> do
              (addr,_) <- lookId id
              emit $ ALOAD addr
              emit ARRAYLEN
      EArrI t' expr -> do
              genCodeExpr expr
              emit $ NEWARRAY t'
          
      err -> fail $ "Not implemented: " ++ show err

-- | GenCodes an arithmetic operation Mul.
genCodeArithMul :: Type -> MulOp -> Expr -> Expr -> GenCode ()
genCodeArithMul t op exp1 exp2 =
    do
      genCodeExpr exp1
      genCodeExpr exp2
      emit $ case t of
               Int    -> case op of
                                Times -> IMUL
                                Div   -> IDIV
                                Mod   -> IREM
               Doub -> case op of
                                Times -> DMUL
                                Div   -> DDIV
                                Mod   -> error "Mod not implemented for double"

-- | GenCode an arithmetic operation Add.
genCodeArithAdd :: Type -> AddOp -> Expr -> Expr -> GenCode ()
genCodeArithAdd t op exp1 exp2 =
    do
      genCodeExpr exp1
      genCodeExpr exp2
      emit $ case t of
               Int    -> case op of
                                Plus  -> IADD
                                Minus -> ISUB
               Doub -> case op of
                                Plus  -> DADD
                                Minus -> DSUB


-- | GenCodes a integer comparison.
genCodeRelInt :: (Label -> Instruction) -> Expr -> Expr -> GenCode ()
genCodeRelInt instr exp1 exp2 =
    do
      true_l <- newLabel
      emit ICONST_1
      genCodeExpr exp1
      genCodeExpr exp2
      emit (instr true_l)
      emit POP   
      emit ICONST_0
      emit $ PUTLABEL true_l
      emit NOP
           

