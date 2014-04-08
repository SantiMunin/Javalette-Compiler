{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Implements a type checker for the Javalette language.
module Frontend.TypeChecker where

import           Javalette.Abs
import           Javalette.ErrM
import           Internal.Types
  
import           Data.Map            (Map)
import qualified Data.Map            as M
import qualified Data.Set            as S

import           Control.Monad       (forM, unless, zipWithM_)
import           Control.Monad.State as CMS


-- | An environment is a pair containing information about functions
-- and variables defined. It supports different scopes.
data Env = Env { functions :: FunctionHeaders
               , structs   :: Map Ident Type
               , pointers  :: Map Ident Ident
               , context   :: [Context]
               , sugarVar  :: Int }

-- | Relation between pointers an the pointed structure.
type Pointers = Map Ident Ident

-- | The functions information is a relation name ->
-- list of types (arguments) and the return type.
type FunctionHeaders = Map Ident ([Type], Type)

-- | A context is a relation identifier -> (type, number of dimensions)
-- (variables).
type Context = Map Ident Type

-- | This monad holds a state and allows to stop the execution
-- returning an error.
newtype TypeCheck a = TypeCheck { runType :: StateT Env Err a }
    deriving (Monad,MonadState Env)

-- | Looks for a variable in the environment.
lookupVar :: Ident -> TypeCheck Type
lookupVar id = do
  cntx <- CMS.gets context
  look cntx
    where
      look [] = fail $ "Variable " ++ show id ++ " not declared."
      look (top:rest) = case M.lookup id top of
                           Nothing -> look rest
                           Just t  -> return t

-- | Looks for a function in the environment.
lookupFun :: Ident -> TypeCheck ([Type],Type)
lookupFun id = do
  functions <- CMS.gets functions
  case M.lookup id functions of
    Nothing -> fail $ "Function " ++ show id ++ " not declared."
    Just t  -> return t

-- | Adds a variable type to the context if it does not exists.
createVarIfNotExists :: Ident -> Type -> TypeCheck ()
createVarIfNotExists id t = do
  top:rest <- CMS.gets context
  case M.lookup id top of
    Nothing   -> do
      t' <- converseType t
      CMS.modify (\env -> env { context = M.insert id t' top : rest })
    Just _    -> fail $ concat [ "Variable "
                              , show id
                              , " already defined." ]

-- | Deletes a variable.
deleteVar :: Ident -> TypeCheck ()
deleteVar id = do
  top:rest <- CMS.gets context
  CMS.modify (\env -> env { context =  M.delete id top: rest })

-- | Updates the function signature in the environment
-- unless it was previously defined (in that case throws an error).
createFunIfNotExists :: Ident -> ([Type],Type) -> TypeCheck ()
createFunIfNotExists id (argTypes, retType) = do
  fun <- CMS.gets (M.lookup id . functions)
  case fun of
    Just  _ -> fail $ "Function " ++ show id ++ " defined twice."
    Nothing -> do
      argChecked <- mapM converseType argTypes
      retChecked <- converseType retType
      CMS.modify (\env -> env { functions = M.insert id
                     (argChecked, retChecked) (functions env)})


-- | Converts type from parser give type to internal defined.
converseType :: Type -> TypeCheck Type
converseType t =
  case t of
    Array t' dims -> return $ DimT t' (fromIntegral $ length dims)
    Ref name -> do
           structName <- CMS.gets (M.lookup name . pointers)
           case structName of
             Nothing -> fail $ "Struct with name: " ++ show name ++ " not defined."
             Just strName  -> return (Pointer strName)
    _            -> return t

-- | Creates a new context for variables.
newBlock :: TypeCheck ()
newBlock = CMS.modify (\env -> env {context =  M.empty : context env})

-- | Removes a context of variables.
removeBlock :: TypeCheck ()
removeBlock  = CMS.modify (\env -> env { context = tail $ context env})

-- | Creates an empty environment.
emptyEnv :: Env
emptyEnv = Env { functions   = M.empty
               , structs     = M.empty
               , pointers    = M.empty
               , context     = []
               , sugarVar    = 0 }

newSugarVar :: TypeCheck Ident
newSugarVar = do
  var <- CMS.gets sugarVar
  CMS.modify (\env -> env {sugarVar = sugarVar env + 1})
  return (Ident $ '_' : show var)

-- | Initializes the environment, adding all the primitive functions.
initializeEnv ::[TopDef] -> TypeCheck ()
initializeEnv functions = do
  mapM_ addDef (initializeDefs ++ functions)
  where
    addDef (FnDef  t id args _)  = createFunIfNotExists id
                                   (map (\(Argument t _) -> t) args, t)
    initializeDefs =
      [ FnDef Void (Ident "printInt")    [Argument Int (Ident "x")]  (SBlock [])
      -- void   printInt(int x)
      , FnDef Void (Ident "printDouble") [Argument Doub (Ident "x")] (SBlock [])
      -- void  printDouble(double x)
      , FnDef Void (Ident "printString") [Argument String (Ident "x")] (SBlock [])
      -- void printString(String x)
      , FnDef Int  (Ident "readInt")     []                     (SBlock [])
      -- int readInt()
      , FnDef Doub (Ident "readDouble")  []                     (SBlock [])
      -- double readDouble()
      ]

-- | Typechecks a program.
typecheck :: Program -> Err (Structs, Program)
typecheck program = evalStateT (runType $ typeCheckProgram program) emptyEnv
  where
    typeCheckProgram :: Program -> TypeCheck (Structs, Program)
    typeCheckProgram (Prog defs) = do
      let (structDefs,pointerDef , funDefs) = splitDefinitions program
      typeCheckStructs pointerDef structDefs
      initializeEnv funDefs
      typedDefs <- mapM typeCheckFun funDefs
      structs   <- CMS.gets structs
      return (structs, Prog typedDefs)

    splitDefinitions (Prog defs) = (\(a,b,c) -> (reverse a,reverse b, reverse c))
                                   $ foldl select ([], [], []) defs
    select (stDefs, pDefs, funDefs) def@(FnDef _ _ _ _) = (stDefs, pDefs, def:funDefs)
    select (stDefs, pDefs, funDefs) def@(StructDef _ _) = (def:stDefs, pDefs, funDefs)
    select (stDefs, pDefs, funDefs) def@(PtrDef _ _)    = (stDefs, def:pDefs, funDefs)

-- | Checks all typedef and struct definitions and if everything is
--   correct then it put them in the environment.
typeCheckStructs :: [TopDef] -> [TopDef] -> TypeCheck ()
typeCheckStructs pointerDefs structDefs = do
  pointers <- foldM
              (\m (PtrDef (Ref strName) ptr@(Ident synom)) ->
                 if synom `elem` ["int", "double", "bool", "void"] then
                   fail $ "Pointer has the same name as a primitive type."
                 else
                   case M.lookup ptr m of
                     Nothing ->
                       if any (\(StructDef name _) -> name == strName) structDefs
                       then
                         return $ M.insert ptr strName m
                       else
                         fail $ concat [ "Pointer "
                                       , synom
                                       , " not refering to a struct."]
                     Just _  -> fail $ concat [ "Pointer "
                                              , synom
                                              , " already defined."]
              ) M.empty pointerDefs

  structs <- foldM
             (\m (StructDef name fields) ->
                case M.lookup name m of
                  Just _  -> fail $ concat ["Struct "
                                           , show name
                                           , "already defined."]
                  Nothing -> do
                    checkedFields <-
                      foldM
                      (\f (StrField t id) ->
                         case t of
                           Ref name ->
                             case M.lookup name pointers of
                               Nothing ->
                                 fail $ concat [ "Field "
                                               , show id
                                               , " is not a valid pointer"]
                               Just strName ->
                                 return $ f ++ [StrField (Pointer strName) id]
                           _ ->  return  $ f ++ [StrField t id]
                      ) [] fields
                    return $ M.insert name (Struct name checkedFields) m
             ) M.empty structDefs

  CMS.modify (\env -> env { structs  = structs
                          , pointers = pointers})

-- | Typechecks a function definition.
typeCheckFun :: TopDef -> TypeCheck TopDef
typeCheckFun (FnDef ret_t id args (SBlock stmts)) = do
  newBlock
  mapM_ (\(Argument t idArg)  -> createVarIfNotExists idArg t) args
  ret_t'      <- converseType ret_t
  checkedArgs <- mapM (\(Argument t idArg)
                         -> converseType t >>= \t' -> return (Argument t' idArg)) args

  (has_ret, BStmt typedStmts) <- typeCheckStmt ret_t' (BStmt (SBlock stmts))

  unless (has_ret || typeEq ret_t' Void) $
    fail $ "Missing return statement in function " ++ show id
  removeBlock
  return $ FnDef ret_t' id checkedArgs typedStmts


-- Casts a dimension addressing to an expression.
dimToExpr :: DimA -> Expr
dimToExpr (DimAddr e) = e

-- Casts a dimension addressing list to an
-- expression list.
dimsToExprs :: [DimA] -> [Expr]
dimsToExprs = map dimToExpr

-- | Casts an expressions list to a list of
-- dimension addressings.
exprsToDims :: [Expr] -> [DimA]
exprsToDims = map DimAddr

-- | Typechecks the validity of a given statement.
typeCheckStmt :: Type -> Stmt -> TypeCheck (Bool, Stmt)
typeCheckStmt funType stm =
    case stm of
      Empty -> return (False, Empty)
      BStmt (SBlock stmts) -> do
               newBlock
               results <- mapM (typeCheckStmt funType) stmts
               let (rets, typedStmts) = unzip results
               removeBlock
               return (or rets, BStmt (SBlock typedStmts))
      Decl t items -> do
               t' <- converseType t
               typedExprs <- mapM (checkItem t') items
               let typedItems = zipWith typeItem items typedExprs
               mapM_ (uncurry createVarIfNotExists) $
                     zip (map getIdent items) (repeat t')
               return (False, Decl t' typedItems)
          where
             checkItem t (NoInit id)   = return Nothing
             checkItem t (Init id exp) = do
                        typedExpr <- checkTypeExpr t exp
                        return $ Just typedExpr
             typeItem (NoInit id) Nothing = NoInit id
             typeItem (Init id _) (Just typedExpr) = Init id typedExpr
             getIdent (NoInit id)    = id
             getIdent (Init id _)    = id

      Ass lval exp ->
        -- Variable posibbly indexed
        case lval of
          LValVar ident ndims -> do
            typedAddrExpr   <- mapM (checkTypeExpr Int) $ dimsToExprs ndims
            t               <- lookupVar ident
            let dimT = case t of
                         DimT t' tDim -> DimT t' (tDim - fromIntegral (length ndims))
                         t'           -> t'
            typedExpr       <- checkTypeExpr dimT exp
            return (False, Ass (LValVar ident (exprsToDims typedAddrExpr)) typedExpr)

          -- Field of an object in the heap
          LValStr name field -> do
            t <- lookupVar name
            case t of
              Pointer strName ->
                do str <- CMS.gets (M.lookup strName . structs)
                   case str of
                     Nothing -> fail $ "Struct " ++ show strName ++ " not defined."
                     Just (Struct _ fields) ->
                       do case lookup field . map (\(StrField t id) -> (id,t))
                                 $ fields of
                            Nothing ->
                              fail "Trying to reference a field that doesn't exists"
                            Just t' ->
                              do typedExpr <- checkTypeExpr t' exp
                                 return (False, Ass lval typedExpr)

              _ -> error $ "Variable " ++ show name ++ " must be a pointer."

      Incr ident ->
          lookupVar ident >>= checkTypeNum  >>= (\typedExpr -> return (False, stm))
      Decr ident ->
          lookupVar ident >>= checkTypeNum  >>= (\typedExpr -> return (False, stm))
      Ret exp ->
          checkTypeExpr funType exp >>= (\typedExpr -> return (True, Ret typedExpr))
      VRet    -> if typeEq funType Void then return (True, VRet)
                 else fail "Not valid return type"
      Cond exp stm1 -> do
               typedExpr <- checkTypeExpr Bool exp
               newBlock
               (has_ret, typedStmt) <- typeCheckStmt funType stm1
               removeBlock
               case exp of
                 ELitTrue -> return (has_ret, Cond typedExpr typedStmt)
                 _        -> return (False, Cond typedExpr typedStmt)
      CondElse exp stm1 stm2 -> do
               typedExpr <- checkTypeExpr Bool exp
               newBlock
               (ret1, typedStmt1) <- typeCheckStmt funType stm1
               -- Cleans the current block.
               removeBlock
               newBlock
               (ret2, typedStmt2) <- typeCheckStmt funType stm2
               removeBlock
               return (ret1 || ret2, CondElse typedExpr typedStmt1 typedStmt2)
      While exp stm' -> do
               typedExpr <- checkTypeExpr Bool exp
               (has_ret, typedStmt) <- typeCheckStmt funType stm'
               return (has_ret, While typedExpr typedStmt)
      SExp exp -> inferTypeExpr exp >>=
                  (\typedExpr -> return (False, SExp typedExpr))
      For (ForDecl t id) exp@(Var v eDims) innerStm -> do
               (ETyped _ type'@(DimT t' nDims)) <- inferTypeExpr exp
               index  <- newSugarVar
               len    <- newSugarVar
               typeCheckStmt funType
                   (BStmt
                    (SBlock
                     [ Decl Int [Init index  (ELitInt 0)]
                     , Decl Int [Init len (Method v eDims (Ident "length"))]
                     , Decl (DimT t' (nDims -1)) [NoInit id]
                     , While (ERel
                              (Var index [])
                              LTH
                              (Var len []))
                               (BStmt
                                (SBlock
                                 [Ass (LValVar id [])
                                        (Var v (eDims
                                                ++ [DimAddr (Var index [])]))
                                 , Incr index
                                 , innerStm
                                 ]))
                     ]))
      For (ForDecl t id) _ innerStm -> fail "The expression should be a variable."


-- | Calculate type equality with dimensional check.
typeEq :: Type -> Type -> Bool
typeEq (DimT t1 dim1) (DimT t2 dim2) =  t1 == t2 && dim1 == dim2
typeEq (DimT t1 dim1) t2             =  t1 == t2 && dim1 == 0
typeEq t1             (DimT t2 dim2) =  t1 == t2 && dim2 == 0
typeEq t1             t2             =  t1 == t2

-- | Checks the type of an expresion in the given environment.
checkTypeExpr :: Type -> Expr -> TypeCheck Expr
checkTypeExpr t exp = do
  typedExpr@(ETyped _ expt') <- inferTypeExpr exp
  when (not $ typeEq t expt') $
       fail $ concat ["Expresion "
                     , show exp
                     , " has not type "
                     , show t
                     , ", instead has "
                     , show expt', "."]
  return typedExpr

-- | Infers the type of a expression in the given environment.
inferTypeExpr :: Expr -> TypeCheck Expr
inferTypeExpr exp =
  case exp of
      ELitTrue         -> return $ ETyped exp Bool
      ELitFalse        -> return $ ETyped exp Bool
      ELitInt n        -> return $ ETyped exp Int
      ELitDoub d       -> return $ ETyped exp Doub

      Var id eDims     -> do
        t <- lookupVar id
        typedEDims <- mapM (checkTypeExpr Int) (dimsToExprs eDims)
        let tExpr = case t of
                      DimT t' dims -> DimT t' (dims - fromIntegral (length eDims))
                      _            -> t
        return $ ETyped (Var id (exprsToDims typedEDims)) tExpr

      Method id eDims (Ident "length") -> do
        (DimT t ndims) <- lookupVar id
        when ((fromIntegral . length) eDims > ndims)
               $ fail "Indexing failure: Too many dimensions"
        typedEDims <- mapM (checkTypeExpr Int) (dimsToExprs eDims)
        return (ETyped (Method id (exprsToDims typedEDims) (Ident "length")) Int)

      ENew t eDims     ->
       -- New object in the heap.
       if null eDims then
         case t of
           Ref structName -> do
                  structs <- CMS.gets structs
                  case M.lookup structName structs of
                    Nothing  -> fail $ "Type not defined: " ++ show structName
                    Just _   -> return (ETyped exp (Pointer structName))
           _ -> fail $ "Cannot create an object of a primitive type: " ++ show t
       -- New array of type t
       else do
         let ndims = fromIntegral $ length eDims
         typedEDims <- mapM (checkTypeExpr Int) (dimsToExprs eDims)
         checkValidArrayType t
         return (ETyped (ENew t (exprsToDims typedEDims)) (DimT t ndims))

      PtrDeRef id1 id2  -> do
             Pointer structName <- lookupVar id1
             Just (Struct name fields) <- CMS.gets (M.lookup structName . structs)
             case lookup id2 . map (\(StrField t id) -> (id,t)) $ fields of
               Nothing -> fail "Trying to reference a field that doesn't exists."
               Just t' -> return $ ETyped exp t'

      ENull id  -> do
        pointers <- CMS.gets pointers
        structs  <- CMS.gets structs
        case M.lookup id pointers of
          Nothing        -> fail $ "Type not defined: " ++ show id
          Just structName  -> do
            case M.lookup structName structs of
              Nothing -> fail $ "Type does not exists"
              Just struct  -> return (ETyped NullC (Pointer structName))

      EString s        -> return $ ETyped exp String

      EApp id args     -> do
        (args_type, ret_type) <- lookupFun id
        typedArgs <- checkArgs id args_type args
        return $ ETyped (EApp id typedArgs) ret_type

      EMul exp1 op exp2  -> do
        typedE1@(ETyped _ t1)  <- inferTypeExpr exp1
        checkTypeNum t1
        typedE2 <- checkTypeExpr t1 exp2
        return $ ETyped (EMul typedE1 op typedE2) t1

      EAdd exp1 op exp2  -> do
        typedE1@(ETyped _ t1)  <- inferTypeExpr exp1
        checkTypeNum t1
        typedE2 <- checkTypeExpr t1 exp2
        return $ ETyped (EAdd typedE1 op typedE2)  t1

      ERel exp1 op exp2    -> do
        t <- inferTypeCMP exp1 exp2
        typedE1 <- inferTypeExpr exp1
        typedE2 <- inferTypeExpr exp2
        return $ ETyped (ERel typedE1 op typedE2) t

      EAnd exp1 exp2   -> do
        typedE1 <- checkTypeExpr Bool exp1
        typedE2 <- checkTypeExpr Bool exp2
        return $ ETyped (EAnd typedE1 typedE2) Bool

      EOr exp1 exp2    -> do
        typedE1 <- checkTypeExpr Bool exp1
        typedE2 <- checkTypeExpr Bool exp2
        return $ ETyped (EOr typedE1 typedE2) Bool

      Not exp          -> do
        typedExpr <- checkTypeExpr Bool exp
        return $ ETyped (Not typedExpr) Bool

      Neg exp          -> do
        typedExpr@(ETyped _ t) <- inferTypeExpr exp
        checkTypeNum t
        return $ ETyped (Neg typedExpr) t

-- | Checks if a type is suitable to be contained in an array.
checkValidArrayType :: Type -> TypeCheck ()
checkValidArrayType Void        = fail "Cannot create an array of voids."
checkValidArrayType (Array _ _) = fail "Cannot create an array of arrays."
checkValidArrayType _         = return ()


-- | Check the type of a numeric expression. If its neither Int or Double error.
checkTypeNum :: Type -> TypeCheck Type
checkTypeNum t@Int    = return t
checkTypeNum t@Doub   = return t
checkTypeNum t@(DimT Int 0)    = return t
checkTypeNum t@(DimT Doub 0)   = return t
checkTypeNum t                 = fail $ "Expected type Int or Double, actual type: " ++ show t

-- | Check that the arguments to a function call correspond on type and number as
-- | function signature.
checkArgs :: Ident -> [Type] -> [Expr] -> TypeCheck [Expr]
checkArgs _ [] []  = return []
checkArgs ide _  [] = fail $
  "Diferent number of arguments from declared in function " ++ show ide
checkArgs ide [] _  = fail $
  "Diferent number of arguments from declared in function " ++ show ide
checkArgs ide (e_t:xs) (c_t:ys) = do
  e_t'      <- converseType e_t
  typedExpr <- checkTypeExpr e_t  c_t
  otherTypedExpr <- checkArgs ide xs ys
  return $ typedExpr : otherTypedExpr

-- | Infer the type of a comparison operator.
inferTypeCMP :: Expr -> Expr -> TypeCheck Type
inferTypeCMP exp1 exp2 = do
    (ETyped _ t1) <- inferTypeExpr exp1
    checkVoid t1
    (ETyped _ t2) <- inferTypeExpr exp2
    checkVoid t2
    if typeEq t1 t2 then return Bool
    else
      fail $ "Cannot compare type " ++ show t1
                                   ++ " with type " ++ show t2
      where
        checkVoid t = when (typeEq t Void)$ fail "Void is not comparable."

