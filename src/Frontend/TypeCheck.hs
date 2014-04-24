{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Implements a type checker for the Javalette language.
module Frontend.TypeCheck (typecheck) where

import           Javalette.Abs
import           Javalette.ErrM
import           Internal.Types
  
import           Data.Map            (Map)
import qualified Data.Map            as M
import qualified Data.Set            as S

import           Control.Monad       (forM, unless, zipWithM_)
import           Control.Monad.State as CMS
import           Control.Monad.Reader as CMR


-- | An environment is a pair containing information about functions
-- and variables defined. It supports different scopes.
data ReadEnv  = REnv { functions :: FunHeader
                     , structs   :: Structs
                     }
              
data StateEnv = SEnv { context   :: [Context]
                     }
               
-- | A context is a relation identifier -> (type, number of dimensions)
-- (variables).
type Context = Map Ident Type

-- | This monad holds a state and allows to stop the execution
-- returning an error.
type TypeCheck a = ReaderT ReadEnv (StateT StateEnv Err) a

type FunHeader   = Map Ident ([Type], Type)

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

-- | Adds a variable type to the context if it does not exists.
createVarIfNotExists :: Ident -> Type -> TypeCheck ()
createVarIfNotExists id t = do
  top:rest <- CMS.gets context
  case M.lookup id top of
    Nothing   -> CMS.modify (\env -> env { context = M.insert id t top : rest })
    Just _    -> fail $ concat [ "Variable "
                              , show id
                              , " already defined." ]

-- | Deletes a variable.
deleteVar :: Ident -> TypeCheck ()
deleteVar id = do
  top:rest <- CMS.gets context
  CMS.modify (\env -> env { context =  M.delete id top: rest })

-- | Creates a new context for variables.
newBlock :: TypeCheck ()
newBlock = CMS.modify (\env -> env {context =  M.empty : context env})

-- | Removes a context of variables.
removeBlock :: TypeCheck ()
removeBlock  = CMS.modify (\env -> env { context = tail $ context env})

-- | Looks for a function in the environment.
lookupFun :: Ident -> TypeCheck ([Type],Type)
lookupFun id = do
  functions <- CMR.asks functions
  case M.lookup id functions of
    Nothing -> fail $ "Function " ++ show id ++ " not declared."
    Just t  -> return t

-- | Checks all function definitions at the top level.
checkFuns ::[FnDef] -> Err FunHeader
checkFuns functions =
  foldM (\m (FunDef ret_t id args _ ) ->
         do case M.lookup id m of
              Just  _ -> fail $ "Function " ++ show id ++ " defined twice."
              Nothing ->
                do let argTypes = map (\(Argument t _) -> t) args
                   return $ M.insert id (argTypes, ret_t) m)
          M.empty (initializeDefs ++ functions)
    where 
      initializeDefs = 
        [ FunDef Void (Ident "printInt")    [Argument Int (Ident "x")]  (SBlock [])
        -- void   printInt(int x)
        , FunDef Void (Ident "printDouble") [Argument Doub (Ident "x")] (SBlock [])
        -- void  printDouble(double x)
        , FunDef Void (Ident "printString") [Argument String (Ident "x")] (SBlock [])
        -- void printString(String x)
        , FunDef Int  (Ident "readInt")     []                     (SBlock [])
        -- int readInt()
        , FunDef Doub (Ident "readDouble")  []                     (SBlock [])
        -- double readDouble()
        ]

                                            
-- | Typechecks a program.
typecheck :: (Structs, [FnDef], ObjectH) -> Err (Structs, [FnDef])
typecheck (structDefs, fnDefs, objectH) = do
  initFuns  <- checkFuns fnDefs
  let initialREnv = REnv { functions   = initFuns
                         , structs     = structDefs }

      initialSEnv = SEnv { context = [] }
  typedFnDefs <- evalStateT
                 (runReaderT (mapM typeCheckFun fnDefs) initialREnv)
                 initialSEnv
  return (structDefs, typedFnDefs)

-- | Typechecks a function definition.
typeCheckFun :: FnDef -> TypeCheck FnDef
typeCheckFun (FunDef ret_t id args (SBlock stmts)) = do
  newBlock
  mapM_ (\(Argument t idArg)  -> createVarIfNotExists idArg t) args
  (has_ret, BStmt typedStmts) <- typeCheckStmt ret_t (BStmt (SBlock stmts))
  unless (has_ret || (=~=) ret_t Void)
           $ fail $ "Missing return statement in function " ++ show id
  removeBlock
  return $ FunDef ret_t id args typedStmts


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

typeCheckLVal :: LVal -> TypeCheck LVal
typeCheckLVal lval =
  case lval of
    LValVar ident ndims ->
      do typedAddrExpr   <- mapM (checkTypeExpr Int) $ dimsToExprs ndims
         t               <- lookupVar ident
         let dimT = case t of
                      DimT t' tDim -> DimT t' (tDim - fromIntegral (length ndims))
                      t'           -> t'
         return $ LValTyped (LValVar ident (exprsToDims typedAddrExpr)) dimT

    LValStr name field ->
      do t <- lookupVar name
         case t of
           Pointer strName _ ->
             do structs <- CMR.asks structs
                case M.lookup strName structs of
                  Nothing -> fail $ "Struct " ++ show strName ++ " not defined."
                  Just (Struct _ fields) ->
                    do case lookup field . map (\(StrField t id) -> (id,t))
                              $ fields of
                         Nothing ->
                           fail "Trying to reference a field that doesn't exists"
                         Just t' -> return $ LValTyped lval t'

           _ -> error $ "Variable " ++ show name ++ " must be a pointer."


-- | Typechecks the validity of a given statement.
typeCheckStmt :: Type -> Stmt -> TypeCheck (Bool, Stmt)
typeCheckStmt funType stm =
    case stm of
      Empty -> return (False, Empty)
      BStmt (SBlock stmts) ->
        do newBlock
           results <- mapM (typeCheckStmt funType) stmts
           let (rets, typedStmts) = unzip results
           removeBlock
           return (or rets, BStmt (SBlock typedStmts))
      Decl t items -> 
        do typedExprs <- mapM (checkItem t) items
           let typedItems = zipWith typeItem items typedExprs
           mapM_ (uncurry createVarIfNotExists) $
                 zip (map getIdent items) (repeat t)
           return (False, Decl t typedItems)
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
        do typedLVal@(LValTyped _ t') <- typeCheckLVal lval
           typedExpr       <- checkTypeExpr t' exp
           return (False, Ass typedLVal typedExpr)

      Incr lval ->
        do typedLVal@(LValTyped _ t') <- typeCheckLVal lval
           checkTypeNum t'
           return (False, Incr typedLVal)
            
      Decr lval ->
        do typedLVal@(LValTyped _ t') <- typeCheckLVal lval
           checkTypeNum t'
           return (False, Decr typedLVal)
                   
      Ret exp ->
          checkTypeExpr funType exp >>= (\typedExpr -> return (True, Ret typedExpr))
      VRet    -> if (=~=) funType Void then return (True, VRet)
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
               let has_ret = case exp of
                              ELitTrue  -> ret1
                              ELitFalse -> ret2
                              _         -> ret1 && ret2
               return (has_ret, CondElse typedExpr typedStmt1 typedStmt2)
      While exp stm' -> do
               typedExpr <- checkTypeExpr Bool exp
               (stm_has_ret, typedStmt) <- typeCheckStmt funType stm'
               let has_ret = case exp of
                          ELitTrue  -> stm_has_ret
                          _         -> False
               return (has_ret, While typedExpr typedStmt)
      SExp exp -> inferTypeExpr exp >>=
                  (\typedExpr -> return (False, SExp typedExpr))

      For _ _ _ -> fail "The expression should be already desugared."


-- | Calculate type equality with dimensional check.
(=~=) :: Type -> Type -> Bool
(=~=) (DimT t1 dim1) (DimT t2 dim2) =  t1 == t2 && dim1 == dim2
(=~=) (DimT t1 dim1) t2             =  t1 == t2 && dim1 == 0
(=~=) t1             (DimT t2 dim2) =  t1 == t2 && dim2 == 0
(=~=) (Pointer name1 st) (Pointer name2 st2)
      | name1 == name2   = True
      | name2 `elem` st = True
                           
(=~=) t1 t2 = t1 == t2
-- | Checks the type of an expresion in the given environment.
checkTypeExpr :: Type -> Expr -> TypeCheck Expr
checkTypeExpr t exp = do
  typedExpr@(ETyped _ expt') <- inferTypeExpr exp
  when (not $ expt' =~= t) $
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

      Method (Var id eDims) (Var (Ident "length") []) -> do
        (DimT t ndims) <- lookupVar id
        when ((fromIntegral . length) eDims > ndims)
               $ fail "Indexing failure: Too many dimensions"
        typedEDims <- mapM (checkTypeExpr Int) (dimsToExprs eDims)
        return (ETyped (Method (Var id 
                        (exprsToDims typedEDims)) (Var (Ident "length") [])) Int)
                
      Method _ _ -> fail $ "Bad method invocation: " ++ show exp
                    
      ENew t eDims     ->
       -- New object in the heap.
       if null eDims then
         case t of
           Pointer structName supertypes -> 
             return (ETyped exp (Pointer structName supertypes))
           _ -> fail $ "Cannot create an object of a primitive type: " ++ show t
       -- New array of type t
       else do
         let ndims = fromIntegral $ length eDims
         typedEDims <- mapM (checkTypeExpr Int) (dimsToExprs eDims)
         checkValidArrayType t
         return (ETyped (ENew t (exprsToDims typedEDims)) (DimT t ndims))

      PtrDeRef id1 id2  -> do
             Pointer structName supertypes <- lookupVar id1
             Just (Struct name fields) <- CMR.asks (M.lookup structName . structs)
             case lookup id2 . map (\(StrField t id) -> (id,t)) $ fields of
               Nothing -> fail "Trying to reference a field that doesn't exists."
               Just t' -> return $ ETyped exp t'

      ENull id  -> return (ETyped NullC (Pointer id []))

      EString s        -> return $ ETyped exp String

      EApp id args     ->
        do (args_type, ret_type) <- lookupFun id
           typedArgs <- checkArgs id args_type args
           return $ ETyped (EApp id typedArgs) ret_type

      MApp (Ident id) obj args ->
        do (ETyped _ (Pointer (Ident strName) _)) <- inferTypeExpr obj
           let methodClass = Ident $ strName ++ "." ++ id
           (args_type, ret_type) <- lookupFun methodClass
           typedArgs <- checkArgs methodClass args_type (obj : args)
           return $ ETyped (EApp methodClass typedArgs) ret_type

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
    if t1 =~= t2 then return Bool
    else
      fail $ "Cannot compare type " ++ show t1
                                   ++ " with type " ++ show t2
     where
        checkVoid t = when (t =~= Void)$ fail "Void is not comparable."

