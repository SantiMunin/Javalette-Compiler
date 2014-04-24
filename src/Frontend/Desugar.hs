{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Frontend.Desugar (desugar) where

import           Javalette.Abs
import           Javalette.ErrM

import           Internal.Types

import           Control.Monad.State  as CMS
import           Control.Monad.Reader as CMR

import           Data.Map            (Map)
import qualified Data.Map            as M

import qualified Data.List as L
  
data ReadEnv   = REnv { pointers   :: Pointers
                      , hierarchy  :: ObjectH }

data StateEnv  = SEnv { sugarVar  :: Int
                      , classAttr :: [Ident] }

               
type Desugar a = ReaderT ReadEnv (StateT StateEnv Err) a

type Pointers = Map Ident Ident

type Classes = Map Ident ([SField],[FnDef])

newClassAttr :: [Ident] -> Desugar ()
newClassAttr attr = CMS.modify (\env -> env { classAttr = attr })

emptyClassAttr :: Desugar ()
emptyClassAttr = CMS.modify (\env -> env { classAttr = [] })

deleteClassAttr :: Ident -> Desugar ()
deleteClassAttr id =
  CMS.modify (\env -> env { classAttr = L.delete id $ classAttr env })

isClassAttr :: Ident -> Desugar Bool
isClassAttr id = CMS.gets ((elem id) . classAttr)

lookSuperTypes :: Ident -> Desugar (Maybe [Ident])
lookSuperTypes type' = CMR.asks (M.lookup type' . hierarchy)
                       
-- | Take a new unique variable to use in desugar.
newSugarVar :: Desugar Ident
newSugarVar = do
  var <- CMS.gets sugarVar
  CMS.modify (\env -> env { sugarVar = sugarVar env + 1})
  return . Ident $ "_" ++ show var
           
-- | Split top level defintions in structs, pointers, classes and functions.
splitDefinitions :: [TopDef] -> ([TypeDecl],[TypeDecl],[TypeDecl],[FnDef])
splitDefinitions defs =
  (\(a,b,c,d) -> (reverse a,reverse b, reverse c, reverse d))
  $ foldl select ([], [], [], []) defs
  where
    select (s, p, c, f) definition =
      case definition of
        TopFnDef def@(FunDef _ _ _ _)      -> (s, p, c, def:f)
        TopTypeDecl def@(StructDef _ _)    -> (def:s, p, c, f)
        TopTypeDecl def@(PtrDef _ _)       -> (s, def:p, c, f)
        TopTypeDecl def@(ClassDef _ _ _ _) -> (s, p, def:c, f)

desugarMethod :: Ident -> FnDef -> FnDef
desugarMethod name@(Ident class') (FunDef type' (Ident id) args block) =
  (FunDef type'
          (Ident $ class' ++ "." ++ id)
          (Argument (Ref name) (Ident "self") : args)
          block)

-- | Desugar a program without typechecking.
desugar:: Program -> Err (Structs, [FnDef], ObjectH)
desugar (Prog defs) = do
  let (s, p, c, f)   = splitDefinitions defs
  (structs,pointers,classes,objectH) <- checkStructs p s c
  let initialREnv     = REnv pointers objectH
      initialSEnv     = SEnv 0 [] 
      functions       = zip (repeat []) f

      methodsTopLevel = concatMap
                        (\(class', (attr, methods)) ->
                           zip (repeat (map (\(StrField _ id) -> id) attr))
                               (map (desugarMethod class') methods)
                        ) (M.toList classes)

  desugaredTopLevel  <- evalStateT
                        (runReaderT (mapM (uncurry desugarFnDef)
                                          (functions ++ methodsTopLevel))
                         initialREnv)
                        initialSEnv

  return (structs, desugaredTopLevel, objectH)

-- | Check top level struct declaration against pointer declaration,
--   checking for name clashes.
checkStructs :: [TypeDecl] -- ^ Pointer definitions
             -> [TypeDecl] -- ^ Struct  definitions
             -> [TypeDecl] -- ^ Classes definitions
             -> Err (Structs, Pointers, Classes, ObjectH)

checkStructs pointerDefs structDefs classDefs = do
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
                                 return $ f ++ [StrField (Pointer strName []) id]
                           _ ->  return  $ f ++ [StrField t id]
                      ) [] fields
                    return $ M.insert name (Struct name checkedFields) m
             ) M.empty structDefs

  (newStrs,newPtrs,classes,objectH) <-
    foldM
    (\(strs,ptrs,classes,objectH)
      (ClassDef name@(Ident class') hierarchy fields classMethods) ->
       case M.lookup name strs of
         Just _  -> fail $ concat ["Class name "
                                  , show name
                                  , "already defined."]
         Nothing ->
           do (parentAttr, parentMethods, supertypes) <-
                case hierarchy of
                  HEmpty -> return ([],[],[])
                  HExtend parent ->
                    case M.lookup parent classes of
                      Nothing -> fail $ concat [ "Class "
                                               , show name
                                               , "doesnt make sens"]
                      Just (a,m) ->
                        do let Just supertypes = M.lookup parent objectH 
                           return (a,m,parent : supertypes)

              let newPtrs    = M.insert name name ptrs
                  newObjectH = M.insert name supertypes objectH
              checkedFields <- 
                foldM
                (\f (StrField t id) ->
                   case t of
                     Ref name ->
                       case M.lookup name newPtrs of
                         Nothing ->
                           fail $ concat [ "Attribute "
                                         , show id
                                         , " is not valid."]
                         Just strName ->
                           do let Just supertypes = M.lookup strName newObjectH
                              return $ f ++ [StrField (Pointer strName supertypes ) id]
                     _ ->  return  $ f ++ [StrField t id]
                ) [] (L.union fields parentAttr)

              return ( M.insert name (Struct name checkedFields) strs
                     , newPtrs
                     , M.insert name
                                  (checkedFields
                                  ,L.unionBy fnEq classMethods parentMethods) classes
                     , newObjectH)
    ) (structs, M.union pointers (M.mapWithKey const structs)
      , M.empty, M.map (const []) structs) classDefs

  return (newStrs, newPtrs, classes, objectH)
    where
      fnEq (FunDef _ id1 _ _) (FunDef _ id2 _ _) = id1 == id2
                                                   
desugarFnDef :: [Ident] -> FnDef -> Desugar FnDef
desugarFnDef classAttr (FunDef type' id args block) = do
  newClassAttr classAttr
  desugaredType  <- desugarType type'
  desugaredArgs  <- mapM desugarArg args
  desugaredBlock <- desugarBlock block
  emptyClassAttr
  return (FunDef desugaredType id desugaredArgs desugaredBlock)

desugarArg :: Arg -> Desugar Arg
desugarArg (Argument type' id) = do
  desugaredType <- desugarType type'
  deleteClassAttr id
  return (Argument desugaredType id)

desugarBlock :: Block -> Desugar Block
desugarBlock (SBlock stmts) = fmap SBlock $ mapM desugarStmt stmts

desugarStmt :: Stmt -> Desugar Stmt
desugarStmt stmt = case stmt of
  BStmt block  -> fmap BStmt $ desugarBlock block
  Decl type' items     -> do
    desugaredType  <- desugarType type'
    desugaredItems <- mapM desugarItem items
    return (Decl desugaredType desugaredItems)
  For (ForDecl t id) exp@(Var v eDims) innerStm ->
    do index  <- newSugarVar
       len    <- newSugarVar
       desugaredType <- desugarType t
       desugaredStmt <- desugarStmt innerStm
       return $ (BStmt
                 (SBlock
                  [ Decl Int [Init index  (ELitInt 0)]
                  , Decl Int [Init len (Method exp (Var (Ident "length") [])) ]
                  , Decl desugaredType [NoInit id]
                  , While (ERel
                           (Var index [])
                           LTH
                           (Var len []))
                            (BStmt
                             (SBlock
                              [Ass (LValVar id [])
                                     (Var v (eDims
                                             ++ [DimAddr (Var index [])]))
                              , Incr (LValVar index [])
                              , desugaredStmt
                              ]))
                  ]))
  For (ForDecl t id) _ innerStm -> fail "The expression should be a variable."
  Ass lval expr   -> liftM2 Ass (desugarLVal lval) (desugarExpr expr)
  Ret expr        -> liftM Ret $ desugarExpr expr
  Cond expr stmt  -> liftM2 Cond (desugarExpr expr) (desugarStmt stmt)
  CondElse expr stmt1 stmt2  ->
    liftM3 CondElse (desugarExpr expr) (desugarStmt stmt1) (desugarStmt stmt2)
  While expr stmt -> liftM2 While (desugarExpr expr) (desugarStmt stmt)
  SExp expr       -> liftM SExp $ desugarExpr expr
  Incr lval       -> liftM Incr $ desugarLVal lval
  Decr lval       -> liftM Decr $ desugarLVal lval
  _               -> return stmt

desugarLVal :: LVal -> Desugar LVal
desugarLVal lval = case lval of
  LValVar id dimas  -> do
    isAttr <- isClassAttr id
    if isAttr then
      return (LValStr (Ident "self") id)
    else
      liftM (LValVar id) (mapM desugarDimA dimas) 
  LValStr id1 id2   -> return (LValStr id1 id2)


desugarItem :: Item -> Desugar Item
desugarItem item = case item of
  Init id expr -> do
    desugaredExpr <- desugarExpr expr
    deleteClassAttr id
    return (Init id desugaredExpr)
  NoInit id -> do
    deleteClassAttr id
    return (NoInit id)

desugarType :: Type -> Desugar Type
desugarType ty =
  case ty of
    Array t' dims -> return $ DimT t' (fromIntegral $ length dims)
    Ref name -> do
           pointers <- CMR.asks pointers
           case M.lookup name pointers of
             Nothing -> fail $ "Struct with name: " ++ show name ++ " not defined."
             Just strName  ->
               do Just supertypes <- lookSuperTypes strName
                  return (Pointer strName supertypes)
    _            -> return ty

desugarDimA :: DimA -> Desugar DimA
desugarDimA (DimAddr expr) = liftM DimAddr $ desugarExpr expr

desugarExpr :: Expr -> Desugar Expr
desugarExpr expr =
  case expr of
    Var id dimas -> do
      isAttr <- isClassAttr id
      if isAttr then
        return (PtrDeRef (Ident "self") id)
      else
        liftM (Var id) (mapM desugarDimA dimas) 
    ENew type' dimas  -> liftM2 ENew (desugarType type') (mapM desugarDimA dimas)
    ENull id -> do
      pointers <- CMR.asks pointers
      case M.lookup id pointers of
        Nothing          -> fail $ "Type not defined: " ++ show id
        Just structName  -> return (ENull structName)
    EApp id@(Ident name) exprs  -> 
      liftM (EApp id) $ mapM desugarExpr exprs

    ERel expr1 relop expr2  -> do
      desugaredExpr1 <- desugarExpr expr1
      desugaredExpr2 <- desugarExpr expr2
      return (ERel desugaredExpr1 relop desugaredExpr2)
    Method expr1 (EApp id exprs) ->
      do object <- desugarExpr expr1
         args   <- mapM desugarExpr exprs
         return $  MApp id object args
    Neg expr  -> liftM Neg $ desugarExpr expr
    Not expr  -> liftM Not $ desugarExpr expr
    EMul expr1 mulop expr2  -> do
      desugaredExpr1 <- desugarExpr expr1
      desugaredExpr2 <- desugarExpr expr2
      return (EMul desugaredExpr1 mulop desugaredExpr2)
    EAdd expr1 addop expr2  -> do
      desugaredExpr1 <- desugarExpr expr1
      desugaredExpr2 <- desugarExpr expr2
      return (EAdd desugaredExpr1 addop desugaredExpr2)
    EAnd expr1 expr2  -> liftM2 EAnd (desugarExpr expr1) (desugarExpr expr2)
    EOr  expr1 expr2  -> liftM2 EOr  (desugarExpr expr1) (desugarExpr expr2)
    _ -> return expr
