{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Frontend.Desugar where

import           Javalette.Abs
import           Javalette.ErrM

import           Internal.Types

import           Control.Monad.State  as CMS
import           Control.Monad.Reader as CMR

import           Data.Map            (Map)
import qualified Data.Map            as M

data ReadEnv   = REnv { pointers :: Pointers }

data StateEnv  = SEnv { sugarVar :: Int }
               
newSugarVar :: Desugar Ident
newSugarVar = do
  var <- CMS.gets sugarVar
  CMS.modify (\env -> env { sugarVar = sugarVar env + 1})
  return . Ident $ "_" ++ show var
         
type Desugar a = ReaderT ReadEnv (StateT StateEnv Err) a

type Pointers = Map Ident Ident
  
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

-- | Desugar a program without typechecking.
desugar:: Program -> Err (Structs, [FnDef])
desugar (Prog defs) = do
  let (s, p, c, f)   = splitDefinitions defs
  (structs,pointers) <- checkStructs p s
  let initialREnv     = REnv pointers
      initialSEnv     = SEnv 0
  desugaredFuns      <- evalStateT
                        (runReaderT (mapM desugarFnDef f) initialREnv)
                        initialSEnv
  return (structs, desugaredFuns)

-- | Check top level struct declaration against pointer declaration,
--   checking for name clashes.
checkStructs :: [TypeDecl] -> [TypeDecl] -> Err (Structs, Pointers)
checkStructs pointerDefs structDefs = do
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

  return (structs, pointers)

desugarFnDef :: FnDef -> Desugar FnDef
desugarFnDef (FunDef type' id args block) = do
  desugaredType  <- desugarType type'
  desugaredArgs  <- mapM desugarArg args
  desugaredBlock <- desugarBlock block
  return (FunDef desugaredType id desugaredArgs desugaredBlock)

desugarArg :: Arg -> Desugar Arg
desugarArg (Argument type' id) = do
  desugaredType <- desugarType type'
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
                  , Decl Int [Init len (Method v eDims (Ident "length") MTailEmpty) ]
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
                              , Incr index
                              , desugaredStmt
                              ]))
                  ]))
  For (ForDecl t id) _ innerStm -> fail "The expression should be a variable."
  Ass lval expr   -> liftM (Ass lval) (desugarExpr expr)
  Ret expr        -> liftM Ret $ desugarExpr expr
  Cond expr stmt  -> liftM2 Cond (desugarExpr expr) (desugarStmt stmt)
  CondElse expr stmt1 stmt2  ->
    liftM3 CondElse (desugarExpr expr) (desugarStmt stmt1) (desugarStmt stmt2)
  While expr stmt -> liftM2 While (desugarExpr expr) (desugarStmt stmt)
  SExp expr       -> liftM SExp $ desugarExpr expr
  _               -> return stmt

desugarItem :: Item -> Desugar Item
desugarItem item = case item of
  Init id expr -> liftM (Init id) $ desugarExpr expr
  _ -> return item

desugarType :: Type -> Desugar Type
desugarType ty =
  case ty of
    Array t' dims -> return $ DimT t' (fromIntegral $ length dims)
    Ref name -> do
           pointers <- CMR.asks pointers
           case M.lookup name pointers of
             Nothing -> fail $ "Struct with name: " ++ show name ++ " not defined."
             Just strName  -> return (Pointer strName)
    _            -> return ty

desugarExpr :: Expr -> Desugar Expr
desugarExpr expr =
  case expr of
    ENull id -> do
      pointers <- CMR.asks pointers
      case M.lookup id pointers of
        Nothing          -> fail $ "Type not defined: " ++ show id
        Just structName  -> return (ENull structName)
    EApp id exprs  -> liftM (EApp id) $ mapM desugarExpr exprs
    ERel expr1 relop expr2  -> do
      desugaredExpr1 <- desugarExpr expr1
      desugaredExpr2 <- desugarExpr expr2
      return (ERel desugaredExpr1 relop desugaredExpr2)
    _ -> return expr
