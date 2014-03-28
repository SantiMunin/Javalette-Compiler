module Backend.LLVM where

import Data.List (intersperse)

data Label  = IntLab Int | SLab String

instance Show Label where
  show (IntLab n) = "lab" ++ show n
  show (SLab s)   = s

newtype Register = Register String

instance Show Register where
  show (Register n) = "%t" ++ n
                      
type Id = String
  
data Ty = I32
        | D
        | I1
        | V
        | I8
        | Ptr Ty
        | ArrayT Ty
          
instance Show Ty where
  show I32 = "i32"
  show D   = "double"
  show I1  = "i1"
  show V   = "void"
  show I8  = "i8"
  show (Ptr t) =  show t ++ "*"
  show (ArrayT t) = "%array" ++ show t

data Constant = CI32 { i32 :: Integer }
              | CD   { d   :: Double  }
              | CI1  { i1  :: Bool }
              | Null
              | Undef
                
instance Show Constant where
  show (CI32 int ) = show int
  show (CD double) = show double
  show (CI1 bool)  = case bool of
                       True  -> "true"
                       False -> "false"
  show Null        = "null"
  show Undef       = "undef"     
data Operand = Const { const :: Constant }
             | Reg   { reg   :: Register }
             | Emp
               
instance Show Operand where
  show (Const cons) = show cons
  show (Reg   reg ) = show reg

data NonTerminator = IAdd { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | ISub { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | IMul { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | IDiv { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | IMod { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | INeg { op1 :: Operand
                         , ty  :: Ty }
                               
                   | ILth { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | ILe  { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | IGth { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | IGe  { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | IEq { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | INEq { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | IAnd { op1 :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | IOr { op1  :: Operand
                         , op2 :: Operand
                         , ty  :: Ty }

                   | INot { op1 :: Operand
                         , ty  :: Ty }

                   | IAlloc { ty  :: Ty }

                   | ILoad { addr :: Register
                           , ty   :: Ty }

                   | IStore { addr :: Register
                            , val  :: Operand
                            , ty    :: Ty }

                   | ICall { ty    :: Ty
                           , id    :: Id
                           , args  ::[(Ty,Operand)]
                            }
                   | GetElementPtr { ptrVector :: Ty
                                   , ptrVal    :: Operand
                                   , sub       :: [(Ty,Operand)]
                                   }

                   | PtrToInt { ptrTy :: Ty
                              , op    :: Register
                              , ty2   :: Ty }
                     
                   | BitCast { ty  :: Ty
                             ,  op :: Register
                             , ty2 :: Ty }
                                      
                   | Lit { str :: String }
instance Show NonTerminator where
  show nonTerm =
    case nonTerm of
      IAdd op1 op2 ty -> concat [isD ty, "add ",show ty, " ", show op1, " ,", show op2]
      ISub op1 op2 ty -> concat [isD ty, "sub ",show ty, " ", show op1, " ,", show op2]
      IMul op1 op2 ty -> concat [isD ty, "mul ",show ty, " ", show op1, " ,", show op2]
      INeg op1 ty     -> concat [isD ty, "sub ",show ty, " ", zero    , " ,", show op1]
        where
          zero = case ty of
                       D   -> "0.0"
                       I32 -> "0"
      IMod op1 op2 ty -> concat [instr, "rem ",show ty, " ", show op1, " ,", show op2]
        where
          instr = case ty of
                    D   -> "f"
                    I32 -> "s"
      IDiv op1 op2 ty -> concat [instr, "div ",show ty, " ", show op1, " ,", show op2]
        where
          instr = case ty of
                    D   -> "f"
                    I32 -> "s"

      ICall ty id args ->  concat [ "call " ++ show ty
                                  , " @" ++ id
                                  , "(" ++ concat (intersperse "," ( showArgs args )) ++ ")"]
      ILth op1 op2 ty -> concat [instr, show ty," ", show op1,", ", show op2] 
        where
          instr = case ty of
                    D   -> "fcmp olt "
                    I32 -> "icmp slt "
      ILe  op1 op2 ty ->concat [instr, show ty," ", show op1,", ", show op2] 
        where
          instr = case ty of
                    D   -> "fcmp ole "
                    I32 -> "icmp sle "
      IGth op1 op2 ty -> concat [instr, show ty," ", show op1,", ", show op2] 
        where
          instr = case ty of
                    D   -> "fcmp ogt "
                    I32 -> "icmp sgt "
      IGe  op1 op2 ty -> concat [instr, show ty," ", show op1,", ", show op2] 
        where
          instr = case ty of
                    D   -> "fcmp oge "
                    I32 -> "icmp sge "
      IEq op1 op2 ty -> concat [instr, show ty," ", show op1,", ", show op2] 
        where
          instr = case ty of
                    D   -> "fcmp oeq "
                    I32 -> "icmp eq "
                    I1  -> "icmp eq "
                    
      INEq op1 op2 ty ->concat [instr, show ty," ", show op1,", ", show op2] 
        where
          instr = case ty of
                    D   -> "fcmp one "
                    I32 -> "icmp ne "
                    I1  -> "icmp ne "
      IAnd op1 op2 ty -> concat ["and ", show ty, " ", show op1,", ",show op2]  
      IOr op1  op2 ty -> concat ["or ", show ty, " ", show op1,", ",show op2]  
      INot op1 ty -> concat["xor ", show ty," " , show op1, ", true"]
      IAlloc ty -> concat ["alloca ", show ty]
      ILoad addr ty -> concat ["load ", show ty,"* ", show addr]
      IStore addr val ty -> concat ["store ",show ty, " ", show val,", ", show ty, "* ", show addr]
      Lit str -> str            
      GetElementPtr ptr1 ptr2 sub -> concat ["getelementptr ",show ptr1," ",show ptr2, ", "
                                            , concat . intersperse "," $ index]
        where
          index = map (\(ty,op) -> show ty ++ " " ++ show op) sub
      BitCast ty elem ty2  -> "bitcast " ++ show ty ++ " " ++ show elem ++ " to " ++ show ty2
      PtrToInt ty elem ty2 -> "ptrtoint " ++ show ty ++ " " ++ show elem ++ " to " ++ show ty2
    where
      isD D   = "f"
      isD I32 = ""
      showArgs = map (\(t, v) -> show t ++ " " ++ show v) 
      cmp ty cond = case ty of
                       I32 -> "icmp " ++ cond ++ " "
                       D   -> "fcmp " ++ cond ++ " " 

data Terminator = IVRet
                | IRet { retOp :: Operand
                       , retTy :: Ty }
                | BrC   { cond  :: Operand
                        , true_l  :: Label
                        , false_l :: Label
                        }
                | BrU { jump :: Label }
                | Unreachable
                  
instance Show Terminator where
  show term =
    case term of
      IRet op ty -> concat ["ret " ,show ty ," " ,show op]
      IVRet      -> "ret void"
      BrC cond true false -> concat [ "br i1 ", show cond
                                    , ", label %", show true
                                    , ", label %", show false ]
      BrU label           -> "br label %" ++ show label
      Unreachable         -> "unreachable"
                             
data Instr = NonTerm  NonTerminator (Maybe Register)
           | Term     Terminator
           | Label    Label

data Function = Fun { idF    :: Id
                    , tyF    :: Ty
                    , argsF  :: [(Id,Ty)]
                    , instr  :: [IBlock] }

instance Show Function where
  show (Fun name ty args blocks) = unlines $ [header] ++ map show blocks ++ ["}"]
        where
          header = concat ["define " ,show ty ," @" ,name
                          ,"(" ,concat (intersperse "," (map showArg args))
                          ,")" ," {" ]
          showArg (id,t) = show t ++ " %t" ++ id 

data IBlock = IBlock { lab :: Label
                     , ins :: [(NonTerminator, Maybe Register)]
                     , ter :: Terminator }


instance Show IBlock where
  show (IBlock lab ins ter) = unlines [ "\n" ++ show lab ++ ":"
                                     , unlines $ map ((indent++) . showNonT) ins
                                     , indent ++  show ter
                                     ]
    where
      indent :: String
      indent = "  "
      showNonT (nonterm,reg) = maybe "" ((++ " = ") . show) reg ++ show nonterm

                                 

mkFun :: Id -> Ty -> [(Id,Ty)] -> [Instr] -> Function


         
type Accum = Maybe (Label,[(NonTerminator,Maybe Register)])
  
addLabel   :: Label -> ([IBlock],Accum) -> ([IBlock],Accum)
addLabel label (block,Nothing) = (block,Just (label,[]))

addNonTerm :: (NonTerminator,Maybe Register) -> ([IBlock],Accum) -> ([IBlock],Accum)
addNonTerm nonterm (block, Nothing) = (block,Nothing)
addNonTerm nonterm (block, (Just (lab,instr))) = (block,Just (lab,instr ++ [nonterm]))

addTerm :: Terminator -> ([IBlock],Accum) -> ([IBlock],Accum)
addTerm term (block,(Just (lab,nonterm))) = (block ++ [IBlock lab nonterm term],Nothing)
addTerm term (block,Nothing)              = (block,Nothing)
                                            
mkFun id ty args instr = Fun id ty args (go instr ([],Just (SLab "entry",[])))
  where
    go [] (blocks, Nothing)            = blocks
    go [] (blocks, Just (label,instr)) = blocks ++ [IBlock label instr Unreachable]
    go (i:is) acc                     =
      case i of
        Label lab             -> go is (addLabel lab acc)
        NonTerm nonterm reg   -> go is (addNonTerm (nonterm,reg) acc)
        Term term             -> go is (addTerm term acc)
