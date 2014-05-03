-- | Internal representation of a LLVM program. Useful in order 
-- to make sure we are generating correct programs.
module Backend.LLVM where

import Data.List (intercalate, intersperse)

-- | A label can be either a number or a string. 
-- The numbers will be displayed as "lab" ++ n.
data Label  = IntLab Int | SLab String

instance Show Label where
  show (IntLab n) = "lab" ++ show n
  show (SLab s)   = s
 
-- | An ID is a String.
type Id = String
  
-- | A LLVM type. It includes primitive (int, floating p., boolean 
-- void, 8-bit int), pointers and arrays.
data Ty = I32
        | I64 -- ^ To allow 64-bits hashes
        | D
        | I1
        | V
        | I8
        | Ptr Ty
        | ArrayT Ty Integer
        | Def Id
        | F Ty [Ty]
        | Str [(Id,Ty)]
          
instance Show Ty where
  show I32 = "i32"
  show I64 = "i64"
  show D   = "double"
  show I1  = "i1"
  show V   = "void"
  show I8  = "i8"
  show (Ptr t) =  show t ++ "*"
  show (ArrayT t _) = "%array" ++ show t
  show (Def id) = "%" ++ id
  show (F rT argT) = concat [ show rT
                              , "("
                              , if null argT then "..."
                                else intercalate "," $ map show argT
                              , ")*"]
    
-- | Constants are directly written on the target code. 
data Constant = CI32 { i32 :: Integer }
              | CI64 { i64 :: Integer }
              | CD   { d   :: Double  }
              | CI1  { i1  :: Bool }
              | Null
              | Undef
              | LitCode  { text :: String } -- ^ Literal code
                
instance Show Constant where
  show (CI32 int)  = show int
  show (CI64 int)  = show int
  show (CD double) = show double
  show (CI1 bool)  = if bool then "true" else "false" 
  show Null        = "null"
  show Undef       = "undef"
  show (LitCode s)     = s

-- | A LLVM register. Shown on the target code as
-- % ++ name.
newtype Register = Register String

instance Show Register where
  show (Register n) = "%" ++ n

-- | An operand can be a constant, a register, or nothing.
data Operand = Const { const :: Constant }
             | Reg   { reg   :: Register }
             | Global { name :: String }
             | Emp
               
instance Show Operand where
  show (Const c) = show c
  show (Reg   r) = show r
  show (Global s) = "@" ++ s


-- | A nonterminator operation is just any operation which does not 
-- ends a function (i.e. arithmetic, comparisons, stores, loads...).
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
      IAdd a b t -> concat [isD t, "add ", show t, " ", show a, ", ", show b]
      ISub a b t -> concat [isD t, "sub ", show t, " ", show a, ", ", show b]
      IMul a b t -> concat [isD t, "mul ", show t, " ", show a, ", ", show b]
      INeg a t   -> concat [isD t, "sub ", show t, " ", zero  , ", ", show a]
        where
          zero = case t of
                       D   -> "0.0"
                       I32 -> "0"
      IMod a b t -> concat [instr, "rem ", show t, " ", show a, ", ", show b]
        where
          instr = case t of
                    D   -> "f"
                    I32 -> "s"
      IDiv a b t -> concat [instr, "div ", show t, " ", show a, ", ", show b]
        where
          instr = case t of
                    D   -> "f"
                    I32 -> "s"

      ICall t id args ->  concat [ "call " ++ show t
                                 , " "
                                 , id
                                 , "(" ++ intercalate "," ( showArgs args ) ++ ")"]
      ILth a b t -> concat [instr, show t, " ", show a, ", ", show b] 
        where
          instr = case t of
                    D   -> "fcmp olt "
                    I32 -> "icmp slt "
      ILe  a b t ->concat [instr, show t, " ", show a, ", ", show b] 
        where
          instr = case t of
                    D   -> "fcmp ole "
                    I32 -> "icmp sle "
      IGth a b t -> concat [instr, show t, " ", show a, ", ", show b] 
        where
          instr = case t of
                    D   -> "fcmp ogt "
                    I32 -> "icmp sgt "
      IGe  a b t -> concat [instr, show t, " ", show a, ", ", show b] 
        where
          instr = case t of
                    D   -> "fcmp oge "
                    I32 -> "icmp sge "
      IEq a b t -> concat [instr, show t, " ", show a, ", ", show b] 
        where
          instr = case t of
                    D   -> "fcmp oeq "
                    I32 -> "icmp eq "
                    I1  -> "icmp eq "
                    Ptr _ -> "icmp eq " 
      INEq a b t -> concat [instr, show t, " ", show a, ", ", show b] 
        where
          instr = case t of
                    D   -> "fcmp one "
                    I32 -> "icmp ne "
                    I1  -> "icmp ne "
                    Ptr _  -> "icmp ne "
      IAnd a b t -> concat ["and ", show t, " ", show a, ", ",show b]  
      IOr a  b t -> concat ["or ", show t, " ", show a, ", ",show b]  
      INot a t -> concat["xor ", show t, " " , show a, ", true"]
      IAlloc t -> "alloca " ++ show t
      ILoad addr t -> concat ["load ", show t, "* ", show addr]
      IStore addr val t -> concat ["store ",show t, " ", show val, ", ", show t, "* ", show addr]
      Lit str -> str            
      GetElementPtr ptr1 ptr2 sub -> concat ["getelementptr ", show ptr1, " ",show ptr2, ", "
                                            , intercalate "," index]
        where
          index = map (\(t,op) -> show t ++ " " ++ show op) sub
      BitCast t elem t2  -> "bitcast " ++ show t ++ " " ++ show elem ++ " to " ++ show t2
      PtrToInt t elem t2 -> "ptrtoint " ++ show t ++ " " ++ show elem ++ " to " ++ show t2
    where
      isD D   = "f"
      isD I32 = ""
      showArgs = map (\(t, v) -> show t ++ " " ++ show v) 
      cmp t cond = case t of
                       I32 -> "icmp " ++ cond ++ " "
                       D   -> "fcmp " ++ cond ++ " " 

-- | A terminator is a instruction that can terminate a 
-- function or block (i.e. returns, jumps).
data Terminator = IVRet
                | IRet { retOp :: Operand
                       , retTy :: Ty }
                | BrC   { cond    :: Operand
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

-- | An instruction can be a non-terminator, a terminator or a label.
data Instr = NonTerm  NonTerminator (Maybe Register)
           | Term     Terminator
           | Label    Label

-- | A function has an id, a return type, a list of arguments and a
-- block of intructions.
data Function = Fun { idF    :: Id
                    , tyF    :: Ty
                    , argsF  :: [(Id,Ty)]
                    , instr  :: [IBlock] }

instance Show Function where
  show (Fun id ty args blocks) = unlines $ [header] ++ map show blocks ++ ["}"]
        where
          header = concat ["define " ,show ty ," @",id
                          ,"(" , intercalate "," (map showArg args)
                          ,")" ," {" ]
          showArg (id, t) = show t ++ " %" ++ id

-- | A block of instructions starts with a label followed by a 
-- list of nonterminators and finished by a terminator.
data IBlock = IBlock { lab :: Label
                     , ins :: [(NonTerminator, Maybe Register)]
                     , ter :: Terminator }


instance Show IBlock where
  show (IBlock lab ins ter) = unlines [ show lab ++ ":"
                                      , unlines $ map ((indent++) . showNonT) ins
                                      , indent ++  show ter
                                      ]
    where
      indent :: String
      indent = "  "
      showNonT (nonterm, reg) = maybe "" ((++ " = ") . show) reg ++ show nonterm

-- | An accumulator is an optional tuple (label, list of non-terminators). 
type Accum = Maybe (Label, [(NonTerminator, Maybe Register)])
  
-- | Adds a label to a block.
addLabel :: Label -> ([IBlock], Accum) -> ([IBlock], Accum)
addLabel label (block, Nothing) = (block, Just (label,[]))

-- | Adds a non terminator operator to a block.
addNonTerm :: (NonTerminator, Maybe Register) -> ([IBlock], Accum) -> ([IBlock], Accum)
addNonTerm _       (block, Nothing) = (block, Nothing)
addNonTerm nonterm (block, Just (lab, instr)) = (block, Just (lab, instr ++ [nonterm]))

-- | Adds a terminator operator to a block.
addTerm :: Terminator -> ([IBlock], Accum) -> ([IBlock], Accum)
addTerm _    (block, Nothing)               = (block, Nothing)
addTerm term (block, Just (lab, nonterm)) = (block ++ [IBlock lab nonterm term], Nothing)
                                            
-- | Builds a functions from its components.
mkFun :: Id -> Ty -> [(Id,Ty)] -> [Instr] -> Function
mkFun id ty args instr = Fun id ty args (go instr ([], Just (SLab "entry", [])))
  where
    go [] (blocks, Nothing)            = blocks
    go [] (blocks, Just (label, instr)) = blocks ++ [IBlock label instr Unreachable]
    go (i:is) acc                     =
      case i of
        Label lab             -> go is (addLabel lab acc)
        NonTerm nonterm reg   -> go is (addNonTerm (nonterm,reg) acc)
        Term term             -> go is (addTerm term acc)


data TopLevel = FunDecl  Ty Id [Ty]
              | TypeDecl Id [Ty]
              | GlobalDecl Ty Id [(Ty, Operand)]

instance Show TopLevel where
  show (FunDecl retType name argTypes) =
    concat [ "declare "
           , show retType
           , " @"
           , name
           , "("
           , intercalate "," . map show $ argTypes
           , ")" ]
  show (TypeDecl name typeList) =
    concat [ "%"
           , name
           , " = type {"
           , intercalate "," . map show $ typeList
           , "}" ]
  show (GlobalDecl ty name fields) =
    concat [ "@"
           , name
           , " = global "
           , show ty
           , " { "
           , intercalate "," $ map (\(t, name) -> show t ++ " " ++ show name) fields
           , " }" ]
  
