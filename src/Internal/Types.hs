module Internal.Types where

import Javalette.Abs
import Data.Map

type Structs = Map Ident [SField]

type Classes = Map Ident ClassInfo

data ClassInfo = ClassInfo 
               { superT        :: [Ident]
               , hierarchyAttr :: [SField]
               , classAttr     :: [SField]
               , methods       :: [FnDef]
               }
