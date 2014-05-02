module Internal.Types where

import Javalette.Abs
import Data.Map

type Structs = Map Ident [SField]

-- Class name - supertypes - attributes - methods
type Classes = Map Ident ([Ident], [SField], [FnDef])
