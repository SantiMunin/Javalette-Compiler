module Types where

import Javalette.Abs
import Data.Map

type Pointer = Map Ident Ident
type Structs = Map Ident Type
