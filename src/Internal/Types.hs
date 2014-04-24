module Internal.Types where

import Javalette.Abs
import Data.Map

type Structs = Map Ident Type

type ObjectH = Map Ident [Ident]
