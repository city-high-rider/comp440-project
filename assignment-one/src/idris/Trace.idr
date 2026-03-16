module Trace

import All
import Data.List
import Elem
import Subset
import Task
import State

%default total

data Step : State ts a -> State ts b -> Type where
  Complete : (current : State ts (Just t)) -> Step current (complete current)

