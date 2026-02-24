module Task

export
data Task : Type where
  MkTask : Nat -> Task

public export total
mkTask : Nat -> Task
mkTask = MkTask
