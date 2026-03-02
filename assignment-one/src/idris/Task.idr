module Task

export
data Task : Type where
  MkTask : Nat -> Task

export
Eq Task where
  (MkTask a) == (MkTask b) = a == b

-- List of (Task, Dependencies)
public export
Graph : Type
Graph = List (Task, List Task)

public export total
mkTask : Nat -> Task
mkTask = MkTask

public export total
deps : Graph -> Task -> List Task
deps [] _ = []
deps ((task, ds) :: xs) needle = if task == needle then ds else deps xs needle
