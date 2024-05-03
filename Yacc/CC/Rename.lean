namespace CC

def Rename (n n' : Nat) : Type :=
  Fin n -> Fin n'

def Rename.ext (f : Rename n n') : Rename n.succ n'.succ := by
  intro i
  cases i using Fin.cases
  case zero => exact 0
  case succ i0 => apply Fin.succ; exact f i0

def Rename.weaken {n : Nat} : Rename n n.succ :=
  fun i => Fin.succ i

def Rename.open (x : Fin n) : Rename n.succ n := by
  intro i
  cases i using Fin.cases
  case zero => exact x
  case succ i => exact i

end CC
