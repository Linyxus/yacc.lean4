import Yacc.CC.Term
namespace CC

inductive Store : Nat -> Type where
| empty : Store 0
| cons (γ : Store n) (t : Term n 0) (hv : t.IsVal) : Store (n+1)

structure EvalConfig (n : Nat) : Type where
  γ : Store n
  t : Term n 0

end CC
