import Yacc.CC.EvalContext
import Yacc.CC.TypeSubst

namespace CC

inductive Lookup : Store n -> (Fin n) -> Term n m -> Prop where
| here :
  Lookup (Store.cons γ t hv) 0 t.weaken
| there :
  Lookup γ x t ->
  Lookup (Store.cons γ t' hv) (Fin.succ x) t.weaken

inductive Reduce : EvalConfig n -> EvalConfig n' -> Prop where
| apply :
  (hl : Lookup γ x (Term.abs T t)) ->
  Reduce
    ⟨γ, Term.app x y⟩
    ⟨γ, t.open_var y⟩
| tapply :
  (hl : Lookup γ x (Term.tabs S' t)) ->
  Reduce
    ⟨γ, Term.tapp x S⟩
    ⟨γ, t.open_tvar S⟩
| openbox :
  (hl : Lookup γ x (Term.box y)) ->
  Reduce
    ⟨γ, Term.unbox C x⟩
    ⟨γ, Term.var x⟩
| rename :
  Reduce
    ⟨γ, Term.letin (Term.var x) t⟩
    ⟨γ, t.open_var x⟩
| lift :
  (hv : v.IsVal) ->
  Reduce
    ⟨γ, Term.letin v t⟩
    ⟨Store.cons γ v hv, t⟩
| ctx :
  (hred : Reduce ⟨γ, t⟩ ⟨γ, t'⟩) ->
  Reduce
    ⟨γ, Term.letin t u⟩
    ⟨γ, Term.letin t' u⟩
| ctx1 :
  Reduce ⟨γ, t⟩ ⟨Store.cons γ v hv, t'⟩ ->
  Reduce ⟨γ, Term.letin t u⟩ ⟨Store.cons γ v hv, Term.letin t' u.weaken1⟩

end CC
