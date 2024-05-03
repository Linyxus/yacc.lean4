import Yacc.CC.Type

namespace CC

inductive Ctx : Nat -> Nat -> Type where
| empty : Ctx 0 0
| cons_var : Ctx n m -> CType n m -> Ctx (n+1) m
| cons_tvar : Ctx n m -> PType n m -> Ctx n (m+1)

inductive BoundVar : Ctx n m -> Fin n -> CType n m -> Type where
| here :
  BoundVar (Ctx.cons_var Γ T) 0 T.weaken
| there_tvar :
  BoundVar Γ x T ->
  BoundVar (Ctx.cons_tvar Γ P) x T.tweaken
| there_var :
  BoundVar Γ x T ->
  BoundVar (Ctx.cons_var Γ T') x.succ T.weaken

inductive BoundTVar : Ctx n m -> Fin m -> PType n m -> Type where
| here :
  BoundTVar (Ctx.cons_tvar Γ P) 0 P.tweaken
| there_tvar :
  BoundTVar Γ x P ->
  BoundTVar (Ctx.cons_tvar Γ P') x.succ P.tweaken
| there_var :
  BoundTVar Γ x P ->
  BoundTVar (Ctx.cons_var Γ T) x P.weaken

end CC
