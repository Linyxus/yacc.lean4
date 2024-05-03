import Yacc.CC.CaptureSet
import Yacc.CC.Context

namespace CC

inductive Subcapt : Ctx n m -> CaptureSet n -> CaptureSet n -> Prop where
| trans :
  Subcapt Γ C1 C2 ->
  Subcapt Γ C2 C3 ->
  Subcapt Γ C1 C3
| elem {C : CaptureSet n} :
  x ∈ C ->
  Subcapt Γ {x} C
| elem_cap {C : CaptureSet n} :
  C.HasCap ->
  Subcapt Γ CaptureSet.singleton_cap C
| union :
  Subcapt Γ C1 C3 ->
  Subcapt Γ C2 C3 ->
  Subcapt Γ (C1 ∪ C2) C3
| var :
  BoundVar Γ x (CType.capt S C) ->
  Subcapt Γ {x} C

end CC
