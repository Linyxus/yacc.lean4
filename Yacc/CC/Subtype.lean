import Yacc.CC.Subcapt

namespace CC

inductive SubtypeP : Ctx n m -> PType n m -> PType n m -> Prop where
| refl :
  SubtypeP Γ S S
| trans :
  SubtypeP Γ S1 S2 ->
  SubtypeP Γ S2 S3 ->
  SubtypeP Γ S1 S3
| tvar :
  BoundTVar Γ X S ->
  SubtypeP Γ (PType.tvar X) S
| top :
  SubtypeP Γ S PType.top
| func :
  SubtypeP Γ S2 S1 ->
  Subcapt Γ C2 C1 ->
  SubtypeP (Ctx.cons_var Γ (CType.capt S2 C2)) R1 R2 ->
  Subcapt (Ctx.cons_var Γ (CType.capt S2 C2)) D1 D2 ->
  SubtypeP Γ (PType.arr S1 C1 R1 D1) (PType.arr S2 C2 R2 D2)
| tfunc :
  SubtypeP Γ S2 S1 ->
  SubtypeP (Ctx.cons_tvar Γ S2) R2 R1 ->
  Subcapt (Ctx.cons_tvar Γ S2) C2 C1 ->
  SubtypeP Γ (PType.tarr S1 R1 C1) (PType.tarr S2 R2 C2)
| boxed :
  SubtypeP Γ S1 S2 ->
  Subcapt Γ C1 C2 ->
  SubtypeP Γ (PType.boxed S1 C1) (PType.boxed S2 C2)

inductive Subtype : Ctx n m -> CType n m -> CType n m -> Prop where
| capt :
  SubtypeP Γ S1 S2 ->
  Subcapt Γ C1 C2 ->
  Subtype Γ (CType.capt S1 C1) (CType.capt S2 C2)

end CC
