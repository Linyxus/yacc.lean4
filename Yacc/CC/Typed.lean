import Yacc.CC.Subtype
import Yacc.CC.TypeSubst
import Yacc.CC.Term

namespace CC

def letC : (isVal : Bool) -> (Ct : CaptureSet n) -> (Cu : CaptureSet (n+1)) -> CaptureSet n
| true, _, ⟨BitSet.cons false bs, u⟩ => ⟨bs, u⟩
| _, Ct, ⟨BitSet.cons _ bs, u⟩ => Ct ∪ ⟨bs, u⟩

inductive CaptureSet.Inject : CaptureSet (n+1) -> CaptureSet n -> Prop where
| inject :
  CaptureSet.Inject ⟨BitSet.cons false bs, u⟩ Cu

inductive PType.Inject : PType (n+1) m -> PType n m -> Prop where
| tvar :
  PType.Inject (PType.tvar S) (PType.tvar S)
| top : PType.Inject PType.top PType.top

inductive Typed : CaptureSet n -> Ctx n m -> Term n m -> CType n m -> Prop where
| var :
  BoundVar Γ x (CType.capt S C) ->
  Typed {x} Γ (Term.var x) (CType.capt S {x})
| sub :
  Typed C Γ t T ->
  Subtype Γ T U ->
  Typed C Γ t U
| abs :
  Typed ⟨BitSet.cons b bs, u⟩ (Ctx.cons_var Γ (CType.capt Sarg Carg)) t (CType.capt Sres Cres) ->
  Typed ⟨bs, u⟩ Γ (Term.abs T t) (CType.capt (PType.arr Sarg Carg Sres Cres) ⟨bs, u⟩)
| tabs :
  Typed C (Ctx.cons_tvar Γ Sarg) t (CType.capt Sres Cres) ->
  Typed C Γ (Term.tabs Sarg t) (CType.capt (PType.tarr Sarg Sres Cres) C)
| app :
  Typed Cf Γ (Term.var x) (CType.capt (PType.arr Sarg Carg Sres Cres) C) ->
  Typed Ca Γ (Term.var y) (CType.capt Sarg Carg) ->
  Typed (Cf ∪ Ca) Γ (Term.app x y) ((CType.capt Sres Cres).open_var y)
| tapp :
  Typed Cf Γ (Term.var x) (CType.capt (PType.tarr Sarg Sres Cres) C) ->
  Typed Cf Γ (Term.tapp x Sarg) ((CType.capt Sres Cres).open Sarg)
| box :
  Typed Cx Γ (Term.var x) (CType.capt S C) ->
  Typed {} Γ (Term.box x) (CType.capt (PType.boxed S C) {})
| unbox :
  Typed Cx Γ (Term.var x) (CType.capt (PType.boxed S C) C') ->
  Typed (Cx ∪ C) Γ (Term.unbox C x) (CType.capt S C)
| letin :
  Typed Ct Γ t T ->
  Typed Cu (Ctx.cons_var Γ T) u U.weaken ->
  Typed (letC t.is_value Ct Cu) Γ (Term.letin t u) U

end CC
