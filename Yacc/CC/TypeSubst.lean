import Yacc.CC.Type
import Yacc.CC.Term

namespace CC

def TypeSubst (n m m' : Nat) : Type :=
  Fin m -> PType n m'

def TypeSubst.ext (σ : TypeSubst n m m') : TypeSubst n.succ m m' :=
  fun i => (σ i).weaken

def TypeSubst.text (σ : TypeSubst n m m') : TypeSubst n m.succ m'.succ := by
  intro i
  cases i using Fin.cases
  case zero => exact PType.tvar 0
  case succ i0 => exact (σ i0).tweaken

def PType.tsubst : PType n m -> TypeSubst n m m' -> PType n m'
| PType.tvar i, σ => σ i
| PType.top, _ => PType.top
| PType.arr Sarg Carg Sres Cres, σ =>
  PType.arr (Sarg.tsubst σ) Carg (Sres.tsubst σ.ext) Cres
| PType.tarr Sarg Sres Cres, σ =>
  PType.tarr (Sarg.tsubst σ) (Sres.tsubst σ.text) Cres
| PType.boxed S C, σ => PType.boxed (S.tsubst σ) C

def CType.tsubst : CType n m -> TypeSubst n m m' -> CType n m'
| CType.capt S C, σ => CType.capt (S.tsubst σ) C

def TypeSubst.open (S : PType n m) : TypeSubst n m.succ m := by
  intro i
  cases i using Fin.cases
  case zero => exact S
  case succ i0 => exact PType.tvar i0

def PType.open (R : PType n m.succ) (S : PType n m) :=
  R.tsubst (TypeSubst.open S)

def CType.open (R : CType n m.succ) (S : PType n m) :=
  R.tsubst (TypeSubst.open S)

def Term.tsubst : Term n m -> TypeSubst n m m' -> Term n m'
| Term.var i, _ => Term.var i
| Term.abs T t, σ => Term.abs (T.tsubst σ) (t.tsubst σ.ext)
| Term.tabs S t, σ => Term.tabs (S.tsubst σ) (t.tsubst σ.text)
| Term.box i, _ => Term.box i
| Term.app i j, _ => Term.app i j
| Term.tapp i S, σ => Term.tapp i (S.tsubst σ)
| Term.letin t u, σ => Term.letin (t.tsubst σ) (u.tsubst σ.ext)
| Term.unbox C x, _ => Term.unbox C x

def Term.open_tvar (t : Term n m.succ) (S : PType n m) : Term n m :=
  t.tsubst (TypeSubst.open S)

end CC
