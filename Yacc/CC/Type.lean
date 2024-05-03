import Yacc.CC.CaptureSet
import Yacc.CC.Rename

namespace CC

inductive PType : Nat -> Nat -> Type where
| tvar : Fin m -> PType n m
| top : PType n m
| arr
  (Sarg : PType n m)
  (Carg : CaptureSet n)
  (Sres : PType n.succ m)
  (Cres : CaptureSet n.succ)
  : PType n m
| tarr
  (Sarg : PType n m)
  (Sres : PType n m.succ)
  (Cres : CaptureSet n)
  : PType n m
| boxed
  (S : PType n m)
  (C : CaptureSet n)
  : PType n m

inductive CType : Nat -> Nat -> Type where
| capt
  (S : PType n m)
  (C : CaptureSet n)
  : CType n m

def PType.rename : PType n m -> Rename n n' -> PType n' m
| PType.tvar x, _ => PType.tvar x
| PType.top, _ => PType.top
| PType.arr Sarg Carg Sres Cres, ρ =>
  PType.arr (Sarg.rename ρ) (Carg.rename ρ) (Sres.rename ρ.ext) (Cres.rename ρ.ext)
| PType.tarr Sarg Sres Cres, ρ =>
  PType.tarr (Sarg.rename ρ) (Sres.rename ρ) (Cres.rename ρ)
| PType.boxed S C, ρ =>
  PType.boxed (S.rename ρ) (C.rename ρ)

def PType.trename : PType n m -> Rename m m' -> PType n m'
| PType.tvar x, ρ => PType.tvar (ρ x)
| PType.top, _ => PType.top
| PType.arr Sarg Carg Sres Cres, ρ =>
  PType.arr (Sarg.trename ρ) Carg (Sres.trename ρ) Cres
| PType.tarr Sarg Sres Cres, ρ =>
  PType.tarr (Sarg.trename ρ) (Sres.trename ρ.ext) Cres
| PType.boxed S C, ρ =>
  PType.boxed (S.trename ρ) C

def CType.rename : CType n m -> Rename n n' -> CType n' m
| CType.capt S C, ρ => CType.capt (S.rename ρ) (C.rename ρ)

def CType.trename : CType n m -> Rename m m' -> CType n m'
| CType.capt S C, ρ => CType.capt (S.trename ρ) C

def PType.weaken (S : PType n m) : PType n.succ m :=
  S.rename Rename.weaken

def PType.tweaken (S : PType n m) : PType n m.succ :=
  S.trename Rename.weaken

def CType.weaken (T : CType n m) : CType n.succ m :=
  T.rename Rename.weaken

def CType.tweaken (T : CType n m) : CType n m.succ :=
  T.trename Rename.weaken

def CType.open_var (T : CType (n+1) m) (x : Fin n) : CType n m :=
  T.rename (Rename.open x)

def CType.open_tvar (T : CType n (m+1)) (x : Fin m) : CType n m :=
  T.trename (Rename.open x)

end CC
