import Yacc.CC.Type

namespace CC

inductive Term : Nat -> Nat -> Type where
| var : Fin n -> Term n m
| abs : CType n m -> Term (n+1) m -> Term n m
| tabs : PType n m -> Term n (m+1) -> Term n m
| box : Fin n -> Term n m
| app : Fin n -> Fin n -> Term n m
| tapp : Fin n -> PType n m -> Term n m
| letin : Term n m -> Term (n+1) m -> Term n m
| unbox : CaptureSet n -> Fin n -> Term n m

def Term.rename : Term n m -> Rename n n' -> Term n' m
| Term.var x, f => Term.var (f x)
| Term.abs T t, f => Term.abs (T.rename f) (t.rename f.ext)
| Term.tabs S t, f => Term.tabs (S.rename f) (t.rename f)
| Term.box x, f => Term.box (f x)
| Term.app x y, f => Term.app (f x) (f y)
| Term.tapp x T, f => Term.tapp (f x) (T.rename f)
| Term.letin t u, f => Term.letin (t.rename f) (u.rename f.ext)
| Term.unbox C x, f => Term.unbox (C.rename f) (f x)

def Term.trename : Term n m -> Rename m m' -> Term n m'
| Term.var x, _ => Term.var x
| Term.abs T t, f => Term.abs (T.trename f) (t.trename f)
| Term.tabs S t, f => Term.tabs (S.trename f) (t.trename f.ext)
| Term.box x, _ => Term.box x
| Term.app x y, _ => Term.app x y
| Term.tapp x T, f => Term.tapp x (T.trename f)
| Term.letin t u, f => Term.letin (t.trename f) (u.trename f)
| Term.unbox C x, _ => Term.unbox C x

def Term.open_var (t : Term (n+1) m) (x : Fin n) : Term n m :=
  t.rename (Rename.open x)

def Term.rename_tvar (t : Term n (m+1)) (X : Fin m) : Term n m :=
  t.trename (Rename.open X)

def Term.weaken (t : Term n m) : Term (n+1) m :=
  t.rename Rename.weaken

def Term.weaken1 (t : Term (n+1) m) : Term (n+2) m :=
  t.rename Rename.weaken.ext

def Term.tweaken (t : Term n m) : Term n (m+1) :=
  t.trename Rename.weaken

inductive Term.IsVal : Term n m -> Prop where
| abs : Term.IsVal (Term.abs T t)
| tabs : Term.IsVal (Term.tabs S t)
| box : Term.IsVal (Term.box x)

def Term.is_value : Term n m -> Bool
| Term.abs _ _ => true
| Term.tabs _ _ => true
| Term.box _ => true
| _ => false

end CC
