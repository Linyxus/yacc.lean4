import Std.Data.Fin.Basic
import Aesop
import Yacc.CC.Rename

namespace CC

/-!

# Capture Sets

!-/

inductive BitSet : Nat -> Type where
| empty : BitSet 0
| cons : Bool -> BitSet n -> BitSet (n+1)

structure CaptureSet (n : Nat) : Type where
  elems : BitSet n
  cap : Bool

/-!

## Membership

!-/

@[aesop safe [constructors, cases]]
inductive BitSet.HasElem : BitSet n -> Fin n -> Prop where
| here :
  BitSet.HasElem (BitSet.cons true bs) 0
| there :
  BitSet.HasElem bs i →
  BitSet.HasElem (BitSet.cons b bs) (Fin.succ i)

@[simp]
instance : Membership (Fin n) (BitSet n) :=
  ⟨fun a s => BitSet.HasElem s a⟩

def CaptureSet.HasElem (C : CaptureSet n) (i : Fin n) : Prop :=
  i ∈ C.elems

@[simp]
instance : Membership (Fin n) (CaptureSet n) :=
  ⟨fun a s => CaptureSet.HasElem s a⟩

def CaptureSet.HasCap (C : CaptureSet n) : Prop :=
  C.cap

/-!

## Lookup

!-/

def BitSet.lookup : BitSet n -> Fin n -> Bool
| BitSet.empty, _ => false
| BitSet.cons b _, ⟨Nat.zero, h⟩ => b
| BitSet.cons _ bs, ⟨Nat.succ i0, h⟩ =>
  BitSet.lookup bs ⟨i0, Nat.lt_of_succ_lt_succ h⟩

theorem BitSet.lookup_to_has_elem {bs : BitSet n} :
  (h : bs.lookup i = true) ->
  i ∈ bs := by
  intro h
  induction bs
  case empty => cases h
  case cons b bs ih =>
    cases i using Fin.cases
    case zero =>
      simp [lookup] at h
      subst h
      constructor
    case succ =>
      simp [lookup] at h
      apply BitSet.HasElem.there
      apply ih h

theorem BitSet.has_elem_to_lookup {bs : BitSet n}
  (h : i ∈ bs) : bs.lookup i = true := by
  induction h
  case here => rfl
  case there h ih =>
    simp [BitSet.lookup]
    apply ih

/-!

## Empty sets

!-/

def BitSet.emptySet : {n : Nat} -> BitSet n
| 0 => BitSet.empty
| n+1 => BitSet.cons false (BitSet.emptySet (n := n))

@[simp]
instance : EmptyCollection (BitSet n) :=
  ⟨BitSet.emptySet⟩

def CaptureSet.emptySet {n : Nat} : CaptureSet n :=
  { elems := {}, cap := false }

@[simp]
instance : EmptyCollection (CaptureSet n) :=
  ⟨CaptureSet.emptySet⟩

/-!

Singleton

!-/

def BitSet.addElem : BitSet n -> Fin n -> BitSet n
| BitSet.empty, _ => BitSet.empty
| BitSet.cons _ bs, ⟨Nat.zero, h⟩ => BitSet.cons true bs
| BitSet.cons b bs, ⟨Nat.succ i0, h⟩ =>
  BitSet.cons b (BitSet.addElem bs ⟨i0, Nat.lt_of_succ_lt_succ h⟩)

def BitSet.singleton (i : Fin n) : BitSet n :=
  BitSet.addElem {} i

@[simp]
instance : Singleton (Fin n) (BitSet n) :=
  ⟨BitSet.singleton⟩

theorem BitSet.add_elem_has_elem {bs : BitSet n} :
  i ∈ bs.addElem i := by
  induction bs
  case empty => apply Fin.elim0 i
  case cons b bs ih =>
    cases i using Fin.cases
    case zero =>
      constructor
    case succ =>
      apply BitSet.HasElem.there
      apply ih

theorem BitSet.singleton_has_elem {i : Fin n} :
  i ∈ ({i} : BitSet n) := BitSet.add_elem_has_elem

def CaptureSet.singleton (i : Fin n) : CaptureSet n :=
  { elems := {i}, cap := false }

@[simp]
instance : Singleton (Fin n) (CaptureSet n) :=
  ⟨CaptureSet.singleton⟩

theorem CaptureSet.singleton_has_elem {i : Fin n} :
  i ∈ ({i} : CaptureSet n) := BitSet.singleton_has_elem

def CaptureSet.singleton_cap : CaptureSet n :=
  { elems := {}, cap := true }

/-!

## Union

!-/

def BitSet.union : BitSet n -> BitSet n -> BitSet n
| BitSet.empty, BitSet.empty => BitSet.empty
| BitSet.cons b1 bs1, BitSet.cons b2 bs2 =>
  BitSet.cons (b1 || b2) (BitSet.union bs1 bs2)

@[simp]
instance : Union (BitSet n) :=
  ⟨BitSet.union⟩

theorem BitSet.in_union_elim {bs1 bs2 : BitSet n} :
  i ∈ bs1 ∪ bs2 -> i ∈ bs1 ∨ i ∈ bs2 := by
  intro h
  induction bs1
  case empty =>
    cases bs2; simp [BitSet.union] at h
    cases h
  case cons b1 bs1 ih1 =>
    simp at h
    cases bs2
    case cons b2 bs2 =>
      simp [union] at h
      cases b1 <;> cases b2 <;> cases h <;>
        try (solve | left; constructor | right; constructor)
      all_goals (rename_i h; have ih1 := ih1 h; cases ih1 <;> aesop)

theorem BitSet.union_comm (bs1 bs2 : BitSet n) :
  bs1 ∪ bs2 = bs2 ∪ bs1 := by
  induction bs1
  case empty => cases bs2; simp [BitSet.union]
  case cons b1 bs1 ih1 =>
    cases bs2 with
    | cons b2 bs2 =>
      simp [BitSet.union]
      simp [Bool.or_comm]
      aesop

theorem BitSet.cons_has_elem_succ_inv' {bs : BitSet n} {i : Fin n}
  (h : BitSet.HasElem (BitSet.cons b bs) i')
  (he : i' = Fin.succ i) :
  BitSet.HasElem bs i := by
  cases h
  cases he
  rw [Fin.succ_inj] at he
  subst he; assumption

theorem BitSet.cons_has_elem_succ_inv {bs : BitSet n} {i : Fin n}
  (h : BitSet.HasElem (BitSet.cons b bs) (Fin.succ i)) :
  BitSet.HasElem bs i := by
  apply BitSet.cons_has_elem_succ_inv' h rfl

theorem BitSet.in_union_intro_left {bs1 bs2 : BitSet n} :
  i ∈ bs1 -> i ∈ bs1 ∪ bs2 := by
  intro h
  induction bs1
  case empty => cases h
  case cons b1 bs1 ih1 =>
    simp [union]
    cases bs2; rename_i b2 bs2
    cases i using Fin.cases
    case zero =>
      cases h; simp [union]; constructor
    case succ =>
      simp [union]; apply BitSet.HasElem.there
      have h' := BitSet.cons_has_elem_succ_inv h
      apply ih1 h'

theorem BitSet.in_union_intro_right {bs1 bs2 : BitSet n} :
  i ∈ bs2 -> i ∈ bs1 ∪ bs2 := by
  intros h
  rw [BitSet.union_comm]
  apply BitSet.in_union_intro_left h

theorem BitSet.in_union_intro {bs1 bs2 : BitSet n} :
  i ∈ bs1 ∨ i ∈ bs2 -> i ∈ bs1 ∪ bs2 := by
  intro h
  cases h
  case inl h => apply BitSet.in_union_intro_left h
  case inr h => apply BitSet.in_union_intro_right h

def BitSet.union_list : List (BitSet n) -> BitSet n
| [] => {}
| bs :: bss => bs ∪ union_list bss

def CaptureSet.union (C1 C2 : CaptureSet n) : CaptureSet n :=
  { elems := C1.elems ∪ C2.elems, cap := C1.cap || C2.cap }

instance : Union (CaptureSet n) :=
  ⟨CaptureSet.union⟩

/-!

## Renaming

!-/

def BitSet.rename_i (bs : BitSet n) (i : Fin n) (f : Fin n -> Fin n') : BitSet n' :=
  match bs.lookup i with
  | true => BitSet.singleton (f i)
  | false => {}

def BitSet.rename (bs : BitSet n) (f : Fin n -> Fin n') : BitSet n' :=
  BitSet.union_list ((Fin.list n).map (fun i => bs.rename_i i f))

def CaptureSet.rename (C : CaptureSet n) (f : Fin n -> Fin n') : CaptureSet n' :=
  { elems := C.elems.rename f, cap := C.cap }

def CaptureSet.inject (C : CaptureSet (n+1)) : CaptureSet n :=
  match C with
  | {elems := (BitSet.cons _ bs), cap := c} => {elems := bs, cap := c}

end CC
