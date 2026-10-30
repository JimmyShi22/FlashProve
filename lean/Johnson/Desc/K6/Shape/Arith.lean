-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Shape/Arith.lean: the shape of a form through the signs in which the output head's
texts write their forms.

What it is not. No law on a value, a coefficient or a constant: a shape holds none. Nothing on any
property of the protocol. It stands on Johnson/Desc/First/Shape/Parts.lean.

A form's shape (AffSh, affSh: Parts.lean) is the list of the entries and the list of the slots that
the form names, in the order in which they were written. All arithmetic of forms is Aff.addMul
(OnBytes/Model/Hide.lean), which lays every term of its second form behind the first one's and
tests no coefficient: Parts.lean has that law (affSh_addMul, affSh_add, affSh_sub). Here: the same
for each sign of Johnson/Desc/Kinds/HeadParts.lean and OnBytes/Desc/First/P6/NormRowLaw.lean.

  `noTerm`   the shape of a form that names nothing: a unit of AffSh.append (noTerm_append,
             append_noTerm; append_assoc)
  `slotSh j`   the shape of the hidden scalar under slot j
  `sumSh n f`   f 0, f 1, .., f (n - 1), one behind the other
  `catSh l`   the members of a list, one behind the other
  `affSh_*`   one law a sign

-/
import Johnson.Desc.First.Shape.Parts
import Johnson.Desc.Kinds.Norm
import OnBytes.Desc.First.P6.NormRowLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Shape
open OnBytes (E)
open OnBytes.Model (Aff)
open VerifiableInference.Desc.First.Shape (AffSh affSh affSh_addMul affSh_add affSh_sub)

local infixl:65 " ⋆ " => AffSh.append

/-- The shape of a form that names no entry and no slot. -/
def noTerm : AffSh := AffSh.mk [] []

/-- The shape of the hidden scalar under slot j. -/
def slotSh (j : Nat) : AffSh := AffSh.mk [] [j]

/-- f 0, f 1, .., f (n - 1), one behind the other. -/
def sumSh (n : Nat) (f : Nat → AffSh) : AffSh := (List.range n).foldl (fun s i => s ⋆ f i) noTerm

/-- The members of a list, one behind the other. -/
def catSh (l : List AffSh) : AffSh := l.foldl (· ⋆ ·) noTerm

theorem noTerm_append (a : AffSh) : noTerm ⋆ a = a := by
  obtain ⟨e, s⟩ := a
  rfl

theorem append_noTerm (a : AffSh) : a ⋆ noTerm = a := by
  obtain ⟨e, s⟩ := a
  show (e ++ [], s ++ []) = (e, s)
  rw [List.append_nil, List.append_nil]

theorem append_assoc (a b c : AffSh) : a ⋆ b ⋆ c = a ⋆ (b ⋆ c) := by
  obtain ⟨e1, s1⟩ := a
  obtain ⟨e2, s2⟩ := b
  obtain ⟨e3, s3⟩ := c
  show ((e1 ++ e2) ++ e3, (s1 ++ s2) ++ s3) = (e1 ++ (e2 ++ e3), s1 ++ (s2 ++ s3))
  rw [List.append_assoc, List.append_assoc]

theorem affSh_empty : affSh ({} : Aff) = noTerm := by
  rfl

theorem affSh_const (v : E) : affSh (Aff.ofConst v) = noTerm := by
  rfl

theorem affSh_slot (j : Nat) : affSh (Aff.slot j) = slotSh j := by
  rfl

theorem affSh_scale (f : Aff) (k : E) : affSh (Aff.scale f k) = affSh f := by
  show affSh (Aff.addMul {} f k) = affSh f
  rw [affSh_addMul, affSh_empty, noTerm_append]

theorem affSh_smulE (k : E) (f : Form) : affSh (k • f) = affSh f := by
  exact affSh_scale f k

theorem affSh_smulN (n : Nat) (f : Form) : affSh (n • f) = affSh f := by
  exact affSh_scale f (natE n)

theorem affSh_addE (f : Form) (x : E) :
    affSh (HAdd.hAdd (α := Form) (β := E) (γ := Form) f x) = affSh f := by
  show affSh (f + Aff.ofConst x) = affSh f
  rw [affSh_add, affSh_const, append_noTerm]

theorem affSh_Eadd (x : E) (f : Form) :
    affSh (HAdd.hAdd (α := E) (β := Form) (γ := Form) x f) = affSh f := by
  show affSh (Aff.ofConst x + f) = affSh f
  rw [affSh_add, affSh_const, noTerm_append]

theorem affSh_subE (f : Form) (x : E) :
    affSh (HSub.hSub (α := Form) (β := E) (γ := Form) f x) = affSh f := by
  show affSh (f - Aff.ofConst x) = affSh f
  rw [affSh_sub, affSh_const, append_noTerm]

theorem affSh_addN (f : Form) (n : Nat) :
    affSh (HAdd.hAdd (α := Form) (β := Nat) (γ := Form) f n) = affSh f := by
  show affSh (f + Aff.ofConst (natE n)) = affSh f
  rw [affSh_add, affSh_const, append_noTerm]

theorem affSh_subN (f : Form) (n : Nat) :
    affSh (HSub.hSub (α := Form) (β := Nat) (γ := Form) f n) = affSh f := by
  show affSh (f - Aff.ofConst (natE n)) = affSh f
  rw [affSh_sub, affSh_const, append_noTerm]

theorem affSh_natCast (n : Nat) : affSh ((n : Nat) : Form) = noTerm := by
  rfl

theorem affSh_sumTo (n : Nat) (f : Nat → Form) :
    affSh (sumTo n f) = sumSh n fun i => affSh (f i) := by
  unfold sumTo sumSh
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [affSh_add, ih]

theorem affSh_sumTo6 (n : Nat) (f : Nat → Form) :
    affSh (OnBytes.Desc.First.P6.sumTo n f) = sumSh n fun i => affSh (f i) := by
  unfold OnBytes.Desc.First.P6.sumTo sumSh
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [affSh_add, ih]

theorem affSh_sm (k : Nat) (f : Form) : affSh (OnBytes.Desc.First.P6.sm k f) = affSh f := by
  exact affSh_scale f _

theorem affSh_nat (n : Nat) : affSh (OnBytes.Desc.First.P6.nat n) = noTerm := by
  rfl

/-- A fold that adds forms, from a form on. -/
theorem affSh_foldl_add (l : List Form) (a : Form) :
    affSh (l.foldl (· + ·) a) = (l.map affSh).foldl (· ⋆ ·) (affSh a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, affSh_add]

end VerifiableInference.Desc.Kinds.Head.Shape

#print axioms VerifiableInference.Desc.Kinds.Head.Shape.noTerm_append
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.append_noTerm
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.append_assoc
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_empty
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_const
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_slot
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_scale
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_smulE
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_smulN
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_addE
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_Eadd
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_subE
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_addN
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_subN
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_natCast
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_sumTo
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_sumTo6
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_sm
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_nat
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.affSh_foldl_add
