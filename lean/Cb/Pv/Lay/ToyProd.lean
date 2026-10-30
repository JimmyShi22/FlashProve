-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/ToyProd.lean: the product layer's knowledge soundness (Cb/Pv/Lay/Prod.lean) is not hollow
in two ways: a small closed value of its parameters, over any finite field.

A statement "from joint A to joint B" says nothing if A follows from what rides along, or if A has
no member. Here the parameters are filled: two variables, bound in the order that swaps them; eight
cells, four for each of the two maps; one incoming mask; the point (0, 0), so that the claim reads
    cell (false, 0) * cell (true, 0) + mask = 2.
What rides along is a written list of four equations: on the mask and on three cells, among them the
other factor. The cell that is turned below is in none of them.

Main names:
  `toy`: the parameters. `good`, `bad`: two tuples of entries; they differ in the one cell (false,
    0).
  `toy_sg`: what the input claim says at the toy.
  `toy_member`: at `good` the joint before the block holds, in its exact form.
  `toy_tooth`: at `bad` what rides along holds, all of it, and the joint before the block fails, in
    its relaxed form: so the input claim does not follow from what rides along.
  `toy_know`: the block's knowledge soundness at the toy, for any short sumcheck.

Limits: two more ways of being hollow stay open here. `toy_know` is for any short sumcheck V, so
also for one whose verifier refuses everything; and nothing here shows that the joint behind the
block has a member at an output of a verifier. `toy_member` is stated of the exact relation, which
knowledge soundness does not read; at the toy the relaxed one is the same formula (`toy_memberR`).
The base relation is "true"; the toy says nothing on packing or on a configuration.

-/
import Cb.Pv.Lay.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.Toy
open Iop Prob Cb IOR Finset TWhole

noncomputable section

variable (E : Type) [Field E] [Fintype E]

/-- the names: eight cells; the incoming mask; the block's own masks -/
abbrev JT : Type :=
  (Bool × Fin 4) ⊕ (Unit ⊕ (PIdx (ldPartFmt E 2 (fun _ => 2) ++ [pDummy E 2]) ⊕ Bool))

/-- a cell, read off the entries -/
def cell (m : JT E → E) (b : Bool) (X : ℕ) : E := if h : X < 4 then m (.inl (b, ⟨X, h⟩)) else 0

open Classical in
/-- The parameters. -/
@[reducible] def toy : ProdL E where
  J := JT E
  k := 2
  e := Equiv.swap 0 1
  St := Unit
  vm := fun _ m b X => cell E m b X
  pnt := fun _ => Alg.corner fun _ => false
  inc := fun _ j => if j = .inr (.inl ()) then 1 else 0
  tg := fun _ => 2
  wAt := fun i => .inr (.inr (.inl i))
  cAt := fun b => .inr (.inr (.inr b))
  Rd := fun _ m => m (.inr (.inl ())) = 1 ∧ m (.inl (true, 0)) = 1 ∧ m (.inl (false, 1)) = 1 ∧
    m (.inl (true, 1)) = 1

/-- all entries 1 -/
def good : JT E → E := fun _ => 1

open Classical in
/-- the cell (false, 0) turned to 2 -/
def bad : JT E → E := fun j => if j = .inl (false, 0) then 2 else 1

theorem bad_ne (j : JT E) (h : j ≠ .inl (false, 0)) : bad E j = 1 := if_neg h

theorem toy_sg (m : JT E → E) :
    (toy E).Sg () m ↔ m (.inl (false, 0)) * m (.inl (true, 0)) + m (.inr (.inl ())) = 2 := by
  classical
  unfold ProdL.Sg
  have h1 : Blocks.ext (toy E).k (fun X => (toy E).vm () m false X * (toy E).vm () m true X)
      (Blocks.nat ((toy E).pnt ())) = m (.inl (false, 0)) * m (.inl (true, 0)) := by
    show Blocks.ext 2 (fun X => cell E m false X * cell E m true X)
      (Blocks.nat (Alg.corner fun _ : Fin 2 => false)) = _
    rw [ext_corner]
    have h0 : Alg.num (fun _ : Fin 2 => false) = 0 := by decide
    rw [h0]
    rfl
  have h2 : ∑ j, (toy E).inc () j * m j = m (.inr (.inl ())) := by
    show ∑ j : JT E, (if j = .inr (.inl ()) then (1 : E) else 0) * m j = _
    rw [Finset.sum_eq_single (.inr (.inl ()))]
    · rw [if_pos rfl, one_mul]
    · intro j _ hj
      rw [if_neg hj, zero_mul]
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  rw [h1, h2]

variable (Ex : ExtSpec)

/-- the base: nothing is asked -/
@[reducible] def R0 : Rels Unit Unit Ex ((JT E → E) × Unit) :=
  ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩

theorem toy_member (y : Ex.Str) :
    ((toy E).relIn (R0 E Ex) id).rel () y (good E, ()) :=
  ⟨⟨trivial, rfl, rfl, rfl, rfl⟩, (toy_sg E (good E)).2 (by
    show (1 : E) * 1 + 1 = 2
    norm_num)⟩

/-- the same of the relaxed relation -/
theorem toy_memberR (y : Ex.Str) :
    ((toy E).relIn (R0 E Ex) id).relR ((), y) (good E, ()) :=
  toy_member E Ex y

theorem toy_tooth (y : Ex.Str) :
    ((toy E).A0 (R0 E Ex) id).relR ((), y) (bad E, ()) ∧
      ¬ ((toy E).relIn (R0 E Ex) id).relR ((), y) (bad E, ()) := by
  classical
  refine ⟨⟨trivial, ?_, ?_, ?_, ?_⟩, fun h => ?_⟩
  · exact bad_ne E (.inr (.inl ())) (by simp)
  · exact bad_ne E (.inl (true, 0)) (by simp)
  · exact bad_ne E (.inl (false, 1)) (by simp)
  · exact bad_ne E (.inl (true, 1)) (by simp)
  · have h1 := (toy_sg E (bad E)).1 h.2
    have e1 : bad E (.inl (false, 0)) = 2 := if_pos rfl
    have e2 : bad E (.inl (true, 0)) = 1 := bad_ne E _ (by simp)
    have e3 : bad E (.inr (.inl ())) = 1 := bad_ne E _ (by simp)
    rw [e1, e2, e3] at h1
    have h2 : (1 : E) = 0 := by linear_combination h1
    exact one_ne_zero h2

theorem toy_know (V : ShortK (toy E).T.par Ex) :
    KnowAt ((toy E).blk V) ((toy E).relIn (R0 E Ex) id) ((toy E).relOut (R0 E Ex) id)
      (fun _ _ _ wp => wp) ((toy E).eps (Kc := Unit) V) :=
  (toy E).knowAt (R0 E Ex) id V

end
end Cb.Pv.Lay.Toy

#print axioms Cb.Pv.Lay.Toy.toy_member
#print axioms Cb.Pv.Lay.Toy.toy_tooth
#print axioms Cb.Pv.Lay.Toy.toy_know
