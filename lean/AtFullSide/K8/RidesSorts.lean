-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/RidesSorts.lean: which items pass over the smallness test's draw (the kind K8). By Lean's
kernel, at each of the 25 draws: every item that is open there and that the row neither shuts nor
owes is unmarked, pinW, pile, pinI, a row or the claim on the weights of the draw's segment, the
forms of a run of that segment in front of the draw, or a part of parts4 of a later segment.

  k8ItemSort        the test on one item at one segment
  k8_open_sorts     the kernel's answer at the 25 draws
  k8_open_sorts_bites, k8_open_forms_bites, k8_open_wo_bites   controls: with pile, the forms or the
                    claim on the weights struck from the test, the answer turns
  k8_open_cases     the same at one segment and one item

Limits. Closed facts on the written lists. Nothing on what any item says.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstRows
import Johnson.Desc.First.K8.TiePromise
import Johnson.P1K8R.TableAtK8
import Johnson.P5J.MeansQ
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K8.Term
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.K8 (drawAt)
open ProofFile.Honest
open P1K8T (pcOf)

/-- True of the sorts of item that pass over the draw of segment l. -/
def k8ItemSort (l : Nat) : Item → Bool
  | .unmarked | .pinW | .pile | .pinI => true
  | .row m _ => m == l
  | .wo m => m == l
  | .forms m k _ => m == l && decide (k < pcOf l)
  | .constr m q => decide (l < m) && P5J.parts4.contains q
  | _ => false

/-- An item that passes a test t at the draw of segment l, or that its row shuts or owes. -/
def k8RowTest (t : Nat → Item → Bool) (l : Nat) : Bool :=
  (fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
    (FirstRows.rows P5J.At.links P5J.At.ps) (drawAt l)).all fun i =>
    (FirstRows.rows P5J.At.links P5J.At.ps (drawAt l)).shuts.contains i ||
      (FirstRows.rows P5J.At.links P5J.At.ps (drawAt l)).owes.contains i || t l i

set_option maxRecDepth 1000000 in
/-- **At each draw every open item that the row neither shuts nor owes is of these sorts.** -/
theorem k8_open_sorts : ((List.range 25).all fun l => k8RowTest k8ItemSort l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with pile struck from the test the answer turns. -/
theorem k8_open_sorts_bites :
    ((List.range 25).all fun l =>
      k8RowTest (fun l i => k8ItemSort l i && i != Item.pile) l) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the forms struck from the test the answer turns. -/
theorem k8_open_forms_bites :
    ((List.range 25).all fun l =>
      k8RowTest (fun l i => k8ItemSort l i && !(match i with | .forms _ _ _ => true | _ => false))
        l) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the claim on the weights struck from the test the answer turns. -/
theorem k8_open_wo_bites :
    ((List.range 25).all fun l =>
      k8RowTest (fun l i => k8ItemSort l i && !(match i with | .wo _ => true | _ => false))
        l) = false := by
  decide +kernel

/-- **At one segment and one item.** -/
theorem k8_open_cases {l : Nat} (hl : l ≤ 24) {i : Item}
    (h1 : i ∈ fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (drawAt l))
    (h2 : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (drawAt l)).shuts)
    (h3 : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (drawAt l)).owes) :
    i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ (∃ c, i = .row l c) ∨ i = .wo l ∨
      (∃ k r, k < pcOf l ∧ i = .forms l k r) ∨ (∃ m q, q ∈ P5J.parts4 ∧ i = .constr m q) := by
  have t := List.all_eq_true.1
    (List.all_eq_true.1 k8_open_sorts l (List.mem_range.2 (Nat.lt_succ_of_le hl))) i h1
  rw [Bool.or_eq_true, Bool.or_eq_true] at t
  rcases t with (t | t) | t
  · exact absurd (List.contains_iff_mem.1 t) h2
  · exact absurd (List.contains_iff_mem.1 t) h3
  · cases i with
    | unmarked => exact Or.inl rfl
    | pinW => exact Or.inr (Or.inl rfl)
    | pile => exact Or.inr (Or.inr (Or.inl rfl))
    | pinI => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | row m c =>
      have e : m = l := beq_iff_eq.1 t
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, by rw [e]⟩))))
    | wo m =>
      have e : m = l := beq_iff_eq.1 t
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e]))))))
    | forms m k r =>
      have t' : (m == l && decide (k < pcOf l)) = true := t
      rw [Bool.and_eq_true] at t'
      have e : m = l := beq_iff_eq.1 t'.1
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, r, of_decide_eq_true t'.2, by rw [e]⟩))))))
    | constr m q =>
      have t' : (decide (l < m) && P5J.parts4.contains q) = true := t
      rw [Bool.and_eq_true] at t'
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨m, q, List.contains_iff_mem.1 t'.2, rfl⟩))))))
    | _ => simp [k8ItemSort] at t

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.k8_open_sorts
#print axioms AtFullSide.K8.Term.k8_open_sorts_bites
#print axioms AtFullSide.K8.Term.k8_open_forms_bites
#print axioms AtFullSide.K8.Term.k8_open_wo_bites
#print axioms AtFullSide.K8.Term.k8_open_cases
