-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/RidesSorts.lean: which items pass over a code switch (the kind K2). By Lean's kernel,
at each of the 25 written places: every item that is open there and that the row neither shuts nor
owes is unmarked, pinW, pile, pinI or a part of parts4 of a segment's relation; and at number 339
alone, the part lookCallsHeard.

  k2ItemSort          the test on one item at one number
  k2_open_sorts       the kernel's answer at the 25 places
  k2_open_sorts_bites, k2_open_heard_bites   controls: with pile struck from the test, or with
                      lookCallsHeard struck from it, the answer turns
  k2_head_link        number 339 stands in segment 24
  k2_open_cases       the same at one place and one item

Limits. Closed facts on the written lists. Nothing on what any item says.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ExchangeByKind
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2.Term
open VerifiableInference.Desc.First (Item)
open ProofFile.Honest
open ProofFile.Honest.K2 (SwitchPlace)
open ProofFile.Honest.K2.Law (placesW switchNo)

/-- True of the sorts of item that pass over the code switch at number b. -/
def k2ItemSort (b : Nat) : Item → Bool
  | .unmarked | .pinW | .pile | .pinI => true
  | .constr _ q => P5J.parts4.contains q || (b == 339 && q == .lookCallsHeard)
  | _ => false

set_option maxRecDepth 1000000 in
/-- **At each written place every open item that the row neither shuts nor owes is of these
sorts.** -/
theorem k2_open_sorts : (placesW.all fun p =>
    (fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (switchNo p)).all fun i =>
      (FirstRows.rows P5J.At.links P5J.At.ps (switchNo p)).shuts.contains i ||
        (FirstRows.rows P5J.At.links P5J.At.ps (switchNo p)).owes.contains i ||
        k2ItemSort (switchNo p) i) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with pile struck from the test the answer turns. -/
theorem k2_open_sorts_bites : (placesW.all fun p =>
    (fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (switchNo p)).all fun i =>
      (FirstRows.rows P5J.At.links P5J.At.ps (switchNo p)).shuts.contains i ||
        (FirstRows.rows P5J.At.links P5J.At.ps (switchNo p)).owes.contains i ||
        (k2ItemSort (switchNo p) i && i != Item.pile)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at no number the part lookCallsHeard, and the answer turns. -/
theorem k2_open_heard_bites : (placesW.all fun p =>
    (fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (switchNo p)).all fun i =>
      (FirstRows.rows P5J.At.links P5J.At.ps (switchNo p)).shuts.contains i ||
        (FirstRows.rows P5J.At.links P5J.At.ps (switchNo p)).owes.contains i ||
        k2ItemSort 0 i) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Number 339 stands in segment 24. -/
theorem k2_head_link : (P5J.At.ps[339]?).map (·.link) = some (some 24) := by
  decide +kernel

/-- **At one place and one item.** -/
theorem k2_open_cases {p : SwitchPlace} (hp : p ∈ placesW) {i : Item}
    (h1 : i ∈ fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (switchNo p))
    (h2 : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (switchNo p)).shuts)
    (h3 : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (switchNo p)).owes) :
    i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨
      (∃ m q, q ∈ P5J.parts4 ∧ i = .constr m q) ∨
      (switchNo p = 339 ∧ ∃ m, i = .constr m .lookCallsHeard) := by
  have t := List.all_eq_true.1 (List.all_eq_true.1 k2_open_sorts p hp) i h1
  rw [Bool.or_eq_true, Bool.or_eq_true] at t
  rcases t with (t | t) | t
  · exact absurd (List.contains_iff_mem.1 t) h2
  · exact absurd (List.contains_iff_mem.1 t) h3
  · cases i with
    | unmarked => exact Or.inl rfl
    | pinW => exact Or.inr (Or.inl rfl)
    | pile => exact Or.inr (Or.inr (Or.inl rfl))
    | pinI => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | constr m q =>
      have t' : (P5J.parts4.contains q || (switchNo p == 339 && q == .lookCallsHeard)) = true := t
      rw [Bool.or_eq_true, Bool.and_eq_true] at t'
      rcases t' with c | ⟨c1, c2⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, q, List.contains_iff_mem.1 c, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨beq_iff_eq.1 c1, m, by rw [beq_iff_eq.1 c2]⟩))))
    | _ => simp [k2ItemSort] at t

end AtFullSide.K2.Term

#print axioms AtFullSide.K2.Term.k2_open_sorts
#print axioms AtFullSide.K2.Term.k2_open_sorts_bites
#print axioms AtFullSide.K2.Term.k2_open_heard_bites
#print axioms AtFullSide.K2.Term.k2_head_link
#print axioms AtFullSide.K2.Term.k2_open_cases
