-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeNoSplit.lean: NO PLAN THAT THE PLANNER RETURNS WANTS A SPLIT'S MESSAGE IN A
REQUEST'S OWN GROUP, UP TO THE LAST CHAIN'S PARAMETERS AT THE SEAT. Statements and proofs; no
definition.

Why. The door of the last chain asks that the own group which is handed has two members. K13's text
lays one member for each message that the claim's masks name, W, and the split's message where the
shape wants one (`rows_count`, Johnson/Desc/Last/ShapeDoorItems.lean). Here the third summand is 0
wherever the shape is the planner's.

Main names (namespace `VerifiableInference.Desc.Last`).
  `exc_guard_not`: a guard that was passed: its condition failed. `noOwnSplit_of_leaves`: where the
    gate on the table's leaves is passed (`missedInTheTablesLeaves S = false`,
    OnBytes/Params/Gate.lean) W and Omega have one code.
  **`configure_noOwnSplit`**: what `configure` returns has `sized.proof.batch.shape.ownSplitNeeded =
    false`: `configure` refuses where `missedOnTheTable` says true, and that says true where the
    batch's shape wants such a split. `chainsOf_noOwnSplit`: so at the verifier's own chains.
  **`noOwnSplit_at_seat`**: `ProofFile.pureRoad.pub o pol lay KL = .ok Z` gives `(ProofFile.pAt
    Z).S.ownSplitNeeded = false` (by `ProofFile.Law.pub_chainsOf`).

Every "there is": none.
Limits. (1) It walks `configure`'s and `chainsOf`'s texts guard by guard: it falls if a guard is
moved. (2) It speaks of the batch's shape; of the key's one-time shape nothing (there:
`keyOnce_ownSplit`). (3) That K13's block at the seat is handed this shape is not said here. (4) The
seated description tests the same of its plan beside (`n6`, Johnson/Desc/OnPlan/OkBesideC.lean): not
used. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Params.ConfigureLaws
import OnBytes.Model.VerifyChains
import Johnson.Desc.Last.ShapeDoorAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Last
open OnBytes OnBytes.Params

/-- A guard that was passed: its condition did not hold, and what follows has returned the value.
The like of `opt_guard_not` (OnBytes/Params/Fit/LinParts.lean) for steps that refuse with a name;
`exc_guard` (OnBytes/Params/ConfigureLaws.lean) keeps the second half alone; a private copy stands
in OnBytes/Model/Fit/ShapeFCaps.lean. -/
theorem exc_guard_not {ε β : Type} {c : Prop} [Decidable c] {e : ε} {next : PUnit → Except ε β}
    {b : β}
    (h : (if c then (throw e : Except ε PUnit) >>= next else pure PUnit.unit >>= next) = .ok b) :
    ¬ c ∧ next PUnit.unit = .ok b := by
  split at h
  · cases h
  · exact ⟨‹_›, h⟩

/-- Where the gate on the table's leaves is passed, W and Omega have one code. -/
theorem noOwnSplit_of_leaves {S : LinShape} (h : missedInTheTablesLeaves S = false) :
    S.ownSplitNeeded = false := by
  unfold missedInTheTablesLeaves at h
  extract_lets at h
  split at h
  · simp only [Bool.or_eq_false_iff] at h
    exact h.1.1.1
  · cases h

/-- **What `configure` returns wants no split's message in a request's own group.** -/
theorem configure_noOwnSplit {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    made.sized.proof.batch.shape.ownSplitNeeded = false := by
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨entry, he, h⟩ := exc_bind h
  split at h
  · obtain ⟨_, _, h⟩ := exc_bind h
    replace h := exc_guard h
    replace h := exc_guard h
    obtain ⟨hg, h⟩ := exc_guard_not h
    have hm : missedInTheTablesLeaves z.proof.batch.shape = false := by
      cases c : missedInTheTablesLeaves z.proof.batch.shape with
      | false => rfl
      | true =>
        exfalso
        apply hg
        unfold missedOnTheTable
        simp [c]
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    cases h
    exact noOwnSplit_of_leaves hm
  · cases h

open OnBytes.Model.Verify

/-- At the verifier's own chains. -/
theorem chainsOf_noOwnSplit {X : Public} {layoutFile : Option ByteArray} {cfg : ByteArray}
    {c : Chains} (h : chainsOf X layoutFile cfg = .ok c) :
    c.made.sized.proof.batch.shape.ownSplitNeeded = false := by
  unfold chainsOf at h
  obtain ⟨⟨links, shapes⟩, _, h⟩ := exc_bind h
  obtain ⟨z, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨made, hm, h⟩ := exc_bind h
  split at h
  · cases h
    exact configure_noOwnSplit hm
  · cases h

/-- **Where the public part is computed, the seat's parameters want no split in the own group.** -/
theorem noOwnSplit_at_seat {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) : (ProofFile.pAt Z).S.ownSplitNeeded = false :=
  chainsOf_noOwnSplit (ProofFile.Law.pub_chainsOf hZ)

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.exc_guard_not
#print axioms VerifiableInference.Desc.Last.noOwnSplit_of_leaves
#print axioms VerifiableInference.Desc.Last.configure_noOwnSplit
#print axioms VerifiableInference.Desc.Last.chainsOf_noOwnSplit
#print axioms VerifiableInference.Desc.Last.noOwnSplit_at_seat
