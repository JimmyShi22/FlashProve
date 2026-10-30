-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/CarryAtLaw.lean: WHAT THE TERMS OF Johnson/Desc/ProofFile/CarryAt.lean
ARE AT
THE VALUE THAT `ProofFile.onlineDescription` GIVES. Statements with their proofs: unfoldings and calls.

  `rowAtK2_eq`, `pAtK2?_eq`: the two terms with the table and the list of places bound once: the
  forms
    in which a file for Lean's evaluator reads them.
  `pub_files`: the public part that `pubPlain` makes holds the parameter file and the scale file
  that
    it was made of: so `rowAtK2 Z.pol lay Z.KL` is `rowAtK2 pol lay KL`.
  `doorAtK2_in`, `doorAtK2_finish`: the way in is the identity but at the finish.
  **`descPure_seated`**: onlineDescription o pol lay KL = .ok G gives Z, N, c with: the public part is Z;
  K12's
    places are N; `onlineFirstChainAt Z = .ok c`; G = `seatedAt o Z N c`. By `descPure_chain`
    (Law/LinkAtLaw.lean), which calls `descPure_parts`. IT SAYS MORE THAN `descPure_cut`
    (Johnson/Desc/Plain/StartThreeAtPure.lean) AND TYPES NO WALK OF ITS OWN.
  `data_older`: the rounds' data do not read the placeholder for the second hash function.
  `wholeAt_of`, `allAt_of`, `keyAt_of`: where that value's data are D: `wholeAt Z = some D`,
    `allAt Z = allOf D`, `keyAt Z = D.key₁`: the depth at which the frame is laid (`WholeD.at`)
    turns neither the list of trees nor the keys.
Limits. Facts on definitions' texts. No soundness is claimed.

-/
import Johnson.Desc.ProofFile.CarryAt
import Johnson.Desc.ProofFile.Law.LinkAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2Caller (tableOf)
open VerifiableInference.Desc.Sound (allOf)
open Desc.K14 (sharedSeatAt)

theorem rowAtK2_eq (pol lay KL : ByteArray) (m : Nat) :
    rowAtK2 pol lay KL m = ((tableOf pol lay KL).toOption.getD [])[m]? := by
  unfold rowAtK2
  cases (tableOf pol lay KL).toOption <;> rfl

theorem pAtK2?_eq (Z : Pub) (m : Nat) :
    pAtK2? Z m = ((k2SpotsAt Z).find? fun x => x.2.grp == m + 1).map (·.2) := rfl

/-- The public part holds the two files that it was made of. -/
theorem pub_files {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pubPlain o pol lay KL = .ok Z) : Z.pol = pol ∧ Z.KL = KL := by
  unfold pubPlain pubBy at h
  obtain ⟨m, _, h⟩ := bind_ok h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; exact ⟨rfl, rfl⟩)

theorem doorAtK2_in (Z : Pub) (m : Nat) (s : S) (h : (pAtK2 Z m).stands ≠ .finish) :
    doorAtK2 Z m s = some s := by
  unfold doorAtK2
  cases hs : (pAtK2 Z m).stands with
  | finish => exact absurd hs h
  | link => rfl
  | head => rfl

theorem doorAtK2_finish (Z : Pub) (m : Nat) (s : S) (h : (pAtK2 Z m).stands = .finish) :
    doorAtK2 Z m s = (VerifiableInference.Desc.First.K2.finishFrontQ s).toOption := by
  unfold doorAtK2
  rw [h]

/-- **Wherever `onlineDescription` gives a value: its letters, the first chain's make among them.** -/
theorem descPure_seated {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {G : FileDescription Inst}
    (h : onlineDescription o pol lay KL = .ok G) :
    ∃ (Z : Pub) (N : H2U.Places4) (c : Chain S Cl), pureRoad.pub o pol lay KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧ onlineFirstChainAt Z = .ok c ∧ G = seatedAt o Z N c := by
  obtain ⟨Z, c, A, B, hZ, hc, hA, hB, rfl⟩ := descPure_chain h
  have hA' : sharedSeatAt Z = some A := hA
  have hB' : P2Third.secondSeat Z = some B := hB
  unfold sharedSeatAt at hA'
  unfold P2Third.secondSeat at hB'
  cases hN : H2U.placesOfMade Z.made with
  | error e => rw [hN] at hA'; cases hA'
  | ok N =>
    rw [hN] at hA' hB'
    cases hA'
    cases hB'
    exact ⟨Z, N, c, hZ, hN, hc, rfl⟩

/-- The rounds' data do not read the placeholder for the second hash function. -/
theorem data_older (o o' : SecondHashFunctionArgument) (Z : Pub) (N : H2U.Places4) (c : Chain S Cl)
    (file : String) : (seatedAt o Z N c).data file = (seatedAt o' Z N c).data file := by
  have h1 : (seatedAt o Z N c).roundsDeclaredByBlocks = (seatedAt o' Z N c).roundsDeclaredByBlocks := by
    unfold FileDescription.roundsDeclaredByBlocks
    rfl
  have h2 : (seatedAt o Z N c).tableDepth = (seatedAt o' Z N c).tableDepth := rfl
  unfold FileDescription.data
  rw [h1, h2]

variable {o : SecondHashFunctionArgument} {Z : Pub} {N : H2U.Places4} {c : Chain S Cl} {D : WholeD}

theorem wholeAt_of (hN : H2U.placesOfMade Z.made = .ok N) (hc : onlineFirstChainAt Z = .ok c)
    (hD : (seatedAt o Z N c).data "proof file" = .ok D) : wholeAt Z = some D := by
  unfold wholeAt
  rw [hN, hc]
  show ((seatedAt emptySecondHashFunction Z N c).data "proof file").toOption = some D
  rw [data_older emptySecondHashFunction o, hD]
  rfl

theorem allAt_of (h : wholeAt Z = some D) : allAt Z = allOf D := by
  unfold allAt
  rw [h]
  rfl

theorem keyAt_of (h : wholeAt Z = some D) : keyAt Z = D.key₁ := by
  unfold keyAt
  rw [h]
  rfl

end ProofFile.Law

#print axioms ProofFile.Law.rowAtK2_eq
#print axioms ProofFile.Law.pub_files
#print axioms ProofFile.Law.doorAtK2_in
#print axioms ProofFile.Law.descPure_seated
#print axioms ProofFile.Law.wholeAt_of
#print axioms ProofFile.Law.allAt_of
#print axioms ProofFile.Law.keyAt_of
