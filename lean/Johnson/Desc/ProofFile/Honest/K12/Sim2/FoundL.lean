-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: what the filling lays at the first chain's last test.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/FoundL.lean: in the prover that onlineProverFromPublicFiles returns at the unread
filling onlineProverPartsInUse, the search at the first chain's last test (placeL) finds the half of the
job jobL at the filling's letters. This pays the premise hg of Sim2/StandL.lean there. No property of
the protocol is claimed.

  jobAtLastTest        jobL at the letters of proxLotOf (Honest/AtPureWiderK12.lean)
  proximity_lot_mem    the proximity test's list is a list of the filling
  lots_at_last_test    every list of the filling has no half at placeL, or the proximity test's halves
  last_test_found      the search finds proverSideOfProximityTest of that job
  last_test_found_of_laid   the same where the list has a half, with the finish and fitsL concluded

Premises of last_test_found. hA: onlineProverFromPublicFiles has returned at the filling. hf, hfit: the plan has the finish
and the public test fitsL says yes; where either fails the list lays no half, and the search finds
nothing.

Limits.
- Conditional on onlineProverFromPublicFiles's return. That a half plays is not said.
- It speaks of A.H, the prover that onlineProverFromPublicFiles returns, at the filling's own letters: X := Unit, the state
  on entry doorAtL. At the filling onlineProverPartsInUse alone (K1/Law/WSideAtFill.lean's head).
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LettersFirst
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12Kinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (KindName)
open ProofFile.Honest
open ProofFile.Honest.K12.AtProof

variable {W₀ : Type}

/-- **The job at the first chain's last test**, at the letters of proxLotOf. pl: the finish of the
code switch. -/
abbrev jobAtLastTest (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground)
    (pl : K2.SwitchPlace) : TestJob (Local W₀ IndexCommitterCoins Inst Cells) Unit :=
  jobL (H2U.p12OfMade Z.made) (doorAtL Z) (widerRows S Z G)
    (fun w => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
    (K2.lotClosingAt G.first.layout (K2.segmentsOf Z G)) pl

/-- The proximity test's list is a list of the filling. -/
theorem proximity_lot_mem (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : proxLotAt I S ∈ (onlineProverPartsInUse I o S O).lots := by
  rw [widerFillAtCPUOWM_lots]
  simp

/-- **Every list of the filling has no half at the last test's place, or the proximity test's
halves.** No premise. -/
theorem lots_at_last_test (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      (∀ g ∈ M.halves Z G, g.place ≠ placeL) ∨ M.halves Z G = (proxLotAt I S).halves Z G := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · refine .inl fun g hg e => ?_
    have hmem : M ∈ (widerFillAtC I o S O).lots :=
      (List.mem_append_left _ h : M ∈ (widerFillAt I o S O).lots ++ [closeLotAt I S])
    exact eleven_not_K12_plain I o S O Z G M hmem g hg (by rw [e]; rfl)
  · refine .inl fun g hg e => ?_
    have hk := closeLotAt_kinds I S Z G g hg
    rw [e] at hk
    have hk' : KindName.K12 = KindName.K10 := hk
    cases hk'
  · exact .inr rfl
  · refine .inl fun g hg e => ?_
    rw [wLot_place I o O Z G g hg] at e
    cases e

/-- **The search at the last test's place, in the prover that onlineProverFromPublicFiles returns, finds the half of the
job.** hf, hfit: public. hA: onlineProverFromPublicFiles has returned. -/
theorem last_test_found {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A) (pl : K2.SwitchPlace)
    (hf : finishAt A.Z A.G = some pl) (hfit : fitsL (H2U.p12OfMade A.Z.made) pl = true) :
    A.H.first.find? (fun g => g.place == placeL) =
      some (proverSideOfProximityTest (jobAtLastTest I S A.Z A.G pl)) := by
  refine atPure_first_find hA (proximity_lot_mem I o S O) (lots_at_last_test I o S O A.Z A.G) ?_
  rw [atPure_prox hA I S A.G]
  have e : (proxLotOf (X := Unit) I S).halves A.Z A.G = [proverSideOfProximityTest (jobAtLastTest I S A.Z A.G pl)] :=
    halves_lotAtDoor (widerRows S) (fun Z _ (w : Local W₀ IndexCommitterCoins Inst Cells) =>
      ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
      (fun Z G => K2.lotClosingAt G.first.layout (K2.segmentsOf Z G)) A.Z A.G pl hf hfit
  rw [e]
  refine List.find?_cons_of_pos ?_
  show ((H2U.p12OfMade A.Z.made).place == placeL) = true
  rw [proxPlace]
  exact beq_self_eq_true _

/-- **The same where the list has a half**: the words of FirstTestLaid. Then the finish and the
public test are had, and need not be premises. -/
theorem last_test_found_of_laid {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A)
    (hL : (proxLotAt (X := Unit) I S).halves A.Z A.G ≠ []) :
    ∃ pl, finishAt A.Z A.G = some pl ∧ fitsL (H2U.p12OfMade A.Z.made) pl = true ∧
      A.H.first.find? (fun g => g.place == placeL) =
        some (proverSideOfProximityTest (jobAtLastTest I S A.Z A.G pl)) := by
  rw [atPure_prox hA I S A.G] at hL
  cases hf : finishAt A.Z A.G with
  | none => exact absurd (proxLotOf_none I S hf) hL
  | some pl =>
    cases hfit : fitsL (H2U.p12OfMade A.Z.made) pl with
    | false => exact absurd (proxLotOf_unfit I S hf hfit) hL
    | true => exact ⟨pl, rfl, hfit, last_test_found I o S O hA pl hf hfit⟩

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.jobAtLastTest
#print axioms ProofFile.Honest.K12.Sim2.proximity_lot_mem
#print axioms ProofFile.Honest.K12.Sim2.lots_at_last_test
#print axioms ProofFile.Honest.K12.Sim2.last_test_found
#print axioms ProofFile.Honest.K12.Sim2.last_test_found_of_laid
