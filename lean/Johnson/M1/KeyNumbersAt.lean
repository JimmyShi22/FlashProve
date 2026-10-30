-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: the count at the description.
/-
Johnson/M1/KeyNumbersAt.lean: in the goals' scope, at every description of the key file that the public files name: its declared rounds are
the written ones, so what its own rounds read of the trees of each of the nineteen sendings and of the fold's is within the bound, on each of
the three chains. No property of the protocol is claimed here.


That a member of a side stands at such a round is not said here.
-/
import Johnson.M1.KeyNumbersProved
import Johnson.M1.NumbersAtProved
import Johnson.SendSim.Seat.KeyReadsAtLive
import E2E.KeyProtocolOverDescription
import Johnson.Desc.Sound.ReadsOkProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open Johnson.KB8 (declKeyFull)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)

set_option maxRecDepth 1000000 in
/-- The table off the dry lists is the table off the written declared rounds. -/
theorem tabK_eq : tabK = readsTab declKeyFull := by decide +kernel

/-- **In scope, the declared rounds of a description that the public files name are the written ones.** -/
theorem keyDecl_of_named {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true)
    {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces} (h : KeyNamed Z X N P) :
    (keyFileDescription X N P).roundsDeclaredByBlocks = declKeyFull := by
  obtain ⟨X₀, m, hX, hm, hd, -⟩ := h.named
  have hd2 : Key.descriptionFromPlan m = .ok (keyFileDescription X N P) := by
    unfold Key.descAt at hd
    rw [hm] at hd
    exact hd
  unfold Key.descriptionFromPlan at hd2
  cases e1 : Key.sourceOf m with
  | error e => rw [e1] at hd2; cases hd2
  | ok X' =>
    rw [e1] at hd2
    cases e2 : Key.rangesNumbers m with
    | error e => rw [e2] at hd2; cases hd2
    | ok N' =>
      rw [e2] at hd2
      cases e3 : Key.laterPlaces m with
      | error e => rw [e3] at hd2; cases hd2
      | ok P' =>
        rw [e3] at hd2
        have e : Key.descriptionFromSource X' N' P' = keyFileDescription X N P := Except.ok.inj hd2
        rw [← e]
        exact (VerifiableInference.Desc.Sound.decl_of_planOk (Key.descriptionFromSource X' N' P') (e ▸ h.plan)).trans
          (Johnson.AtFull.KeyBack.decl_at_return scope hX hm e1)

/-- (A3) AT THE KEY FILE's DESCRIPTION. -/
def Spec.atDescriptionK : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles), VerifierAndGoals.InScope Z = true →
  ∀ (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces), KeyNamed Z X N P →
    ∀ ch ∈ [0, 1, 2], ∀ i < (sendsK ch).length, ReadsWithinAt (keyFileDescription X N P) ch (parK ch i) (treesBeforeK ch i)

theorem atDescriptionK : Spec.atDescriptionK := by
  intro Z scope X N P h ch hch i hi
  refine readsWithinAtOf _ _ _ _ ?_
  rw [readsWithinAtB_tab, keyDecl_of_named scope h, ← tabK_eq]
  obtain ⟨-, -, -, -, -, -, hc⟩ := countK
  have h1 := List.all_eq_true.1 (hc ch hch) i (List.mem_range.2 hi)
  have h2 := Bool.and_eq_true_iff.1 h1
  exact (Bool.and_eq_true_iff.1 h2.1).2

/-- **The bound that is a premise inside exact and fresh**, at every sending of the key file, at every due list. -/
theorem budK {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true) {X : Key.Source} {N : H2U.PlaceNums}
    {P : Key.LaterPlaces} (h : KeyNamed Z X N P) {ch : Nat} (hch : ch ∈ [0, 1, 2]) {i : Nat}
    (hi : i < (sendsK ch).length) (ρ : Draws) (hρ : ρ.due (keyFileDescription X N P) = true) (rs : List Nat) :
    budAt (parK ch i) (asksFrom (treeAsks (keyFileDescription X N P) ρ ch) rs (treesBeforeK ch i)) :=
  budAt_of_readsAt (atDescriptionK Z scope X N P h ch hch i hi) ρ hρ rs

end OnBytes.M1

#print axioms OnBytes.M1.tabK_eq
#print axioms OnBytes.M1.keyDecl_of_named
#print axioms OnBytes.M1.atDescriptionK
#print axioms OnBytes.M1.budK
