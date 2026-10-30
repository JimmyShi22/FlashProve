-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPWorkBits.lean: the work bits of the three protocols at the public files are
faithful. The verifiers that soundness speaks of reject unless all work bits are 0, and uniform
challenges with the work bits set to 0 are uniform challenges conditioned on passing. No hypothesis.

  puts_rho                 nonces change no challenge.
  pair_conditioned         along a pair with bits: clearing is conditioning, by counting.
  workFaithful_of_pair     the six laws of WorkBitsFaithful, from a pair that fits a wire and keeps
                           probabilities.
  workFaithful_atFiles     the three protocols of protocolAtFiles Z.
-/
import E2E.CompleteAsIOPAtFiles
import E2E.ClimbAccLawAtD

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Climb
open OnBytes.Prover Prob TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

theorem puts_rho {lam K : ℕ} : ∀ {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A} {τ τ' : Tr s},
    Puts s A W τ τ' → τ'.rho = τ.rho
  | [], _, _, _, _, _ => rfl
  | _ :: _, (_, _), (_, _), (_, c, τ), (_, c', τ'), h => by
      show (c', Tr.rho τ') = (c, Tr.rho τ)
      rw [h.2.1, puts_rho h.2.2.2]

/-- Clearing is conditioning, along a pair with bits: the challenges that pass are the images of
the old ones, one for one. -/
theorem pair_conditioned {s t : Shape} (p : Pair s t) (B : Set (Rho t)) :
    prRho {ρ' : Rho t | p.passR ρ' = true} * prRho {ρ : Rho s | p.zeroR ρ ∈ B} =
      prRho {ρ' : Rho t | p.passR ρ' = true ∧ ρ' ∈ B} := by
  have cntB : ∀ B : Set (Rho t), cnt (fun ρ' : Rho t => p.passR ρ' = true ∧ ρ' ∈ B) =
      cnt (fun ρ : Rho s => p.zeroR ρ ∈ B) := fun B =>
    Nat.card_congr
      { toFun := fun a => ⟨p.oldR a.1, by
          show p.zeroR (p.oldR a.1) ∈ B
          rw [Pair.zeroR_oldR p a.1 a.2.1]
          exact a.2.2⟩
        invFun := fun b => ⟨p.zeroR b.1, p.passR_zeroR b.1, b.2⟩
        left_inv := fun a => Subtype.ext (Pair.zeroR_oldR p a.1 a.2.1)
        right_inv := fun b => Subtype.ext (Pair.oldR_zeroR p b.1) }
  have cntAll : cnt (fun ρ' : Rho t => p.passR ρ' = true) = Fintype.card (Rho s) := by
    have e₁ : cnt (fun ρ' : Rho t => p.passR ρ' = true) =
        cnt (fun ρ' : Rho t => p.passR ρ' = true ∧ ρ' ∈ (Set.univ : Set (Rho t))) :=
      cnt_congr fun ρ' => by simp
    have e₂ : cnt (fun ρ : Rho s => p.zeroR ρ ∈ (Set.univ : Set (Rho t))) =
        cnt (fun _ : Rho s => True) := cnt_congr fun ρ => by simp
    rw [e₁, cntB, e₂, cnt_true]
  show pr (unif (Rho t)) {ρ' | p.passR ρ' = true} * pr (unif (Rho s)) {ρ | p.zeroR ρ ∈ B} =
    pr (unif (Rho t)) {ρ' | p.passR ρ' = true ∧ ρ' ∈ B}
  rw [pr_unif_eq (fun ρ' : Rho t => p.passR ρ' = true),
    pr_unif_eq (fun ρ : Rho s => p.zeroR ρ ∈ B),
    pr_unif_eq (fun ρ' : Rho t => p.passR ρ' = true ∧ ρ' ∈ B), cntB, cntAll]
  have n0 : (Fintype.card (Rho s) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := Rho s))
  have hN : (Fintype.card (Rho s) : ℝ≥0∞) * (Fintype.card (Rho s) : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel n0 (ENNReal.natCast_ne_top _)
  calc (Fintype.card (Rho s) : ℝ≥0∞) / (Fintype.card (Rho t) : ℝ≥0∞) *
        ((cnt fun ρ : Rho s => p.zeroR ρ ∈ B : ℕ) / (Fintype.card (Rho s) : ℝ≥0∞))
      = ((Fintype.card (Rho s) : ℝ≥0∞) * (Fintype.card (Rho s) : ℝ≥0∞)⁻¹) *
          ((cnt fun ρ : Rho s => p.zeroR ρ ∈ B : ℕ) / (Fintype.card (Rho t) : ℝ≥0∞)) := by
        simp only [div_eq_mul_inv]
        ring
    _ = ((cnt fun ρ : Rho s => p.zeroR ρ ∈ B : ℕ) / (Fintype.card (Rho t) : ℝ≥0∞)) := by
        rw [hN, one_mul]

/-- **The six laws, from a pair that fits a wire and keeps probabilities.** -/
theorem workFaithful_of_pair {X : Type} {E : ExtSpec} {lam K : ℕ} {Q₀ Q : BatchInteractiveOracleProof X E}
    (S : BatchPair Q₀ Q) {W : RoundsQueryLayout lam K Q.loc.shape Q.ann} (hF : Fits S.pair.toPair Q.ann W)
    (hU : S.pair.toPair.Unif) : WorkBitsFaithful Q.loc (workOfWire Q.ann W) where
  verifierAsksTheWork := fun x y τ h => by
    have a := S.acc x y τ
    rw [h] at a
    have p : S.pair.toPair.passTr τ = true := by
      have b := a.symm
      rw [Bool.and_eq_true] at b
      exact b.1
    show RoundsQueryLayout.pass Q.loc.shape Q.ann W τ.rho = true
    rw [hF.pass τ.rho, ← Pair.passTr_rho]
    exact p
  clearedPasses := fun ρ => by
    show RoundsQueryLayout.pass Q.loc.shape Q.ann W (RoundsQueryLayout.zero Q.loc.shape Q.ann W ρ) = true
    rw [hF.pass, hF.zero_eq]
    exact Pair.passR_zeroR _ _
  passingStays := fun ρ h => by
    have h' : S.pair.toPair.passR ρ = true := (hF.pass ρ).symm.trans h
    show RoundsQueryLayout.zero Q.loc.shape Q.ann W ρ = ρ
    rw [hF.zero_eq]
    exact Pair.zeroR_oldR _ _ h'
  clearedIsConditioned := fun B => by
    have e : prRho {ρ : Rho Q.loc.shape | RoundsQueryLayout.zero Q.loc.shape Q.ann W ρ ∈ B} =
        prRho {ρ : Rho Q₀.loc.shape | S.pair.toPair.zeroR ρ ∈ B} := hF.prRho_zero hU B
    have e₁ : {ρ : Rho Q.loc.shape | RoundsQueryLayout.pass Q.loc.shape Q.ann W ρ = true} =
        {ρ | S.pair.toPair.passR ρ = true} := Set.ext fun ρ => by
      show RoundsQueryLayout.pass Q.loc.shape Q.ann W ρ = true ↔ S.pair.toPair.passR ρ = true
      rw [hF.pass]
    have e₂ : {ρ : Rho Q.loc.shape | RoundsQueryLayout.pass Q.loc.shape Q.ann W ρ = true ∧ ρ ∈ B} =
        {ρ | S.pair.toPair.passR ρ = true ∧ ρ ∈ B} := Set.ext fun ρ => by
      show (RoundsQueryLayout.pass Q.loc.shape Q.ann W ρ = true ∧ ρ ∈ B) ↔
        (S.pair.toPair.passR ρ = true ∧ ρ ∈ B)
      rw [hF.pass]
    show prRho {ρ : Rho Q.loc.shape | RoundsQueryLayout.pass Q.loc.shape Q.ann W ρ = true} *
        prRho {ρ : Rho Q.loc.shape | RoundsQueryLayout.zero Q.loc.shape Q.ann W ρ ∈ B} =
      prRho {ρ : Rho Q.loc.shape | RoundsQueryLayout.pass Q.loc.shape Q.ann W ρ = true ∧ ρ ∈ B}
    rw [e, e₁, e₂]
    exact pair_conditioned _ B
  noncesKeepChallenges := fun _ _ h => puts_rho h
  ownNonces := fun τ => puts_refl _ _ _ τ

end AtPublicFiles.Climb

namespace AtPublicFiles.AtFiles
open AtPublicFiles.Climb
open VerifierAndGoals (PublicFiles)
open FlashProve (allZeroDigest)

/-- **The work bits of protocolAtFiles Z are faithful**, at every set of public files. -/
theorem workFaithful_atFiles (Z : PublicFiles) : (workAtFiles Z).Faithful :=
  ⟨workFaithful_of_pair (pair0 (lettersZ Z allZeroDigest [])).key (fits_key_input (lettersZ Z allZeroDigest []))
      (unif_key_at (lettersZ Z allZeroDigest [])),
    workFaithful_of_pair (pair0 (lettersZ Z allZeroDigest [])).entry
      (fits_entry_input (lettersZ Z allZeroDigest [])) (unif_entry_at (lettersZ Z allZeroDigest [])),
    workFaithful_of_pair (pair0 (lettersZ Z allZeroDigest [])).proof
      (fits_proof_input (lettersZ Z allZeroDigest [])) (unif_proof_at (lettersZ Z allZeroDigest []))⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.Climb.workFaithful_of_pair
#print axioms AtPublicFiles.AtFiles.workFaithful_atFiles
