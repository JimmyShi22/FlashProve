-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/FromDebts.lean: the proof of the implication Spec.roadPrivate_of_debts
(Johnson/FrontRoad/FromDebtsSpec.lean). No parameters are known at which its premises hold together:
it may apply to nothing.
Terms of this folder: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  below_yesAt   the field below of PremWDebts, at the relation yesAt, is a theorem. It is asked
      again inside PremWDebts all the same.
  premAll_of_debts   PremWDebts at every value d of the public reading gives PremAll at debtSides:
      one call of premW_told_of_debts (E2E/BridgeDebtsTold.lean) at each d.
  zetaLe_of_debts   the premise ZetaLe at debtSides, at the bound boundZ … + (zT + hT + n · hO):
      zetaLe_withErrors (Johnson/FrontRoad/ZetaErr.lean) at the numbers indexPrivacyNumbers s1 zT 0 0 hT 0 hO.
  roadPrivate_of_debts   proves Spec.roadPrivate_of_debts: these two, tieOn_yesAt
      (Johnson/FrontRoad/TieServed.lean), familyLaws_home (Johnson/FrontRoad/AtHomeT.lean) and
      roadPrivate_of_premAll (Johnson/FrontRoad/FromPremises.lean).

How it fits, and all limits: the head of Johnson/FrontRoad/FromDebtsSpec.lean. An implication; it
proves nothing of any prover. It counts as no goal of the release.
-/
import Johnson.FrontRoad.FromDebtsSpec
import Johnson.FrontRoad.FromPremises
import Johnson.FrontRoad.AtHomeT
import Johnson.FrontRoad.TieServed
import Johnson.FrontRoad.ZetaErr

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along
open AtPublicFiles.Committed
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes (TableKey)
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides)
open VerifierAndGoals (PublicFiles InScope readFiles settingsOfRead)
open FlashProve (homeR homeT backB yesAt flashProveDescription allZeroDigest)
open OnBytes.LinkSim.AtHome (homeSim)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_fromDebts : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_fromDebts {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

section Letters
variable (b : PublicFiles → ℕ) (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF :
                        VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
  (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂]
  [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)
  (c : (homeT b Z).D → CoinNums (List Bool))
  (R₀ : (homeT b Z).D → RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
    (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z))
  (okV : (homeT b Z).D → ByteArray × ByteArray → Prop)
  (v₀ : (homeT b Z).D → ByteArray × ByteArray)
  (startT startL startB :
    (homeT b Z).D → ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits)
  (sT : AtPublicFiles.KeyBridge.SimT (homeR b Z).protocol) (s1 : ℕ) (zT hT hO : ℝ≥0∞) (i₀ : (homeR b Z).Index)

/-- The field below of PremWDebts, at the relation yesAt, is a theorem: yesAt_below_object
(Johnson/FrontRoad/TieServed.lean), read at the name RyesZ. -/
theorem below_yesAt {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) :
    ∀ i x, yesAt b Z hr i x → RyesZ Z i x :=
  fun i x h => yesAt_below_object b Z hr i x h

/-- If PremWDebts holds at every value d of the public reading, PremAll holds at debtSides. -/
theorem premAll_of_debts (Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop) (ok : (homeR b Z).Index → Prop)
    (h : ∀ d, PremWDebts allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT (c d) (R₀ d)
      (okV d) (v₀ d) (startT d) (startL d) (startB d) Yes ok sT s1 zT hT hO) :
    PremAll (debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
      startB sT s1 zT hT hO i₀) ok Yes fun _ => True :=
  fun d _ => premW_told_of_debts b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT (c d) (R₀ d)
    (okV d) (v₀ d) (startT d) (startL d) (startB d) d (h d)

/-- The premise ZetaLe at debtSides, where Z is in scope, at least 256 bits of a leaf's salt are
sampled at every d, the number of copies is the same at every d, and the bounds on attempts are at
most CT, CL and CB at every d. -/
theorem zetaLe_of_debts (scope : InScope Z = true) (M CT CL CB : ℕ)
    (hM : ∀ d, ((debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB sT s1 zT hT hO i₀).a d).M = M)
    (cT : ∀ d i, ((debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB sT s1 zT hT hO i₀).a d).capT i ≤ CT)
    (cL : ∀ d i, ((debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB sT s1 zT hT hO i₀).a d).capL i ≤ CL)
    (cB : ∀ d i, ((debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB sT s1 zT hT hO i₀).a d).capB i ≤ CB)
    (hℓ : ∀ d, 256 ≤ (c d).ℓ) :
    ZetaLe (debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
      startB sT s1 zT hT hO i₀) (fun _ => True)
      (upTo s1 fun t n => boundZ (9 + CT + CL + CB) M t n + (zT + hT + (n : ℝ≥0∞) * hO)) := by
  intro d hd t n
  refine (zetaLe_withErrors b Z scope (debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT
    c R₀ okV v₀ startT startL startB sT s1 zT hT hO i₀) M s1 CT CL CB zT 0 0 hT 0 hO 0 hM
    (fun _ => le_rfl) cT cL cB hℓ
    (fun _ => ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩) d hd t n).trans
    (le_of_eq ?_)
  unfold upTo
  split
  · simp only [mul_zero, add_zero]
    ring
  · rfl

end Letters

/-- **An implication.** No parameters are known at which its premises hold together: it may apply to
nothing. Proves Spec.roadPrivate_of_debts. -/
theorem roadPrivate_of_debts : Spec.roadPrivate_of_debts :=
  fun b Z pp hr Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr X₀ Xh B G H Fx TrT X₀T XT Q₂ Q₃ BT _ _ _ _ HT
      val₂ val₃ shT c R₀ okV v₀ startT startL startB sT s1 zT hT hO i₀ ok x₀ Form parse encF M CT CL
      CB NC NP bound hD hok hM cT cL cB hℓ hNC hNP hCoins =>
    roadPrivate_of_premAll (flashProveDescription.reBound b) Z allZeroDigest [] (homeT b Z) Prod.mk
      (debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
        startB sT s1 zT hT hO i₀)
      (settingsOfRead pp) (backB b Z (settingsOfRead pp)) x₀ (backTok b Z) Form parse encF
      (CanServe (settingsOfRead pp)) (yesAt b Z hr) ok _ NC NP bound (familyLaws_home b Z)
      (premAll_of_debts b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
        startL startB sT s1 zT hT hO i₀ (yesAt b Z hr) ok hD)
      (zetaLe_of_debts b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
        startB sT s1 zT hT hO i₀ (hD ((allZeroDigest, []) : (homeT b Z).D)).scope M CT CL CB hM cT cL cB hℓ)
      hok (tieOn_yesAt b Z (hD ((allZeroDigest, []) : (homeT b Z).D)).scope hr) hNC hNP hCoins

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_fromDebts
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_fromDebts
#print axioms OnBytes.FrontRoad.below_yesAt
#print axioms OnBytes.FrontRoad.premAll_of_debts
#print axioms OnBytes.FrontRoad.zetaLe_of_debts
#print axioms OnBytes.FrontRoad.roadPrivate_of_debts
