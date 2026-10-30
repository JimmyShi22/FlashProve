-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FallSmallK9Plain.lean: `fallSmall_k9` (Johnson/P1K8R/FallSmallK9.lean) WITH ITS LETTER
Pr AND ITS HYPOTHESIS hPr GONE. In that lemma's statement Pr stands at two places alone: its binder
and the end of hPr. So at the sentence that always holds hPr is met by anyone. A lemma; NONE OF THE
LIBRARY's GOALS. One call. Nothing on completeness, soundness or hiding.

  **`fallSmall_k9_plain`**   `fallSmall_k9` at Pr := the sentence that always holds
Kin. `P1K8.falls_uniform_k9_plain` (Johnson/P1K8R/FallsUniformK9Plain.lean): the like beneath, where
the input's type is a free letter; here it is the type at which honFit_atFiles stands.
Limits. All that Johnson/P1K8R/FallSmallK9.lean says under "Limits" stands, with fifteen named
hypotheses for sixteen: NOT A NUMBER; none of the fifteen is proved here of anything.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.FallSmallK9

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull silP front₀ join₀)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD RDT)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain Block KindName)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse Coins Ready ready Odds Mark Fall MarkDebt FallDebt KindFits
  markSeat fallSeat fellBy silentQ fitMarks at₁ walk repsAt priceAt fallsFull marksHead qMHead)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open P5J

/- As in E2E/BridgeJoinAtFiles.lean: among all that is imported, the search for this instance runs
out of its budget. It is a proposition. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

set_option maxHeartbeats 4000000 in
/-- `fallSmall_k9` without Pr and hPr: fifteen named hypotheses; the end is the same. -/
theorem fallSmall_k9_plain (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {Yes : FullSizeMatrix → XF → Prop} (Zs : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → Set (protocolAtFiles Z).OutOfDomainSeed)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (kapL : ℝ≥0∞) (notGood : Nat → Odds) (r0 : Nat → Nat)
    {pre₁ : List (Block TS ProofFile.Cl)} {e₁ : Block TS ProofFile.Cl}
    (qF : Block TS ProofFile.Cl → Fall TS → ℝ≥0∞)
    (hG : G.falls₁ = fallsFull Zp Bs.G₀ notGood r0)
    (hn : ∀ g ∈ (G.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H)).first, g.place.kind ≠
      KindName.frame)
    (hf₂ : G.falls₂ = [])
    (hf₃ : G.falls₃ = [])
    (cut : cF.blocksInOrder = pre₁ ++ [e₁])
    (hK3 : ∀ A b b' Bt, pre₁ = A ++ b :: b' :: Bt →
      ∀ mk ∈ (ProofFile.Honest.K3.Good.k3Marks Zp Bs.G₀).filter (fun m => m.place == b.place),
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (ckP .two) mk dsb (fun _ => True) ((mk.share.num : ℝ≥0∞) * kapL))
    (hq9 : ∀ g, g < 12 → ∀ b p u, IM.k9At Zp (2 * g + 1) = some p →
      VerifiableInference.Desc.K9.testsWhere Zp.p.X (2 * g + 1) 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) /
          ((ProofFile.Honest.K9.sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g + 1))))
    (hq9l : ∀ g, g < 12 → ∀ b p u, IM.k9At Zp (2 * g) = some p →
      VerifiableInference.Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) /
          ((ProofFile.Honest.K9.sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g))))
    (hq9h : ∀ b p u, IM.k9At Zp 24 = some p →
      VerifiableInference.Desc.K9.testsWhere Zp.p.X 24 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) /
          ((ProofFile.Honest.K9.sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood 24)))
    (hq4 : ∀ b gk hp, ProofFile.Honest.K4.k4ZeroBound ≤
      qF b (ProofFile.Honest.K4.k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, r0 gk, 2 * gk⟩))
    (hqF : ∀ b g, g.share.val ≤ qF b g) :
    FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n w (instanceAsPlainRecord a))
      ((List.range pre₁.length).map
        (priceAt pre₁ (marksHead Zp Bs.G₀)
          (qMHead kapL (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)))
          (repsAt cF.blocksInOrder G.falls₁) qF)).sum := by
  exact fallSmall_k9 Z Zp Np cF run₂ run₃ B G H scope live L Zs hB kapL notGood r0
    (fun _ _ _ => True) qF hG hn hf₂ hf₃ cut hK3 hq9 hq9l hq9h hq4 hqF (by intros; trivial)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.fallSmall_k9_plain
