-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FallSmallK9.lean: THE ONE TERM THAT JOINS OUR BOUND FOR ALL TIED INPUTS
(`P1K8.falls_uniform_k9`, Johnson/P1K8R/FallsUniformK9.lean) TO THE FRAME's AUTHORS'
fallSmall_of_bound (Johnson/Desc/ProofFile/Honest/Law/FallSmallOfBound.lean): THAT BOUND's
HYPOTHESES, AT THE OBJECT's OWN LETTERS, GIVE THE HYPOTHESIS `FallSmall` THAT honFit_atFiles
(E2E/BridgeJoinAtFiles.lean) ASKS. The term is that of two like lemmas, in files that are not in
this library, at the third bound. A lemma; NONE OF THE
LIBRARY's GOALS. A joining: two calls. Nothing on completeness, soundness or hiding.

  **`fallSmall_k9`**   fallSmall_of_bound; `P1K8.falls_uniform_k9`; head_at_laid
      (E2E/HeadAtLaid.lean)
Limits. NOT A NUMBER: qF, kapL, notGood and r0 are open letters in the sum; nothing says that it is
below 1; at a sum of 1 or more `FallSmall` says nothing, nor where Yes has no member or Zs takes
every seed. SIXTEEN NAMED HYPOTHESES, NONE PROVED HERE OF ANYTHING: scope, live, L (the object's
own, as honFit_atFiles has them), hB, hG, hn, hf₂, hf₃, cut, hK3, hq9, hq9l, hq9h, hq4, hqF, hPr:
the last thirteen are `falls_uniform_k9`'s at the object's letters: the prover is the object's
(cmAlong … .proverAt 0 H over the letter H), Tied is "there are n and e with TiedOut". WHAT THREE OF
THEM COST AT THE TAKER: the same G stands in honFit_atFiles' hypothesis on the threads (its falls
are G.falls₁, G.falls₂, G.falls₃): so with hf₂ and hf₃ that hypothesis is asked with no excuse at
every sub-protocol of the other two chains, and with hG at just the listed falls of the first: no
proof is known to us that both can be met together, and no clash. honFit_atFiles itself is not
called here. WHOEVER SUMS SHARES MAY NOT DROP THE FEED-FORWARD LAYERS' FALL's ON THE STRENGTH OF
THIS LEMMA (their authors' caution): hq4 and hqF stay. AT ALL 25 SEGMENTS THE BATCHING's BOUND IS
EXCHANGED, NOT PAID. All that Johnson/P1K8R/FallsUniformK9.lean says under "Limits" stands.
fallSmall_of_bound, AND falls_uniform_listed BENEATH OUR BOUND, ARE THE FRAME's AUTHORS' WORDING.
THE NAME STANDS IN THE NAMESPACE AtPublicFiles.AtFiles, honFit_atFiles' authors', though the file lies
under Johnson/P1K8R/: the namespace, the opens, the local instance and the variables are those of
the frame's authors' FallSmallAtFiles.lean. No filling is named. One option is raised
(maxHeartbeats, at the frame's authors' figure: whether less serves is not measured). No tactic
that searches.
Terms: lean/GLOSSARY.md.
-/
import E2E.HeadAtLaid
import Johnson.Desc.ProofFile.Honest.Law.FallSmallOfBound
import Johnson.P1K8R.FallsUniformK9

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
/-- `FallSmall` at the family and the falls of honFit_atFiles, at the inputs of `TiedOut`, at the
sum of `P1K8.falls_uniform_k9`, under that lemma's hypotheses at the object's letters. -/
theorem fallSmall_k9 (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {Yes : FullSizeMatrix → XF → Prop} (Zs : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → Set (protocolAtFiles Z).OutOfDomainSeed)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (kapL : ℝ≥0∞) (notGood : Nat → Odds) (r0 : Nat → Nat)
    {pre₁ : List (Block TS ProofFile.Cl)} {e₁ : Block TS ProofFile.Cl}
    (Pr : Block TS ProofFile.Cl → List Fmt.Drawn → TS → Prop) (qF : Block TS ProofFile.Cl → Fall TS → ℝ≥0∞)
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
    (hqF : ∀ b g, g.share.val ≤ qF b g)
    (hPr : ∀ (w₀ : FullSizeMatrix) (rc : (protocolAtFiles Z).EncodingRandomness) (x : ProofFile.Inst) (k : Coins B)
      (R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh), (∃ n e, TiedOut Z Zp Np cF run₂ run₃ B G
                                                       H Yes Zs n (w₀, rc, e) x) →
      ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) B (G.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt
                    0 H)) w₀ rc x k = .ok R →
      ∀ A b b' Bt, pre₁ = A ++ b :: b' :: Bt →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy cF.blocksInOrder G.falls₁ (at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover ((cmAlong (AZ Z) PadZ
                             (holdZ Z)).proverAt 0 H)) w₀ rc x R) (0 +
                             (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (marksHead Zp Bs.G₀ ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0
                    H)) w₀ rc x R).start = some a →
      walk (at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover ((cmAlong (AZ Z) PadZ (holdZ
                    Z)).proverAt 0 H)) w₀ rc x R).lay
        ((at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt
                      0 H)) w₀ rc x R).steps.take (0 + (A.flatMap
                      (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) A.length (x.pub, s')) →
      Pr b fr s') :
    FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n w (instanceAsPlainRecord a))
      ((List.range pre₁.length).map
        (priceAt pre₁ (marksHead Zp Bs.G₀)
          (qMHead kapL (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)))
          (repsAt cF.blocksInOrder G.falls₁) qF)).sum := by
  obtain ⟨xh, h⟩ := head_at_laid Z scope live L
  exact fallSmall_of_bound Z Zp Np cF run₂ run₃ B G H scope live L Zs _
    (P1K8.falls_uniform_k9 h hB _ _ _ G ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) kapL
      notGood r0
      (fun w₀ rc x => ∃ n e, TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n (w₀, rc, e) x)
      Pr qF hG hn hf₂ hf₃ cut hK3 hq9 hq9l hq9h hq4 hqF hPr)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.fallSmall_k9
