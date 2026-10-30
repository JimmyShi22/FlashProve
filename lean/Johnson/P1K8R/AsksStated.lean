-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/AsksStated.lean: THE SMALLNESS TEST's SECOND FALL IN THE HONEST SIDE's FRAME: THE
PREMISE hq OF `firstAsks_share_blocks` (Johnson/P1K8R/LastAtAsks.lean), "THE WRITTEN SUM IS AT MOST
THE NUMBER LAID FOR OUR RECORD", IS MET AT THE STATED SHARE `k8ShareAt`
(Johnson/P1K8R/ShareStated.lean), WHEREVER THE NUMBER LAID FOR A COUNTED FALL IS AT LEAST ITS STATED
SHARE's VALUE. Lemmas; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness,
soundness or hiding.

  **`hq_stated`**   the written sum is that record's share's value: `k8ShareAt_of`, `nU_is_lot`,
      `countShare_sum`
  **`hq_at_share`**   the premise, in its own form
  **`firstAsks_stated_blocks`**   `firstAsks_share_blocks` at that share, hq paid: one call
Limits. At strings of hash blocks alone. (hqF) is a premise on the frame's letter qF. As in
ShareStated.lean: the number is held under `PLast` alone. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.LastAtAsks
import Johnson.P1K8R.ShareStated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw reach_fold)
open ProofFile.Honest (Odds FallDebt KindFits Fall Mark MarkDebt FirstAsks firstAsks_cut fellBy silentQ
  fitMarks drawsFit walk groupOf localFall ChainAt Local fallSeat markSeat cut_first)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open scoped ENNReal

/-- **The written sum IS the value of the stated share of the second fall's own record**, at the
share `k8ShareAt` (Johnson/P1K8R/ShareStated.lean). -/
theorem hq_stated {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {l o : ℕ} {p : K9.Where} {X : LinkH}
    (hp : IM.k9At Z l = some p) (hX : Bs.G₀.built.toList[l]? = some X) :
    shareNumberB Bs p X =
      (k8ShareFall l o (ProofFile.k8NU Bs.G₀ X) (k8ShareAt Z Bs.G₀ l)).share.val := by
  show shareNumberB Bs p X = (k8ShareAt Z Bs.G₀ l).val
  rw [k8ShareAt_of (by rw [← Array.getElem?_toList]; exact hX) hp, nU_is_lot, countShare_sum]
  rfl

/-- **SO THE PREMISE hq OF `firstAsks_share_blocks` (Johnson/P1K8R/LastAtAsks.lean) IS MET** at
share := `k8ShareAt Z Bs.G₀`, wherever the number laid for a counted fall is at least its stated
share's value. -/
theorem hq_at_share {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {c : Chain S Claim}
    (qF : Block S Claim → Fall S → ℝ≥0∞) (hqF : ∀ b g, g.share.val ≤ qF b g) :
    ∀ l, l < 25 → ∀ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b → IM.k9At Z l = some p →
      Bs.G₀.built.toList[l]? = some X →
      shareNumberB Bs p X ≤
        qF b (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) (k8ShareAt Z Bs.G₀ l)) :=
  fun _ _ b _ _ _ hp hX => le_trans (le_of_eq (hq_stated hp hX)) (hqF b _)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

set_option maxHeartbeats 2000000 in
/-- **`firstAsks_share_blocks` AT THE STATED SHARE**: share := `k8ShareAt Z Bs.G₀`; its premise hq
is gone; in its stead: the number laid for a counted fall is at least its stated share's value
(hqF). One call: so Lean holds that `hq_at_share` has the premise's form. -/
theorem firstAsks_stated_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hOk : F.planOk = true)
    (fs : List (Fall S)) (hm : List Mark) (p₁ : ℕ → ℝ≥0∞) {pre₁ : List (Block S Claim)}
    {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Xc : List Fmt.Drawn → ChainAt S Claim (Local W₀ Rc ProofFile.Inst Tr) X₁)
    (PM : Block S Claim → List Fmt.Drawn → Prop) (qM : Block S Claim → Mark → ℝ≥0∞)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    (reps : Block S Claim → List (Fall S))
    (hcut : cutOf c.blocksInOrder = cutFirstFull) (cut : c.blocksInOrder = pre₁ ++ [e₁])
    (hz : ∀ b ∈ pre₁, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (hfs : ∀ f ∈ fs, (fallSeat P5J.At.links) f.place = true)
    (hseat : ∀ mk ∈ hm, markSeat mk.place = true)
    (hq0 : ∀ b ∈ pre₁, qM b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0)
    (hM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) (qM b mk))
    (hPM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
    (hFr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g ∈ reps b, ¬ ShareFallAt Bs (k8ShareAt Z Bs.G₀) A.length g → ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) g 0 b (b' :: B ++ [e₁]) dsb []
        (PWith Z c Bs Pr b) (qF b g))
    (hqF : ∀ b g, g.share.val ≤ qF b g)
    (hin : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ f ∈ fs, (∃ d ∈ groupOf b (b' :: B ++ [e₁]), f.place = d.place) →
      ∃ g ∈ reps b, ∀ fr s' own, PWith Z c Bs Pr b fr s' →
        localFall [f] 0 (b :: (b' :: B ++ [e₁])) s' own →
        localFall [g] 0 (b :: (b' :: B ++ [e₁])) s' own)
    (hPr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A.length (x.pub, s')) →
      Pr b fr s')
    (hLeft : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A.length (x.pub, s')) →
      ∀ l, l < 25 → A.length = 14 * l + (if l = 24 then 11 else 9) →
      ShareLive s' ∧ LiveFore s' ∧ StillAtZ Z Bs l s')
    (hp₁ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum + ((reps b).map (qF b)).sum ≤
        p₁ (0 + A.length))
    (hp₂ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = false →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum ≤ p₁ (0 + A.length)) :
    FirstAsks (F := descAt Z A₂ B₂ c) (_root_.Run.ckP .two) fs hm p₁ pre₁ e₁ x Xc
      (fallSeat P5J.At.links) markSeat PM qM (PWith Z c Bs Pr) qF reps :=
  firstAsks_share_blocks hE hS hR O hOk fs hm p₁ x Xc PM qM Pr qF reps (k8ShareAt Z Bs.G₀) hcut cut
    hz hfs hseat hq0 hM hPM hFr (hq_at_share qF hqF) hin hPr hLeft hp₁ hp₂

end

end P1K8

#print axioms P1K8.hq_stated
#print axioms P1K8.hq_at_share
#print axioms P1K8.firstAsks_stated_blocks
