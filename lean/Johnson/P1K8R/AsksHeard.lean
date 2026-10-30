-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/AsksHeard.lean: THE SMALLNESS TEST's SECOND FALL IN THE HONEST SIDE's FRAME: THE
MEMBER OF `FirstAsks` OF Johnson/P1K8R/AsksStated.lean WITH LESS ASKED AT OUR 25 BLOCKS: OF
`StillAtZ` NOTHING AT THE 24 SEGMENTS BELOW THE HEAD's, ONE FIELD AT THE HEAD's: THE REST ARE THREE
KINDS' AUTHORS' THEOREMS AT EVERY STATE THAT `WrapEnd` ADMITS, AND `WrapEnd` IS WHAT THE FRAME
HANDS. One lemma; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness or
hiding.

  **`firstAsks_head_blocks`**   `firstAsks_stated_blocks` by one call; `wrapEnd_of_handed`,
      `stillAtZ_of_heard`, `heardAtZ_of_head`
Limits. As in LastAtAsks.lean and AsksStated.lean: A MEMBER UNDER PREMISES: NONE OF THEM IS SHOWN
HERE OF ANYTHING, NOR THAT THEY CAN BE MET TOGETHER. At strings of hash blocks alone. Like every
file of this road it takes a cone under Johnson/Goal/ (through the sealed Johnson/IMR/ seats).
`falls_asks` itself is not called. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.AsksStated
import Johnson.P1K8R.BehindButHead

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

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

set_option maxHeartbeats 2000000 in
/-- **`firstAsks_stated_blocks` (Johnson/P1K8R/AsksStated.lean) WITH THREE PAYMENTS LAID IN**: in
its premise hLeft, in `StillAtZ Z Bs l s'`'s place, stands `HeardAtZ s'` AT THE HEAD's SEGMENT
ALONE: all else of `StillAtZ` follows from `WrapEnd`, which the frame's field hP' hands at our
blocks (`wrapEnd_of_handed`, Johnson/P1K8R/LastAtFrame.lean; `stillAtZ_of_heard`,
Johnson/P1K8R/BehindHeard.lean; `heardAtZ_of_head`, Johnson/P1K8R/BehindButHead.lean). All else as
there. -/
theorem firstAsks_head_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
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
      ShareLive s' ∧ LiveFore s' ∧ (l = 24 → HeardAtZ s'))
    (hp₁ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum + ((reps b).map (qF b)).sum ≤
        p₁ (0 + A.length))
    (hp₂ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = false →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum ≤ p₁ (0 + A.length)) :
    FirstAsks (F := descAt Z A₂ B₂ c) (_root_.Run.ckP .two) fs hm p₁ pre₁ e₁ x Xc
      (fallSeat P5J.At.links) markSeat PM qM (PWith Z c Bs Pr) qF reps :=
  firstAsks_stated_blocks hE hS hR O hOk fs hm p₁ x Xc PM qM Pr qF reps hcut cut hz hfs hseat hq0
    hM hPM hFr hqF hin hPr
    (fun A b b' B e hs hn fr a z s' h1 h2 h3 h4 y1 y2 hv hr l hl hA => by
      obtain ⟨g2, g3, g4⟩ := hLeft A b b' B e hs hn fr a z s' h1 h2 h3 h4 y1 y2 hv hr l hl hA
      have hall : c.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := by
        rw [cut, e]
        simp
      exact ⟨g2, g3,
        stillAtZ_of_heard hS hR O hOk hl (wrapEnd_of_handed hS hR O hl hall hA hr)
          (heardAtZ_of_head hS hR O hOk hl (wrapEnd_of_handed hS hR O hl hall hA hr) g4)⟩)
    hp₁ hp₂

end

end P1K8

#print axioms P1K8.firstAsks_head_blocks
