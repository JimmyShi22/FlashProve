-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/AsksAllLive.lean: THE SMALLNESS TEST's SECOND FALL IN THE HONEST SIDE's FRAME: THE
MEMBER OF `FirstAsks` UNDER THE DESCRIPTION's HEAD WITH `readsLive`, THE LAST TEST THAT THE SECOND
FALL's BOUND LAYS ON THE STATE, PAID AT ALL 25 SEGMENTS: THE PREMISE hLeft IS GONE. A lemma; NONE OF
THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.

  **`firstAsks_all_live`**   `firstAsks_head_live` (Johnson/P1K8R/AsksHeadLive.lean);
      `attLive_handed` (AttLiveAtFrame.lean); `depth_at_att` (DepthAtAtt.lean); H2K5.Door.planAt_all
      (Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean); reach_raw (Johnson/Top/H0/Walk/Reach.lean);
      the lines that turn what the field hands into the walk's own letters stand in AsksLooks.lean,
      AsksLayersLive.lean and AsksHeadLive.lean too
Limits. A MEMBER UNDER SIXTEEN NAMED HYPOTHESES: NONE OF THEM IS PROVED HERE OF ANYTHING. BY
READING, NO LEMMA SAYS IT: THEY CAN BE MET TOGETHER, EMPTILY (no fall counted; the prices at the top
of their range): SO THE CONTENT LIES IN THE LETTERS fs, hm, qM, qF, NOT IN THAT THE HYPOTHESES CAN
HOLD: h, hB, hXc, hmk, hsub, hsubK, hsubA, cut, hfs, hseat, hq0, hM, hPM, hFr, hqF, hPr. WHAT HAS
GONE IS hLeft. THE SMALLNESS TEST's FIRST FALL's BOUND AT THE 25 SEGMENTS STAYS IN hFr HERE:
`firstAsks_front` (Johnson/P1K8R/FrontAtAsks.lean) takes it out. hPr STILL NAMES THE STATE THAT THE
FIELD HANDS: it asks the caller's own letter Pr there, which hFr's debts of the other falls may
spend; at the letter that always holds it asks nothing. WHAT hLeft's GOING COST: three lists of
other authors' marks must be among those asked (a hundred, two, and twenty-four), and each mark owes
hseat and hM: hseat has each list's authors' own law without a hypothesis; hM IS EACH LIST's
AUTHORS' OWN MATTER, IN FILES THAT DO NOT LIE BENEATH THIS ONE AND THAT THIS FILE's AUTHOR HAS NOT
READ: at which numbers, and under which hypotheses, each list's debt stands is theirs to say. The
price of the silence is not evaluated here, and nothing says that it is below 1. The head h is a
hypothesis; the full size alone. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.AsksHeadLive
import Johnson.P1K8R.AttLiveAtFrame
import Johnson.P1K8R.DepthAtAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT WholeD)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open ProofFile.Honest.K3.Good (markK3 markOut k3Marks)
open ProofFile.Honest.K6 (part4Marks)
open ProofFile.Honest.K5 (k5Marks)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw reach_fold)
open ProofFile.Honest (Odds FallDebt KindFits Fall Mark MarkDebt FirstAsks firstAsks_cut fellBy silentQ
  fitMarks drawsFit walk groupOf localFall ChainAt Local fallSeat markSeat cut_first repsAt
  priceAt hin_reps hp₁_sum hp₂_sum places_nodup ChainProgress Mid marksQuiet Prover Ready at₁
  letter_starts letter_tree file_head hz_head)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

set_option maxHeartbeats 4000000 in
/-- **`firstAsks_head_live` (Johnson/P1K8R/AsksHeadLive.lean) WITH `readsLive` PAID AT THE TWELVE
ATTENTION SEGMENTS TOO: ITS PREMISE hLeft IS GONE: NO TEST THAT THE SECOND FALL's BOUND LAYS ON THE
STATE IS LEFT ASKED.** One premise comes in its stead: the marks of the sub-protocol "attention's
own rounds" are among those asked (hsubA). At l = 2 g + 1: `attLive_handed`
(Johnson/P1K8R/AttLiveAtFrame.lean) from the marks' silence, at the reached state that the field
hands; its sentence on public numbers by `depth_at_att` (DepthAtAtt.lean). hPr STILL NAMES THE STATE
HANDED: it asks the caller's own letter Pr there. -/
theorem firstAsks_all_live {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {x₀ : Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Pz D r Z Np c x₀)
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok Bs)
    (fs : List (Fall S)) (hm : List Mark) {pre₁ : List (Block S Claim)}
    {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Xc : List Fmt.Drawn → ChainAt S Claim (Local W₀ Rc ProofFile.Inst Tr) X₁)
    (PM : Block S Claim → List Fmt.Drawn → Prop) (qM : Block S Claim → Mark → ℝ≥0∞)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    {Ky X₀ : Type} (Pv : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X₁) (w₀ : W₀) (rc : Rc)
    (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (hXc : Xc = fun _ => at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) Pv w₀ rc x R)
    (hmk : ∀ mk ∈ part1Marks Z Bs.G₀, mk ∈ hm)
    (hsub : ∀ mk ∈ k3Marks Z Bs.G₀, mk ∈ hm) (hsubK : ∀ mk ∈ part4Marks Z Bs.G₀, mk ∈ hm)
    (hsubA : ∀ mk ∈ k5Marks Z Bs.G₀, mk ∈ hm)
    (cut : c.blocksInOrder = pre₁ ++ [e₁])
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
      ∀ g ∈ repsAt c.blocksInOrder fs b, ¬ ShareFallAt Bs (k8ShareAt Z Bs.G₀) A.length g → ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) g 0 b (b' :: B ++ [e₁]) dsb []
        (PWith Z c Bs Pr b) (qF b g))
    (hqF : ∀ b g, g.share.val ≤ qF b g)
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
      Pr b fr s') :
    FirstAsks (F := P5J.F0T OnBytes.secondHashFunction Z Np c) (_root_.Run.ckP .two) fs hm
      (priceAt pre₁ hm qM (repsAt c.blocksInOrder fs) qF) pre₁ e₁ x Xc
      (fallSeat P5J.At.links) markSeat PM qM (PWith Z c Bs Pr) qF (repsAt c.blocksInOrder fs) := by
  refine firstAsks_head_live h hB fs hm x Xc PM qM Pr qF Pv w₀ rc R hXc hmk hsub hsubK cut hfs hseat
    hq0 hM hPM hFr hqF hPr ?_
  intro A b b' B e hs hn fr a z s' h1 h2 h3 h4 y1 y2 hv hr l hl hA hodd
  obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
  have hg : g < 12 := by omega
  have hA' : A.length = 14 * (2 * g + 1) + 9 := by
    rw [hA, if_neg (by omega)]
  obtain ⟨pl, ea⟩ := H2K5.Door.planAt_all h hg
  have hall : c.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := by
    rw [cut, e]
    simp
  obtain ⟨m₀, hm₀, ha⟩ :=
    letter_starts (P5J.F0T OnBytes.secondHashFunction Z Np c) Pv w₀ rc x R Xc hXc _ a y1
  have hft := letter_tree (P5J.F0T OnBytes.secondHashFunction Z Np c) Pv w₀ rc x R Xc hXc (fr.take 0)
  have htk : pre₁.take (0 + A.length) = A := by
    rw [e, Nat.zero_add]
    exact List.take_left' rfl
  have hq : marksQuiet (hm ++ fitMarks pre₁) A [] fr = true := by
    have h4' : marksQuiet (hm ++ fitMarks pre₁) (pre₁.take (0 + A.length)) (fr.take 0)
      (fr.drop 0) = true := h4
    rw [htk] at h4'
    exact h4'
  have hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ hm ++ fitMarks pre₁ := fun d hd =>
    List.mem_append_right _ (List.mem_map.2
      ⟨d, by rw [e]; exact List.mem_append_left _ hd, rfl⟩)
  have hr' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (x.pub, s') := by
    have k := reach_raw (hr hn)
    rw [hA'] at k
    exact k
  obtain ⟨tl, ht, hlive⟩ := attLive_handed h Bs.G₀ hB hg ea (depth_at_att h hg ea)
    (hm ++ fitMarks pre₁) (fun mk hk => List.mem_append_left _ (hsub mk hk))
    (fun mk hk => List.mem_append_left _ (hsubA mk hk)) hall hfit hA'
    (List.length_pos_iff.2 hn) _ hft hm₀ ha (by simpa using h2) hq y2 hv hr'
  intro tl' F' ht' _
  obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans ht')
  exact hlive

end

end P1K8

#print axioms P1K8.firstAsks_all_live
