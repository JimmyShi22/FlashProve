-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FrontAtAsks.lean: THE SMALLNESS TEST's TWO FALLS IN THE HONEST SIDE's FRAME: THE
MEMBER OF `FirstAsks` UNDER THE DESCRIPTION's HEAD WITH THE BOUNDS FOR BOTH OF THAT TEST's FALLS
PAID AT ALL 25 SEGMENTS: hFr IS ASKED OF FALLS THAT ARE NEITHER OF THAT TEST's TWO AT THE STATED
NUMBERS. A definition and lemmas; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness,
soundness or hiding.

  `FrontFallAt`   a definition: a premise's form; the like of `ShareFallAt`
      (Johnson/P1K8R/LastAtAsks.lean)
  **`liveOf_of_last`**   liveOf_at_batch (Johnson/Desc/ProofFile/Honest/K8/FrontNumbers.lean): ONE
      CALL; `there_at_wrap` (Johnson/P1K8R/CountedAtRch.lean); `built_there` (BehindLast.lean);
      `symbolsLive_eq` (DebtsK8.lean); reach_raw (Johnson/Top/H0/Walk/Reach.lean)
  **`firstAsks_front`**   `firstAsks_all_live` (AsksAllLive.lean); `front_fallDebt_blocks`
      (DebtsK8.lean); `batch_rounds_are`, `one_of_fits`, `drop_split` (LastAtFrame.lean);
      `second_at_step` (SecondCount.lean); oneElem_bat (Johnson/Desc/K8/Honest/ChiTyped.lean);
      `fallDebt_mono` (LastAtAsks.lean)
Limits. A MEMBER UNDER SIXTEEN NAMED HYPOTHESES, AS IN Johnson/P1K8R/AsksAllLive.lean: NONE OF THEM
IS PROVED HERE OF ANYTHING; by reading, no lemma says it: they can be met together, emptily: the
content lies in the letters fs, hm, qM, qF. hFr IS WEAKER THAN THERE, NOT GONE: it stays asked of
every counted fall at a block that is neither of the smallness test's two: other kinds' authors'
matter. The first fall is met at the two stated numbers alone: a fall of that test at other numbers
stays under hFr. The bound is `front_fallDebt_blocks`'s, at strings of hash blocks, AND STANDS UNDER
THE MEMBER's OWN CONDITION ON THE STATE (`PWith`), which the member's field hP' has from the marks'
silence; hqF lifts it to the letter qF. The head h is a hypothesis; the full size alone. No number
is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.AsksAllLive
import Johnson.Desc.ProofFile.Honest.K8.FrontNumbers
import Johnson.P1K8R.DebtsK8

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
open ProofFile.Honest.K8 (k8ShareFall k8Second k8FrontFall k8ColsAt k8TauAt liveOf_at_batch)
open Iop
open scoped ENNReal

/-- The fall g is the smallness test's FIRST fall of a segment l, at the two numbers that
Johnson/Desc/ProofFile/Honest/K8/FallNumbers.lean states for l, and n is the number of that
segment's batching in the first chain's list. -/
def FrontFallAt (Bs : ProofFile.PureBase) (n : ℕ) (g : Fall S) : Prop :=
  ∃ l, l < 25 ∧ n = 14 * l + (if l = 24 then 11 else 9) ∧
    g = k8FrontFall l (if l = 24 then 1 else 0) (k8ColsAt Bs.G₀ l) (k8TauAt Bs.G₀ l)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

/-- **What the first fall's bound asks of the state (`liveOf`, Johnson/P1K8R/FrontFallHeld.lean)
follows from what the second fall's asks (`PLast`, LastAtFrame.lean)**, at the stated numbers:
liveOf_at_batch (Johnson/Desc/ProofFile/Honest/K8/FrontNumbers.lean) with its premises drawn out of
`PLast`: the state is reached; the test on the drawn matrix is one of `ShareLive`'s four. -/
theorem liveOf_of_last (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {fr : List Fmt.Drawn} {s' : S} (h : PLast Z c Bs l fr s') :
    liveOf (k8ColsAt Bs.G₀ l) (k8TauAt Bs.G₀ l) s' := by
  obtain ⟨w, hlive, -, -⟩ := h
  obtain ⟨tl, G, ht, hG⟩ := there_at_wrap hS hR O hOk hl w
  obtain ⟨zp, hw⟩ := w
  obtain ⟨Xl, e3⟩ := built_there hS hR O hl
  refine liveOf_at_batch hS hR O hl e3 (reach_raw hw) ht ?_
  rw [← symbolsLive_eq]
  exact (hlive tl G ht hG).2.2.2

set_option maxHeartbeats 4000000 in
/-- **`firstAsks_all_live` (Johnson/P1K8R/AsksAllLive.lean) WITH THE BOUND FOR THE SMALLNESS TEST's
FIRST FALL PAID TOO**: its premise hFr is asked of the counted falls that are neither of that test's
two at the block. At the first fall: `front_fallDebt_blocks` (Johnson/P1K8R/DebtsK8.lean), whose
condition on the state follows from the member's own (`liveOf_of_last`); the number by hqF. No new
premise. -/
theorem firstAsks_front {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
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
      ∀ g ∈ repsAt c.blocksInOrder fs b, ¬ ShareFallAt Bs (k8ShareAt Z Bs.G₀) A.length g →
      ¬ FrontFallAt Bs A.length g → ∀ dsb : List RDT,
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
  refine firstAsks_all_live h hB fs hm x Xc PM qM Pr qF Pv w₀ rc R hXc hmk hsub hsubK hsubA cut hfs
    hseat hq0 hM hPM ?_ hqF hPr
  intro A b b' B e hs hn g hg hns dsb hk
  by_cases hf : FrontFallAt Bs A.length g
  · obtain ⟨l, hl, hA, rfl⟩ := hf
    obtain ⟨Bs', base, O⟩ := h.laid.opened
    obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
    have hall : c.blocksInOrder = (A ++ b :: b' :: B) ++ [e₁] := by
      rw [cut, e]
    have hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b := by
      rw [← hA, hall]
      simp
    obtain ⟨b₀, p, -, hp, -⟩ := second_at_step h.scope h.reads O hl
    rw [batch_rounds_are h.scope h.reads O hl hb hp] at hk
    obtain ⟨d, rfl, e1, e2, e3⟩ := one_of_fits hk
    have h1 : OneElem d.entry d.kind := by
      rw [e1]
      exact oneElem_bat p d.kind e2 e3
    have hlog : d.entry.logN ≤ 64 := by
      rw [e1]
      exact Nat.zero_le _
    have D := front_fallDebt_blocks h.scope h.reads O hl b hb d h1 hlog 0 (k8ColsAt Bs'.G₀ l)
      (k8TauAt Bs'.G₀ l) (PWith Z c Bs' Pr b)
      (fun fr s' hP => liveOf_of_last h.scope h.reads O h.laid.planOk hl (hP.2 l hl hb))
    rw [← hA, drop_split hall] at D
    exact fallDebt_mono D (fun _ _ k => k) (hqF b _)
  · exact hFr A b b' B e hs hn g hg hns hf dsb hk

end

end P1K8

#print axioms P1K8.FrontFallAt
#print axioms P1K8.liveOf_of_last
#print axioms P1K8.firstAsks_front
