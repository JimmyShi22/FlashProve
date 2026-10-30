-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/CountedAtOwn.lean: THE SMALLNESS TEST's TWO FALLS IN THE HONEST SIDE's FRAME: AMONG
THE MEMBERS WITH A ROUND EACH OF THAT TEST's FIFTY RECORDS IS COUNTED AT ITS OWN SEGMENT's BATCHING
ALONE; SO THE MEMBER OF `FirstAsks` ASKS hFr OF THE COUNTED FALLS THAT ARE NONE OF THE FIFTY. A
definition and lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding.

  `frame_roundless`   P1L20.Row.cut_frames (Johnson/AtFull/Desc/Lots/FramesRounds.lean): a sealed
      evaluation over the 358 written rows; cut_row
      (Johnson/Desc/ProofFile/Honest/Law/CoverCut.lean)
  `K8Fall`   a definition: a premise's form
  **`counted_at_own`**   groupPlaces_at (Johnson/Desc/ProofFile/Honest/Law/CoverReps.lean);
      `batch_place`, `quiet_place` (Johnson/P1K8R/PlacesAtFlat.lean); `second_at_step`
      (SecondCount.lean); `batch_rounds_are` (LastAtFrame.lean)
  **`firstAsks_own`**   `firstAsks_front` (FrontAtAsks.lean); file_head
      (Johnson/Desc/ProofFile/Honest/Law/CoverHeadFile.lean); places_nodup (Cuts.lean)
Kin. Sealed, beside the one that is called: IM.frame_of (Johnson/IMR/FrameSeat.lean): at each l < 25
the member one behind the batching has no round, by its number, with no evaluation: with
`quiet_place` it gives what `counted_at_own`'s second case takes from `frame_roundless`;
IM.rounds_of_lot (Johnson/IMR/FlatCases.lean): four arms on a member's rounds; met behind this
file's typing. And: cut_frames_but_last, frames_rounds (Johnson/AtFull/Desc/Lots/FramesRounds.lean)
and frames_noRounds (Johnson/Desc/Plain/Leaves/PureHears.lean): no round at the written rows but the
last; at the blocks of the frames' lot; at what a seat takes for a role of that kind: none speaks of
a member of the chain's list by its place. The frame's authors' cut_rounds_yes, round_cut
(CoverCut.lean): a member at a mark's seat, or at a fall's seat of another kind than `frame`, has a
round: the other half. mem_repsAt (CoverReps.lean): a fall at a place of the group is counted:
`counted_at_own` goes the other way, at two places a segment. `length_of_cut`
(Johnson/P1K8R/LastAtAsks.lean): the number from the member. On places alone, the frame's authors':
seat_front (Johnson/Desc/ProofFile/Honest/Law/Rule/SeatsFacts.lean): in the written list of places,
if `fallSeat` says yes at number i + 1 and the kind there is `frame`, then it says yes at number i,
and the kind there is K9; fallSeat_frame (CoverSeats.lean): which piece of a segment such a seat is.
Limits. A MEMBER UNDER SIXTEEN NAMED HYPOTHESES, AS IN Johnson/P1K8R/FrontAtAsks.lean: NONE OF THEM
IS PROVED HERE OF ANYTHING; by reading, no lemma says it: they can be met together, emptily. hFr is
weaker than there, not gone: it stays asked of every counted fall that is none of the fifty: other
kinds' authors' matter; a fall of the smallness test at other numbers than the stated ones is none
of the fifty. `frame_roundless` rests on an evaluation over one written list: the full size alone.
The head h is a hypothesis. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.FrontAtAsks
import Johnson.P1K8R.PlacesAtFlat
import Johnson.Desc.ProofFile.Honest.Law.CoverCut
import Johnson.Desc.ProofFile.Honest.Law.CoverReps
import Johnson.AtFull.Desc.Lots.FramesRounds

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
open ProofFile.Honest.K8 (k8ShareFall k8Second k8FrontFall k8ColsAt k8TauAt batchPlace quietPlace)
open ProofFile.Honest (groupPlaces groupPlaces_at cut_row)
open Iop
open scoped ENNReal

/-- A member of the kind `frame` that stands in a segment has no round: by the sealed evaluation
P1L20.Row.cut_frames (Johnson/AtFull/Desc/Lots/FramesRounds.lean): of the written cut's rows of that
kind one alone counts a round, and it stands in no segment. -/
theorem frame_roundless {T Cl : Type} {all : List (Block T Cl)}
    (hcut : cutOf all = cutFirstFull) : ∀ b ∈ all, b.place.kind = KindName.frame →
      b.place.link ≠ none → b.rounds = [] := by
  intro b hb h1 h2
  by_contra hne
  have hlen : b.rounds.length ≠ 0 := fun e => hne (List.eq_nil_of_length_eq_zero e)
  have hm : (b.name, b.place.link, b.rounds.length) ∈
      ((cutFirstFull.filter fun r => r.2.1.kind == KindName.frame && r.2.2.1 != 0).map
        fun r => (r.1, r.2.1.link, r.2.2.1)) :=
    List.mem_map.2 ⟨_, List.mem_filter.2 ⟨cut_row hcut hb, by
      show (b.place.kind == KindName.frame && b.rounds.length != 0) = true
      rw [Bool.and_eq_true]
      exact ⟨beq_iff_eq.2 h1, bne_iff_ne.2 hlen⟩⟩, rfl⟩
  rw [P1L20.Row.cut_frames.2] at hm
  exact h2 (Prod.mk.inj (Prod.mk.inj (List.mem_singleton.1 hm)).2).1

/-- **The fall g is one of the smallness test's fifty records**: the first or the second fall of a
segment l, at the numbers that Johnson/Desc/ProofFile/Honest/K8/FallNumbers.lean states for l. No
number of a member stands in it. -/
def K8Fall (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (g : Fall S) : Prop :=
  ∃ l, l < 25 ∧
    (g = k8FrontFall l (if l = 24 then 1 else 0) (k8ColsAt Bs.G₀ l) (k8TauAt Bs.G₀ l) ∨
      ∃ X, Bs.G₀.built.toList[l]? = some X ∧
        g = k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) (k8ShareAt Z Bs.G₀ l))

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

/-- **A FALL THAT STANDS AT A SEGMENT's BATCHING, OR AT THE MEMBER WITHOUT A ROUND BEHIND IT, IS
COUNTED AT THAT BATCHING ALONE**: where it is counted (`repsAt`,
Johnson/Desc/ProofFile/Honest/Law/CoverReps.lean) at a member b with a round, b is the segment's
batching. hcut, hnd: the written cut and the distinct places, which the head gives. -/
theorem counted_at_own (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) (hnd : (c.blocksInOrder.map (·.place)).Nodup)
    {A t : List (Block S Claim)} {b : Block S Claim} (hall : c.blocksInOrder = A ++ b :: t)
    (hn : b.rounds ≠ []) {fs : List (Fall S)}
    {g : Fall S} (hg : g ∈ repsAt c.blocksInOrder fs b) {l : ℕ} (hl : l < 25)
    (hp : g.place = batchPlace l (if l = 24 then 1 else 0) ∨
      g.place = quietPlace l (if l = 24 then 1 else 0)) :
    A.length = 14 * l + (if l = 24 then 11 else 9) := by
  have hm : g.place ∈ groupPlaces c.blocksInOrder b.place := of_decide_eq_true (List.mem_filter.1 hg).2
  rw [groupPlaces_at hnd hall] at hm
  obtain ⟨d, hd, hdp⟩ := List.mem_map.1 hm
  obtain ⟨r, hr⟩ := List.takeWhile_prefix (fun d : Block S Claim => d.rounds.isEmpty) (l := t)
  have hW : ∀ w ∈ t.takeWhile (fun d : Block S Claim => d.rounds.isEmpty), w.rounds = [] := by
    intro w hw
    exact List.isEmpty_iff.1
      (List.mem_takeWhile_imp (p := fun d : Block S Claim => d.rounds.isEmpty) hw)
  obtain ⟨b₀, p, hb₀, hp₀, -⟩ := second_at_step hS hR O hl
  have hb₀r : b₀.rounds ≠ [] := by
    rw [batch_rounds_are hS hR O hl hb₀ hp₀]
    exact List.cons_ne_nil _ _
  have hAb : c.blocksInOrder[A.length]? = some b := by
    rw [hall]
    simp
  unfold groupOf at hd
  rcases List.mem_cons.1 hd with e | hd
  · rw [e] at hdp
    rcases hp with hp | hp
    · exact batch_place hS hR O hl (by
        rw [hAb]
        exact congrArg some (hdp.trans hp))
    · exfalso
      have hk : b.place.kind = KindName.frame := by
        rw [hdp, hp]
        rfl
      have hlk : b.place.link ≠ none := by
        rw [hdp, hp]
        exact fun e => nomatch e
      exact hn (frame_roundless hcut b (by rw [hall]; simp) hk hlk)
  · obtain ⟨W₁, W₂, hsplit⟩ := List.append_of_mem hd
    have hflat : c.blocksInOrder = (A ++ b :: W₁) ++ d :: (W₂ ++ r) := by
      rw [hall, ← hr, hsplit]
      simp
    have eL : (A ++ b :: W₁).length = A.length + (W₁.length + 1) := by
      rw [List.length_append, List.length_cons]
    have hdi : c.blocksInOrder[(A ++ b :: W₁).length]? = some d := by
      rw [hflat]
      simp
    rcases hp with hp | hp
    · exfalso
      have e := batch_place hS hR O hl (n := (A ++ b :: W₁).length) (by
        rw [hdi]
        exact congrArg some (hdp.trans hp))
      rw [e] at hdi
      obtain rfl : b₀ = d := Option.some.inj (hb₀.symm.trans hdi)
      exact hb₀r (hW _ hd)
    · have e := quiet_place hS hR O hl (n := (A ++ b :: W₁).length) (by
        rw [hdi]
        exact congrArg some (hdp.trans hp))
      by_cases h0 : W₁.length = 0
      · omega
      · exfalso
        have hflat2 : c.blocksInOrder = (A ++ [b]) ++ (W₁ ++ d :: (W₂ ++ r)) := by
          rw [hflat]
          simp
        have eL2 : (A ++ [b]).length = A.length + 1 := by
          rw [List.length_append]
          rfl
        have k := hb₀
        rw [hflat2, List.getElem?_append_right (by omega),
          List.getElem?_append_left (by omega)] at k
        have hw : b₀ ∈ t.takeWhile (fun d : Block S Claim => d.rounds.isEmpty) := by
          rw [hsplit]
          exact List.mem_append_left _ (List.mem_of_getElem? k)
        exact hb₀r (hW _ hw)

set_option maxHeartbeats 4000000 in
/-- **`firstAsks_front` (Johnson/P1K8R/FrontAtAsks.lean) WITH hFr ASKED OF THE COUNTED FALLS THAT
ARE NONE OF THE SMALLNESS TEST's FIFTY RECORDS**: the number of the member is gone from that
premise: by `counted_at_own` such a record, where it is counted, is counted at its own batching, and
there the member has its bound. No new premise. -/
theorem firstAsks_own {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
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
      ∀ g ∈ repsAt c.blocksInOrder fs b, ¬ K8Fall Z Bs g → ∀ dsb : List RDT,
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
  refine firstAsks_front h hB fs hm x Xc PM qM Pr qF Pv w₀ rc R hXc hmk hsub hsubK hsubA cut hfs
    hseat hq0 hM hPM ?_ hqF hPr
  intro A b b' B e hs hn g hg hns hnf dsb hk
  refine hFr A b b' B e hs hn g hg ?_ dsb hk
  rintro ⟨l, hl, hgl⟩
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨-, hpl, hcut⟩ := file_head h.toAtMg
  have hall : c.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := by
    rw [cut, e]
    simp
  rcases hgl with hgl | ⟨X, hX, hgl⟩
  · exact hnf ⟨l, hl, counted_at_own h.scope h.reads O hcut (places_nodup hpl).1 hall hn hg hl
      (Or.inl (by rw [hgl]; rfl)), hgl⟩
  · exact hns ⟨l, X, hl, counted_at_own h.scope h.reads O hcut (places_nodup hpl).1 hall hn hg hl
      (Or.inr (by rw [hgl]; rfl)), hX, hgl⟩

end

end P1K8

#print axioms P1K8.frame_roundless
#print axioms P1K8.K8Fall
#print axioms P1K8.counted_at_own
#print axioms P1K8.firstAsks_own
