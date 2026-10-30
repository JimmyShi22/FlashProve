-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/MarksAtHead.lean: THE HONEST SIDE's FRAME: THE TWO FIELDS ON MARKS THAT THE FRAME's
BOUND ON THE FIRST CHAIN's FALLS ASKS (hseat, hM), AT THE FRAME's AUTHORS' OWN LIST `marksHead`
(Johnson/Desc/ProofFile/Honest/Law/MarksHead.lean): THEIR OWN SPLITS BY AUTHOR, CALLED AT THE
AUTHORS' LAWS THAT EXIST. TYPED ON THE FRAME's AUTHORS' WORD. Lemmas; NONE OF THE LIBRARY's GOALS. A
joining. Nothing on completeness, soundness or hiding.

  **`marksHead_seated`**   marksHead_seat_k4 (Johnson/Desc/ProofFile/Honest/Law/MarksHeadK4.lean)
      at `part1Marks_seat` (Johnson/P1K8R/Part1Marks.lean), k3Marks_seat
      (Honest/K3/Good/MarksHead.lean), k5Marks_seat (Honest/K5/Law/MarksListLaw.lean)
  `part1_kinds`, `k5_kinds`   off the list's text; off k5Marks_place (MarksListLaw.lean)
  **`marksHead_hM_left`**   marksHead_hM (MarksHead.lean) AT THE KIT Run.ckP .two, at
      `part1_hM_head` (Part1Marks.lean), k3Marks_kind (K3/Good/MarksHead.lean), k4_kinds
      (MarksHeadK4.lean), k4_markDebt_form (Honest/K4/Law/MarkForm.lean), k5Marks_hM
      (Honest/K5/Law/MarksDebt.lean); LPFK9.places_nodup (Johnson/LPFK9R/ToldInScope.lean)
Why they stand on `marksHead` and not on the bound itself: the bound's statement may turn; hM joins
list by list (hM_append, Johnson/Desc/ProofFile/Honest/Law/CoverMarksJoin.lean).
Limits. `marksHead_hM_left` STANDS AT ONE KIT OF CHALLENGES, Run.ckP .two: the kit is a letter in
the frame's bounds, and the authors' laws join only where all stand at one kit; at typed challenges
nothing is said. hK3 AND hK6 ARE HYPOTHESES (in marksHead_hM's own letters: h with the subscripts 3
and 6): the lookups' marks, each at its share's numerator times the letter kapL; the output head's
own rounds' marks, at kapH. (For hK6 the frame's authors have h6_blocks,
Johnson/Desc/ProofFile/Honest/Law/MarksHeadK6Blocks.lean, which sets kapH; it is not imported here.)
EACH AUTHOR's LAW COMES WITH ITS OWN LIMITS: the law on one round's messages is named in MarkDebt,
not derived; k4_markDebt_form is, by its authors' word, not paid outright. No share is evaluated:
how large the marks' numbers are together is not said. The head h and hB are hypotheses; the full
size alone. hPM, and all that the bound asks on falls, is not spoken of. One option is raised, for
`marksHead_hM_left` alone (maxHeartbeats). One tactic that searches: simp, once.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Law.MarksHeadK4
import Johnson.Desc.ProofFile.Honest.K3.Good.MarksHead
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkForm
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksDebt
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksListLaw
import Johnson.P1K8R.Part1Marks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT WholeD)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open ProofFile.Honest (Mark MarkDebt KindFits markSeat marksHead qMHead marksHead_hM marksHead_seat_k4
  k4_kinds)
open scoped ENNReal

/-- **hseat AT THE LIST AS IT STANDS: EVERY MARK OF `marksHead` STANDS AT A MARK's SEAT.** No
hypothesis. -/
theorem marksHead_seated (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    ∀ mk ∈ marksHead Zp G₀, markSeat mk.place = true :=
  marksHead_seat_k4 (part1Marks_seat Zp G₀)
    (fun mk hm => ProofFile.Honest.K3.Good.k3Marks_seat Zp G₀ mk hm) (ProofFile.Honest.K5.k5Marks_seat Zp G₀)

/-- No mark of our own list stands at a place of the kind K3 or of the kind K6. -/
theorem part1_kinds (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    ∀ mk ∈ part1Marks Zp G₀, mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6 := by
  intro mk hm
  unfold part1Marks at hm
  rcases List.mem_append.1 hm with hm | hm
  · obtain ⟨l, -, hl⟩ := List.mem_filterMap.1 hm
    obtain ⟨X, -, rfl⟩ := Option.map_eq_some_iff.1 hl
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have e' : KindName.K8 = KindName.K3 := e
      cases e'
    · have e' : KindName.K8 = KindName.K6 := e
      cases e'
  · obtain rfl := List.mem_singleton.1 hm
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have e' : KindName.K11 = KindName.K3 := e
      cases e'
    · have e' : KindName.K11 = KindName.K6 := e
      cases e'

/-- No mark of the attention segments' own rounds stands at a place of the kind K3 or K6. -/
theorem k5_kinds (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    ∀ mk ∈ ProofFile.Honest.K5.k5Marks Zp G₀,
      mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6 := by
  intro mk hm
  obtain ⟨l, e⟩ := ProofFile.Honest.K5.k5Marks_place Zp G₀ mk hm
  rw [e]
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have e' : KindName.K5 = KindName.K3 := e
    cases e'
  · have e' : KindName.K5 = KindName.K6 := e
    cases e'

set_option maxHeartbeats 4000000 in
/-- **hM AT THE LIST AS IT STANDS, AT THE KIT WHOSE CHALLENGES ARE STRINGS OF HASH BLOCKS (Run.ckP
.two), BY OWNER**: under the head and hB, at the ground Bs.G₀. HAD, EACH WITH ITS AUTHORS' LIMITS:
our own list's marks (`part1_hM_head`); the wider marks of the feed-forward layers' own rounds
(k4_markDebt_form); those of the attention segments' own rounds (k5Marks_hM). STILL ASKED: hK3: the
lookups' marks; hK6: those of the output head's own rounds. BOTH LETTERS OF qMHead ARE FREE. -/
theorem marksHead_hM_left {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (kapL kapH : ℝ≥0∞)
    {pre₁ : List (Block P5J.TS ProofFile.Cl)} {e₁ : Block P5J.TS ProofFile.Cl}
    (cut : cF.blocksInOrder = pre₁ ++ [e₁]) {PM : Block P5J.TS ProofFile.Cl → List Fmt.Drawn → Prop}
    (hK3 : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (ProofFile.Honest.K3.Good.k3Marks Zp Bs.G₀).filter (fun m => m.place == b.place),
      ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) ((mk.share.num : ℝ≥0∞) * kapL))
    (hK6 : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (ProofFile.Honest.K6.part4Marks Zp Bs.G₀).filter (fun m => m.place == b.place),
      ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) ((mk.share.num : ℝ≥0∞) * kapH)) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (marksHead Zp Bs.G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) (qMHead kapL kapH b mk) := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  refine marksHead_hM (_root_.Run.ckP .two) kapL kapH (part1_kinds _ _) ?_
    (fun mk hm => ProofFile.Honest.K3.Good.k3Marks_kind _ _ mk hm) hK3 k4_kinds
    (ProofFile.Honest.K4.k4_markDebt_form h.scope h.reads O (LPFK9.places_nodup h.scope h.reads O) cut PM)
    (k5_kinds _ _) (ProofFile.Honest.K5.k5Marks_hM h hB cut PM) hK6
  intro A b b' B e mk hmk dsb hk
  have hb : cF.blocksInOrder[A.length]? = some b := by
    rw [cut, e]
    simp
  exact part1_hM_head h hB hb (PM b) mk hmk dsb hk

end P1K8

#print axioms P1K8.marksHead_seated
#print axioms P1K8.part1_kinds
#print axioms P1K8.k5_kinds
#print axioms P1K8.marksHead_hM_left
