-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/HidAtPlan.lean: THE TOWER'S LETTER H (`hidAtSeat`, MeansQ.lean) WITH ITS THREE OPEN
    LETTERS CLOSED: s · seat · f.
  s := `Meaning.sizesOf X` (Johnson/Goal/Meaning/HidPlan.lean: the library's own sizes off the 25
      plans) ·
  seat := `Meaning.seatsOf X (sizesOf X) layout num` (Johnson/Goal/Meaning/HidSeatsOf.lean: the
      seats off the plan's
    layout, a borrowed array at its OWNER's seat) · f := `tokVOf` (TokTerms.lean), at Tok := ℕ.
  `hidAtPlan`: that term, fenced by type with the test `laidThere` (HidSeatsOf.lean),
      `SeatsNamed`,
    `GroupsSeated`. STILL LETTERS IN IT, ALL OF THE PLAN: X · cs · arr · ms · N · layout · num
      (link, message in
    the link ↦ the witness's number) · req · dec.
  `seatsOne_seatsOf`: IN SCOPE reader's and owner's seats are one at the 24 pairs (by
      `seatsOf_eq`,
    `seatsOne_of_planFit`, `planFit_of_core`, `follows_of_core`).
  `sizesOf_beyond`: from segment 25 on the library's sizes have no matrix (what `seatsNamed_of_C`
      asks as hK).
  `sizesFit_sizesOf`: IN SCOPE the test on sizes says yes at sizesOf X.
  **`words_at_plan`**: IN SCOPE: `SeatsNamed`, `GroupsSeated`, `PadsFree` at these letters give the
      24 equations at
    the tower's own reading of EVERY witness: of `words_ownQ`'s five public conditions two are
        theorems here.
  `seatsOf_is_seatBy`, `words_at_plan_by`: in scope seatsOf … IS seatBy (fLay layout
      num) …, at all
    segments' numbers; so the 24 equations follow from SeatsNamed | PadsFree in the form in which
        the cheap tests of
    two other groups of files end.
Limits. NOTHING HERE PINS num TO arr
    (SeatsNamed alone does not):
    `SeatsNamed` says only that
        the number which a seat
    names has just one tenant in the reader's own group: at a num that names ANOTHER message of that
        group it
    still says yes, and the reading takes the wrong message in silence. What pins num is its own
        make against
    arr's: "arr at the seat of the message born at link l as its k-th = num l k" : at arr := arrOf
        ps and
    num := numOfPlan ps, over one planner's list ps, that is `arrOf_is_num`
        (Johnson/P5T/NumOfPlan.lean): see
    HidAtList.lean. layout is a letter, tied to no description here: at the seated term it is the
        first chain's own.
    lay is any. The full size alone.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Meaning.HidSeatsOf
import Johnson.Goal.Meaning.HidPlanFit
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.Goal.Meaning.ScopeCore
import Johnson.P5J.WordsAtQ
import Johnson.P5J.TokTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Layer (matIx)
open OnBytes.Params (ReqLayout)
open Cb.Pv.Tail (Size)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (SeatsNamed GroupsSeated MsgT Mem)

/-- **H WITH s · seat · f CLOSED.** THREE FENCES BY TYPE: the term cannot
    be formed where
the layout's reader gives nothing at an entry (so seatsOf's silent (0, 0, 0) is read nowhere within
    the sizes:
`seat_of_laidThere`), where a named number has not just one tenant in the reader's own
    group, or
where a group's seat is no member's. -/
noncomputable def hidAtPlan (X : Model.Verify.Public) {P Cells : Type} {rows cols : ℕ}
    (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (layout : ReqLayout)
    (num : ℕ → ℕ → ℕ) (req : P × TS → TReq)
    (dec : P × TS → Strs → Option (Fin rows → Fin cols → GE))
    (_hL : laidThere X (sizesOf X) layout = true)
    (hN : SeatsNamed arr N (sizesOf X) (seatsOf X (sizesOf X) layout num))
    (hG : GroupsSeated ms N) : HidAt X P (Wit Cells ℕ MsgT) rows cols :=
  hidAtSeat X cs arr ms N (sizesOf X) (seatsOf X (sizesOf X) layout num) tokVOf req dec hN hG

/-- From segment 25 on the library's own sizes have no matrix. -/
theorem sizesOf_beyond (X : Model.Verify.Public) (k : ℕ) (hk : 25 ≤ k) : (sizesOf X k).NM = 0 := by
  unfold Meaning.sizesOf Meaning.tlAt
  rw [if_pos (by omega)]
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- In scope the test on sizes says yes at the library's own sizes. -/
theorem sizesFit_sizesOf (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : sizesFit X (sizesOf X) = true :=
  sizesFit_of_planFit (follows_of_core h (Hd.core_of_scope hZ hR h))
    (planFit_of_core h (Hd.core_of_scope hZ hR h))

/-- **In scope reader's and owner's seats off the layout are one, at the 24 pairs.** -/
theorem seatsOne_seatsOf (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (layout : ReqLayout) (num : ℕ → ℕ → ℕ) :
    SeatsOne X (sizesOf X) (seatsOf X (sizesOf X) layout num) := by
  have C := Hd.core_of_scope hZ hR h
  have F := follows_of_core h C
  have o := seatsOne_of_planFit (s := sizesOf X) (fLay layout num) (planFit_of_core h C)
  have e : ∀ k, k < 25 → seatsOf X (sizesOf X) layout num k =
      seatBy (fLay layout num) X (sizesOf X) k := fun k hk => seatsOf_eq h C F layout num hk
  refine ⟨fun g h0 hg => ?_, fun g hg => ?_, ?_⟩
  · rw [e (2 * g) (by omega), e (2 * (g - 1)) (by omega)]
    exact o.ff g h0 hg
  · rw [e (2 * g + 1) (by omega), e (2 * g) (by omega)]
    exact o.att g hg
  · rw [e 24 (by omega), e 22 (by omega)]
    exact o.head

/-- **IN SCOPE THE SEATS OFF THE LAYOUT ARE THE ONE FUNCTION OF THE LABEL, AT ALL SEGMENTS'
    NUMBERS**:
below 25 by `seatsOf_eq` (Johnson/Goal/Meaning/HidSeatsOf.lean); from 25 on there
    is no matrix. So whatever is shown at
`seatBy (fLay layout num) X (sizesOf X)` (the form in which the cheap tests of two other groups of
    files end) holds at
`seatsOf X (sizesOf X) layout num`. -/
theorem seatsOf_is_seatBy (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (layout : ReqLayout) (num : ℕ → ℕ → ℕ) :
    seatsOf X (sizesOf X) layout num = seatBy (fLay layout num) X (sizesOf X) := by
  have C := Hd.core_of_scope hZ hR h
  have F := follows_of_core h C
  funext k
  by_cases hk : k < 25
  · exact seatsOf_eq h C F layout num hk
  · funext μ
    exact absurd (sizesOf_beyond X k (by omega) ▸ μ.isLt : μ.val < 0) (Nat.not_lt_zero _)

/-- **THE 24 EQUATIONS AT THE CLOSED LETTERS, AT EVERY WITNESS, IN SCOPE.** -/
theorem words_at_plan {Cells Tok : Type} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) {cs : OnBytes.Codes}
    {arr : ℕ → ℕ → ℕ} {ms : List Mem} {N : Numbers} (layout : ReqLayout) (num : ℕ → ℕ → ℕ)
    (hN : SeatsNamed arr N (sizesOf X) (seatsOf X (sizesOf X) layout num))
    (hG : GroupsSeated ms N)
    (hP : PadsFree cs arr ms N (sizesOf X) (seatsOf X (sizesOf X) layout num) X)
    (w : Wit Cells Tok MsgT) :
    OneWord X (ownQ cs arr ms N (sizesOf X) (seatsOf X (sizesOf X) layout num) w) ∧
      HeadWord X (ownQ cs arr ms N (sizesOf X) (seatsOf X (sizesOf X) layout num) w) :=
  words_ownQ (sizesFit_sizesOf hZ hR h) (seatsOne_seatsOf hZ hR h layout num) hN hG hP w

/-- The same from the two conditions in the form in which the cheap tests end. -/
theorem words_at_plan_by {Cells Tok : Type} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) {cs : OnBytes.Codes}
    {arr : ℕ → ℕ → ℕ} {ms : List Mem} {N : Numbers} (layout : ReqLayout) (num : ℕ → ℕ → ℕ)
    (hN : SeatsNamed arr N (sizesOf X) (seatBy (fLay layout num) X (sizesOf X)))
    (hG : GroupsSeated ms N)
    (hP : PadsFree cs arr ms N (sizesOf X) (seatBy (fLay layout num) X (sizesOf X)) X)
    (w : Wit Cells Tok MsgT) :
    OneWord X (ownQ cs arr ms N (sizesOf X) (seatsOf X (sizesOf X) layout num) w) ∧
      HeadWord X (ownQ cs arr ms N (sizesOf X) (seatsOf X (sizesOf X) layout num) w) := by
  rw [seatsOf_is_seatBy hZ hR h layout num]
  exact words_ownQ (sizesFit_sizesOf hZ hR h)
    (seatsOne_of_planFit (fLay layout num) (planFit_of_core h (Hd.core_of_scope hZ hR h))) hN hG hP
    w

end

end P5J

#print axioms P5J.sizesOf_beyond
#print axioms P5J.sizesFit_sizesOf
#print axioms P5J.seatsOne_seatsOf
#print axioms P5J.words_at_plan
#print axioms P5J.seatsOf_is_seatBy
#print axioms P5J.words_at_plan_by
