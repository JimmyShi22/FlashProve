-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.AccKGiven
import Johnson.Desc.K12.Law.AccKSeatsAll
/-
Johnson/Desc/K12/Law/AccKGivenAtCourse.lean: THE GIVEN FORM AT A SEAT: from AtSeatAll (Johnson/Desc/K12/Law/AccKAtCourseAll.lean: what a yes of a written description's decision gives at a seat of the proximity test) to accK_of_view (Johnson/Desc/K12/Law/AccKGiven.lean): FOR EVERY chain c, tables W and transcript τ THAT ARE GIVEN: if the seat's stretch of the view and the columns that the fold hands the seat are what τ and W show (ViewOf), and τ's tests of work pass, THEN accK SAYS YES AT τ, at the record that the door lays of the run's own record. NO «THERE IS» ON τ OR W. A TOOL CARRIED TO THE SEAT, NO LAW OF THE KIND (see «HOW THIN» below). NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS: ONE CALL.
  GivenAt p F t0 r0 rs' cols     ∀ c ts W τ, ViewOf p F r0 c ts W τ rs' cols → τ's work passes → accK p F t0 r0 c ts W τ = true.
  givenAt_of_step      the kind's block's step's yes at (t0, r0 :: rs', cols) ⇒ GivenAt: accK_of_view, its letters bound.
  atSeatAll_given      AtSeatAll at a cut with a seat ⇒ its whole conclusion AND GivenAt at the same m · t0 · r0 · rs' · cols.
  run_given            F.runEnd x v₁ v₂ v₃ = .ok e · early · one answer · the first chain's flat list is pre ++ B :: l with B a seat ⇒ m and cols are the fold's over pre from F's first record, the first view's rounds (the seal's behind them) and its opened columns · enter m = .ok t0 · the seat's stretch is r0 :: rs' · GivenAt p 0 t0 r0 rs' cols. (The two other chains: by atSeatAll_given at run_atSeat_all's other conjuncts.)
  yesConst_viewOf | yesOwn_viewOf     the ∃-tops LAID ONTO THE GIVEN FORM: the first and the third conjunct behind «∃ τ» in YesConst | YesOwn ARE ViewOf p F r0 c D.ts ‹the top's own tables› τ rs' cols: by ⟨t1, t4⟩.
HOW THIN: accK_of_view | accK_iff_view IS THIN BY ITS MAKE: accK is by definition the running step at the written view and the work's test; the lemma is that definition up to sealed digests and spare columns; IT HOLDS OF EVERY BLOCK: «a step that always refuses meets it; one that checks nothing meets it»: A TOOL, NO LAW OF proximityTestKind. THE WEIGHT LIES IN ViewOf, A PREMISE THAT NOBODY PAYS FROM BYTES, in τ's work, which no view shows, and in accK_acc | accK_acc_tr. THE SAME HOLDS OF GivenAt AND run_given: what they add to that tool is the fold's and the door's carrying (Johnson/Desc/K12/Law/CanonAtFold.lean · inside_step, Johnson/Top/H0/StepLaws/StepLaws.lean), which hold of every block behind a door too; of the kind's own text they spend only that the stretch has a first round.
READ BACKWARDS, UNDER THE SAME PREMISES (the list holds a seat at that cut · early · one answer): where accK says no at a given τ and W whose work passes and which show the seat's stretch and columns, the description's decision does not say yes. That is the shape in which a proof of soundness would spend it; NONE IS GIVEN HERE.
No sorry and no axiom of our own stands in this file.
NO MEMBER AT A REAL p. ViewOf has a member at every τ and W (viewOf_written, AccKGiven.lean: the written view).
LIMITS. (1) THAT A VIEW FROM BYTES IS ViewOf OF THE GAME's τ AND W IS NOT HERE: it is the reading's (the trees' binding; the hash as an oracle). (2) τ's work comes from outside the block: a premise inside GivenAt. (3) "BAT"'s own round is outside τ: r0 is handed to accK as shown. (4) Nothing carries Doomed: no chance is named. (5) That a written description's list holds the seat: the premise hb.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters)

/-- The given form at a record, a stretch and columns: no «there is». -/
def GivenAt (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn) :
    Prop :=
  ∀ {s : Sg} (c : Chain s) (ts : List ℕ) (W : c.Bl → ℕ → WO) (τ : Tr (PQ.uL (ckP .two) c.rds)),
    ViewOf p F r0 c ts W τ rs' cols →
    PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds τ) = true →
    accK p F t0 r0 c ts W τ = true

theorem givenAt_of_step (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView)
    (cols : List OpenedColumn) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n)) :
    GivenAt p F t0 r0 rs' cols :=
  fun c ts W τ h hw => accK_of_view p F t0 r0 c ts W τ rs' cols h hw tE n hstep

/-- The constant arm's ∃-top, laid onto the given form. -/
theorem yesConst_viewOf {X : Letters} {p : P12} {F : ℕ} {t0 : T12} {r0 : Fmt.RoundView}
    {rs' : List Fmt.RoundView} {cols : List OpenedColumn} (h : YesConst X p F t0 r0 rs' cols) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : List H2K.Pub.WR)
      (c : Chain (H2K.Pub.sgOf a)) (D : H2K.First.Plain) (W0 : ℕ → WO)
      (τ : Tr (PQ.uL (ckP .two) c.rds)),
      H2K.Pub.chainFrom X rest a l = some c ∧
      ViewOf p F r0 c D.ts (wAt c W0 D.fresh.t fun _ => W0 D.fresh.t) τ rs' cols ∧
      accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fun _ => W0 D.fresh.t) τ = true := by
  obtain ⟨a, rest, _, l, c, _, _, e3, _, _, _, _, _, _, D, _, _, W0, _, τ, t1, t3, t4⟩ := h
  exact ⟨a, rest, l, c, D, W0, τ, e3, ⟨t1, t4⟩, t3⟩

/-- The own mask's arm's ∃-top, laid onto the given form. -/
theorem yesOwn_viewOf {X : Letters} {p : P12} {F : ℕ} {t0 : T12} {r0 : Fmt.RoundView}
    {rs' : List Fmt.RoundView} {cols : List OpenedColumn} (h : YesOwn X p F t0 r0 rs' cols) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : List H2K.Pub.WR)
      (c : Chain (H2K.Pub.sgOf a)) (D : H2K.First.Plain) (W0 : ℕ → WO)
      (τ : Tr (PQ.uL (ckP .two) c.rds)),
      H2K.Pub.chainFrom X rest a l = some c ∧
      ViewOf p F r0 c D.ts (wAt c W0 D.fresh.t (orc1 c)) τ rs' cols ∧
      accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t (orc1 c)) τ = true := by
  obtain ⟨a, rest, _, l, c, _, _, e3, _, _, _, _, _, _, D, _, _, W0, _, τ, t1, t3, t4⟩ := h
  exact ⟨a, rest, l, c, D, W0, τ, e3, ⟨t1, t4⟩, t3⟩

/-- AtSeatAll at a cut with a seat: its whole conclusion, and the given form at the same letters. -/
theorem atSeatAll_given (X : Letters) (p : P12) (ft : ℕ) {S Cl : Type} (bs : List (Block S Cl))
    (s s' : S) (v : Fmt.View) (h : AtSeatAll X p ft bs s s' v) (pre : List (Block S Cl))
    (B : Block S Cl) (l : List (Block S Cl)) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (hb : bs = pre ++ B :: l) (hB : IsSeat B p enter leave) :
    ∃ (m : S) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (tE : T12) (n : ℕ)
      (t : S),
      foldBlocks ft pre s v.rounds v.opened = .ok (m, behindOf pre v.rounds, cols) ∧
      (∃ j, cols = v.opened.drop j) ∧
      enter m = .ok t0 ∧ (behindOf pre v.rounds).take B.rounds.length = r0 :: rs' ∧
      (proximityTestKind guardedProximityTestParts p : Blk').step ft t0 (r0 :: rs') cols = .ok (tE, n) ∧ leave m tE = .ok t ∧
      foldBlocks ft l t ((behindOf pre v.rounds).drop B.rounds.length) (cols.drop n) =
        .ok (s', [], []) ∧
      YesAll X p ft t0 r0 rs' cols ∧ GivenAt p ft t0 r0 rs' cols := by
  obtain ⟨m, t0, r0, rs', cols, tE, n, t, a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    atSeatAll_at X p ft bs s s' v h pre B l enter leave hb hB
  exact ⟨m, t0, r0, rs', cols, tE, n, t, a1, a2, a3, a4, a5, a6, a7, a8,
    givenAt_of_step p ft t0 r0 rs' cols tE n a5⟩

/-- From a yes of a written description's decision, at a seat in its first chain: the given form. -/
theorem run_given (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    {Xi : Type} (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View) (e : F.S₁ × F.S₂ × F.S₃)
    (h : F.runEnd x v₁ v₂ v₃ = .ok e) (pre : List (Block F.S₁ F.Cl)) (B : Block F.S₁ F.Cl)
    (l : List (Block F.S₁ F.Cl)) (enter : F.S₁ → Except String T12)
    (leave : F.S₁ → T12 → Except String F.S₁) (hb : F.first.blocksInOrder = pre ++ B :: l)
    (hB : IsSeat B p enter leave) :
    ∃ (m : F.S₁) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn),
      foldBlocks 0 pre (F.start₁ (F.pub x)) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
        .ok (m, behindOf pre (withEmptySealRound v₁).rounds, cols) ∧
      (∃ j, cols = (withEmptySealRound v₁).opened.drop j) ∧ enter m = .ok t0 ∧
      (behindOf pre (withEmptySealRound v₁).rounds).take B.rounds.length = r0 :: rs' ∧
      GivenAt p 0 t0 r0 rs' cols := by
  obtain ⟨m, t0, r0, rs', cols, _, _, _, a1, a2, a3, a4, _, _, _, _, a9⟩ :=
    atSeatAll_given X p 0 _ _ _ _ (run_atSeat_all X p he ha F x v₁ v₂ v₃ e h).1 pre B l enter leave
      hb hB
  exact ⟨m, t0, r0, rs', cols, a1, a2, a3, a4, a9⟩

end H2K.JointK

#print axioms H2K.JointK.yesConst_viewOf
#print axioms H2K.JointK.yesOwn_viewOf
#print axioms H2K.JointK.givenAt_of_step
#print axioms H2K.JointK.atSeatAll_given
#print axioms H2K.JointK.run_given
