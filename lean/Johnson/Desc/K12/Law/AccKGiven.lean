-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.RoundIsOf
/-
Johnson/Desc/K12/Law/AccKGiven.lean: accK AT A GIVEN TRANSCRIPT AND GIVEN TABLES, NO «THERE IS»: a view whose rounds behind "BAT" are the transcript's as shown (the sealed digests apart) and whose columns, as many as the step wants, are the transcript's own written columns: on such a view Block.step of proximityTestKind guardedProximityTestParts p says yes, and the transcript's tests of work pass, IF AND ONLY IF accK says yes at the transcript. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. OF proximityTestKind guardedProximityTestParts p.
  ViewOf          the two equations that tie a view (rs', cols) behind r0 to a transcript τ and tables W
  accK_of_view    ViewOf · τ's tests of work pass · a yes of Block.step at (r0 :: rs', cols) ⇒ accK p F t0 r0 c ts W τ = true
  view_of_accK    ViewOf · accK … τ = true ⇒ Block.step says yes at (r0 :: rs', cols) ∧ τ's tests of work pass
  accK_iff_view   the two as one «if and only if»
  viewOf_written  ViewOf has a member at every τ and W: the written view itself (so the «if and only if» is empty nowhere)
WHY: Johnson/Desc/K12/Law/AccKConst.lean's and Johnson/Desc/K12/Law/AccKOwn.lean's tops say «there are tables and a transcript»: their worth is that the lemma is not empty. What a proof of soundness spends is this form: the transcript and the tables are the game's, GIVEN; the view is what they show.
WHAT IT DOES NOT SAY: that a view from bytes is ViewOf of anything: that is the reading's (the trees' binding; the hash as an oracle): NOT HERE · anything of "BAT"'s own round: r0 is handed to accK as shown; it is not in τ · anything on W: it is a free letter here (the lemma's own is wAt c W0 ft fM) · no completeness; no level of security.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Onto (step_congr groupsOf_noDigest)

/-- The view (rs', cols) behind r0 is what the transcript τ and the tables W show: its rounds are
τ's as shown, the sealed digests apart; its columns, as many as the step wants, are τ's written
columns. -/
def ViewOf (p : P12) (F : ℕ) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s) (ts : List ℕ)
    (W : c.Bl → ℕ → WO) (τ : Tr (PQ.uL (ckP .two) c.rds)) (rs' : List Fmt.RoundView) (cols : List OpenedColumn) :
    Prop :=
  (PQ.rvSL (ckP .two) c.rds τ).map noDigest = rs'.map noDigest ∧
  cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
    colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
      (srcK p c (blOf c τ) ts fun z x => colW (W (blOf c τ) z).1 (W (blOf c τ) z).2 x)

/-- On a view of τ and W the step's answer is its answer at the written view, which accK asks. -/
theorem step_viewOf (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s)
    (ts : List ℕ) (W : c.Bl → ℕ → WO) (τ : Tr (PQ.uL (ckP .two) c.rds)) (rs' : List Fmt.RoundView)
    (cols : List OpenedColumn) (h : ViewOf p F r0 c ts W τ rs' cols) :
    (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: PQ.rvSL (ckP .two) c.rds τ)
      (colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
        ((r0 :: PQ.rvSL (ckP .two) c.rds τ).map (·.drawn)))
        (srcK p c (blOf c τ) ts fun z x => colW (W (blOf c τ) z).1 (W (blOf c τ) z).2 x)) =
      (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols := by
  obtain ⟨h1, h2⟩ := h
  have hrs : (r0 :: PQ.rvSL (ckP .two) c.rds τ).map noDigest = (r0 :: rs').map noDigest := by
    rw [List.map_cons, List.map_cons, h1]
  have hg : groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
      ((r0 :: PQ.rvSL (ckP .two) c.rds τ).map (·.drawn)) =
      groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)) := by
    rw [← groupsOf_noDigest, hrs, groupsOf_noDigest]
  rw [hg, step_congr F _ t0 _ _ _ hrs]
  refine step_cols F _ t0 _ _ _ ?_
  rw [h2, List.take_of_length_le]
  have := congrArg List.length h2
  rw [← this]
  exact List.length_take_le _ _


theorem accK_of_view (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s)
    (ts : List ℕ) (W : c.Bl → ℕ → WO) (τ : Tr (PQ.uL (ckP .two) c.rds)) (rs' : List Fmt.RoundView)
    (cols : List OpenedColumn) (h : ViewOf p F r0 c ts W τ rs' cols)
    (hwork : PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds τ) = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n)) :
    accK p F t0 r0 c ts W τ = true := by
  unfold accK
  rw [step_viewOf p F t0 r0 c ts W τ rs' cols h, hstep, hwork]
  rfl

theorem view_of_accK (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s)
    (ts : List ℕ) (W : c.Bl → ℕ → WO) (τ : Tr (PQ.uL (ckP .two) c.rds)) (rs' : List Fmt.RoundView)
    (cols : List OpenedColumn) (h : ViewOf p F r0 c ts W τ rs' cols)
    (hacc : accK p F t0 r0 c ts W τ = true) :
    (∃ (tE : T12) (n : ℕ), (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n)) ∧
      PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds τ) = true := by
  unfold accK at hacc
  rw [step_viewOf p F t0 r0 c ts W τ rs' cols h, Bool.and_eq_true] at hacc
  refine ⟨?_, hacc.2⟩
  cases hs : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols with
  | ok x => exact ⟨x.1, x.2, rfl⟩
  | error e =>
    rw [hs] at hacc
    exact absurd hacc.1 (by simp)


theorem accK_iff_view (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s)
    (ts : List ℕ) (W : c.Bl → ℕ → WO) (τ : Tr (PQ.uL (ckP .two) c.rds)) (rs' : List Fmt.RoundView)
    (cols : List OpenedColumn) (h : ViewOf p F r0 c ts W τ rs' cols) :
    accK p F t0 r0 c ts W τ = true ↔
      (∃ (tE : T12) (n : ℕ), (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n)) ∧
        PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds τ) = true :=
  ⟨view_of_accK p F t0 r0 c ts W τ rs' cols h,
    fun ⟨⟨tE, n, hs⟩, hw⟩ => accK_of_view p F t0 r0 c ts W τ rs' cols h hw tE n hs⟩

/-- ViewOf has a member at every transcript and all tables: the written view itself. -/
theorem viewOf_written (p : P12) (F : ℕ) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s) (ts : List ℕ)
    (W : c.Bl → ℕ → WO) (τ : Tr (PQ.uL (ckP .two) c.rds)) :
    ViewOf p F r0 c ts W τ (PQ.rvSL (ckP .two) c.rds τ)
      (colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
        ((r0 :: PQ.rvSL (ckP .two) c.rds τ).map (·.drawn)))
        (srcK p c (blOf c τ) ts fun z x => colW (W (blOf c τ) z).1 (W (blOf c τ) z).2 x)) := by
  refine ⟨rfl, List.take_of_length_le ?_⟩
  rw [colsOf_eq, colsFrom_length]
  unfold Block.want
  exact le_refl _

end H2K.JointK

#print axioms H2K.JointK.step_viewOf
#print axioms H2K.JointK.accK_of_view
#print axioms H2K.JointK.view_of_accK
#print axioms H2K.JointK.accK_iff_view
#print axioms H2K.JointK.viewOf_written
