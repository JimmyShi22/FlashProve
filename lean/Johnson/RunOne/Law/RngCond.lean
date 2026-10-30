-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngCond.lean: AT A KEY FILE's RANGES' TEST, WHERE THE RANGES' SEAT's ASKING HAS RETURNED: THE CONDITION IN FRONT OF THE PROXIMITY TEST HOLDS AT THE WORD OF WHICH THE KIND K12's LAW SPEAKS. The join of Johnson/RunOne/Law/RngAsked.lean (what that seat asks),
RngSeats.lean (the seats of the law's own typed group are the layout's), RngHolds.lean (the condition `Cond`) and the kind's files' lemmas on what a yes holds. Statements and proofs.
OBJECT. The record at which the ranges' seat's asking has returned (Johnson/Desc/Key/Ranges.lean: asksOnRecord), and the word of which the kind's law speaks there.
USER. Johnson/RunOne/Law/RngSized.lean, RngLemma.lean.
LETTERS. The place p and the record are free. Premises: the asking's return, the kind's block's yes, and that the record names the mask (hmask).

What is said.
  `bat_of_yes`: where the variant's decide returns (the first fold's mask having come earlier: early = true), the kind's batching has returned at the record handed in, ON THE FIRST ROUND SHOWN, AND THE ROW HAS NO KEPT FORM: by the frame's law (k12_ok, Johnson/Desc/K12/FrameLaws.lean) and the variant's guard behind its
    batching (batK_ok, noKept_spec, Johnson/Desc/K12/Law/Top.lean): both from K12's files.
  `facts_of_combineAt`: the test combineAt's yes gives the layout's facts, and that no member stands twice in the layout.
  `entered_some`: where the record names the mask, the plain data's statement and book are the record's.
  `rowsBlank_asked`: where the ranges' seat's asking has returned, the record names the mask, and the batching returns (row, L, S') without a kept form: the plain data D are made, the test gpOk's clauses hold of them (`Good`), and THE WORD OF THE TYPED GROUP MADE OF D
    (the group that the kind's law names), at all members' words and radii, HAS `RowsBlank` AT S' AND L. No premise on the layout, the members or the shapes is left.
  `cond_asked`: so `Cond` at that word, under the stage's sizes and a radius below the distance. BOTH ARE STATED FOR EVERY e r row L S' ON WHICH THE BATCHING RETURNS, AND PIN D: gpOf … = some D: so a spender who holds the kind's lemma in the game (k12_lemma), whose D is pinned
    by the same equation, has the same D.
From the block's own yes: Johnson/RunOne/Law/RngSized.lean.
What is left as a premise: (sg a).Sized and a radius below (sg a).d; that the record names the mask.
Limits. `bat_of_yes` is stated at blocks without claims' type (Cl := Unit), as the kind's laws are. The members' words are letters: how they are read off trees is the reading's. `Cond` is a condition: nothing here says that the relation `Holds` has a witness, or what a
yes is worth. Nothing on soundness.

-/
import Johnson.RunOne.Law.RngSeats
import Johnson.RunOne.Law.RngHolds
import Johnson.Desc.K12.Law.OutK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RngCond
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc.Key Johnson.RunOne.Law.RngAsked Johnson.RunOne.Law.RngSeats Johnson.RunOne.Law.RngHolds
open H2K.ClaimSays (RowsBlank)
open H2K.First (Good Made Plain gpG gpOf gpOk_inv good_of_ok made_of sg)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts k12_ok frontJ)
open VerifiableInference.Desc.First.Close (bat)

/-- A list of which a first stretch is one thing begins with it. -/
theorem head_of_take {α : Type} {l : List α} {n : Nat} {x : α} (h : l.take n = [x]) : l.head? = some x := by
  cases l with
  | nil => simp at h
  | cons y ys =>
    cases n with
    | zero => simp at h
    | succ n =>
      rw [List.take_succ_cons] at h
      exact congrArg some (List.cons.inj h).1

/-- Where the variant's decide returns, the batching has returned at the record handed in, ON THE FIRST ROUND SHOWN, and the row has no kept form. -/
theorem bat_of_yes (p : P12) (he : p.early = true) {t0 tE : T12} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t0 rs gs = .ok tE) :
    ∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
      rs.head? = some r ∧ bat t0.st t0.g e r = .ok (row, L, S') ∧ row.kept = #[] := by
  obtain ⟨first, rest, ds, tF, t1, _, _, hfr, hbat, _, _⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := (H2K.Out.like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := H2K.FoldLaw.bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨hb1, hk, _⟩ := H2K.JointK.batK_ok p _ _ _ _ _ hbat
  obtain ⟨e, r, row, L, S', hrs, hb, rfl⟩ := H2K.JointK.batJ_ok p he _ _ _ _ _ hb1
  exact ⟨e, r, row, L, S', head_of_take hrs, hb, (H2K.JointK.noKept_spec _ row L rfl hk).1⟩

/-- The test's yes gives the layout's facts, and that no member stands twice in the layout. -/
theorem facts_of_combineAt {S' : Statement} {g : Nat} {L : GroupLayout} {rows : Array Row}
    (h : combineAt S' g ⟨L, rows⟩ = true) : ∃ G', LayFacts S' G' L ∧ L.members.toList.Nodup := by
  obtain ⟨G', hG, hL, hOk, _⟩ := combineAt_gives h
  have hL' : S'.layout g = some L := hL
  refine ⟨G', layFacts hG hL' hOk, ?_⟩
  obtain rfl : layoutOf S' G' = L := Option.some.inj ((layout_eq S' g G' hG).symm.trans hL')
  exact hOk.nodup

/-- Where the record names the mask, the plain data's statement and book are the record's. -/
theorem entered_some (p : P12) (t : T12) (cu : IoppStage) (L : GroupLayout) {id : Nat}
    (h : t.mask = some id) : H2K.First.entered p t cu L = some (id, t.st, t.book) := by
  unfold H2K.First.entered
  rw [h]

/-- **The word of the group that the kind's law names has rows of zeros wherever no member has a real row: no premise on the layout, the members or the shapes is left.** -/
theorem rowsBlank_asked {p : P12} {t0 : T12} (ha : asksOnRecord p t0 = .ok ()) {id : Nat}
    (hmask : t0.mask = some id) {e : Fmt.Entry} {r : Fmt.RoundView} {row : GroupRow} {L : GroupLayout}
    {S' : Statement} (hb : bat t0.st t0.g e r = .ok (row, L, S')) (h0 : row.kept = #[]) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : Plain) (hg : Good p.nums.firstTree a row D),
      p.nums.stages = a :: rest ∧ gpOf p { t0 with st := S', pass := .claim row L } a L = some D ∧
      ∀ (rad : ℕ → ℕ) (yw : (gpG hg rad).Words), RowsBlank (sg a) S' L ((gpG hg rad).word yw) := by
  obtain ⟨G, a, rest, _, hs, _, _, a2, ⟨f1, f2, _, _⟩, a4, _⟩ := asked_at_bat ha hb h0
  obtain ⟨D, hD, hok⟩ := gpOk_inv p _ a rest row L hs rfl a4
  have hg := good_of_ok p a row D hok
  have hm := made_of p _ a L D hD
  obtain ⟨G', Fa, hnd⟩ := facts_of_combineAt a2
  have hst : D.st = S' := by
    obtain ⟨cu, _, hent⟩ := hm.ent
    rw [entered_some p { t0 with st := S', pass := .claim row L } cu L (id := id) hmask] at hent
    exact (congrArg (fun x => x.2.1) (Option.some.inj hent)).symm
  exact ⟨a, rest, D, hg, hs, hD, fun rad yw =>
    rowsBlank_gp hg hm rad hnd S' G' Fa (fun i => by rw [← hst]; exact shapes_made hm i) f1 f2 yw⟩

/-- **So the condition in front holds at that word.** -/
theorem cond_asked {p : P12} {t0 : T12} (ha : asksOnRecord p t0 = .ok ()) {id : Nat}
    (hmask : t0.mask = some id) {e : Fmt.Entry} {r : Fmt.RoundView} {row : GroupRow} {L : GroupLayout}
    {S' : Statement} (hb : bat t0.st t0.g e r = .ok (row, L, S')) (h0 : row.kept = #[]) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : Plain) (hg : Good p.nums.firstTree a row D),
      p.nums.stages = a :: rest ∧ gpOf p { t0 with st := S', pass := .claim row L } a L = some D ∧
      ∀ (rd : ℕ), (sg a).Sized → rd < (sg a).d → ∀ (rad : ℕ → ℕ) (yw : (gpG hg rad).Words),
        Cond (sg a) rd t0.st t0.g ((gpG hg rad).word yw) := by
  obtain ⟨a, rest, D, hg, hs, hD, hy⟩ := rowsBlank_asked ha hmask hb h0
  refine ⟨a, rest, D, hg, hs, hD, fun rd hz hd rad yw => cond_of_asks ha hs rd hz hd _ fun G1 L1 hG1 hL1 => ?_⟩
  obtain ⟨G2, _, hG2, hL2, rfl, _, _, _⟩ := RngBat.bat_says hb
  obtain rfl : G2 = G1 := Option.some.inj (hG2.symm.trans hG1)
  obtain rfl : L = L1 := Option.some.inj (hL2.symm.trans hL1)
  exact hy rad yw

end Johnson.RunOne.Law.RngCond

#print axioms Johnson.RunOne.Law.RngCond.bat_of_yes
#print axioms Johnson.RunOne.Law.RngCond.facts_of_combineAt
#print axioms Johnson.RunOne.Law.RngCond.rowsBlank_asked
#print axioms Johnson.RunOne.Law.RngCond.cond_asked
