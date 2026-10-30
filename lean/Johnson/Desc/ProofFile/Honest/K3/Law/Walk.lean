-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Walk.lean: the honest side of the kind "lookup" (K3). The steps
of the walk that leads from the stages' own steps (Honest/K3/Law/Statements.lean: `StageStep` and
`LeavesStep`, which are hypotheses here; `quietStep`, a theorem) to "the verifier's hearing returns
on the course's rounds". Theorems and a few definitions. Everything on a sumcheck is conditional on
`StageStep` (at the leaves: on `LeavesStep`), which are not proved in this file.

Terms. Honest/K3/GLOSSARY.md ("course", "fit", "hearing", "stage", "world, worth").

What is shown.
  `Cut R x`: the course's rounds x, cut by stage. It is a hypothesis of the walk.
  `off f n`: how many rounds the first n stages take; with `off_at`, `off_succ`, `off_le`,
    `off_len`.
  `RowsGood R rows G`: conditional on the stages' summands summing: each of these rows is worth 0 in
    the world of every ledger later than G; with `RowsGood.later`, `RowsGood.push`.
  `quiet_step`, `sum_step`, `leaves_step`: one stage of the row: what the rounds in front of it
    split into, and the invariant behind it. For every face.
  `walk_call_eq`: conditional (one part of keys): the stage's call in the run is its shape with the
    verifier's own variables at the run's points.
  `pts_eq`: the run's points are those of the rounds' challenges.
  `run_walk`: a run of levels of a product tree, by letters for its stages.
Others: `sliceOf` (a definition), `mem_at`, `slice_split`, `slice_len`, `alone_slice`, `split_at`,
`rowsGood_empty`, `walk_sum_take_le`.

Hypotheses that remain.
  `SS`, `LS`: the statements `StageStep` and `LeavesStep`. Shown in: `stageStep` and `leavesStep`
    (Honest/K3/Law/StageStep.lean), conditional on `HB`; `stageStepP` and `leavesStepP`
    (Honest/K3/Law/HBPaid.lean), without `HB`, resting on the theorems of Honest/SumLaw/.
  `C`: `Cut R x`. Shown in: `cut_of_rounds` (Honest/K3/Law/CutOf.lean), from `Fit R` and
    `R.rounds = some x`.
  `hF`: `Fit R`.
  `I`: the invariant `Inv` in front of the stage.
  `hn`, `h`, `hs`: s is the stage number n, or one of the row's. `hc`, `hk`, `ht`: it has no call;
    the call k; an end value. `hp`: (in `walk_call_eq`) one part of keys. `g`, `l`, `z`: (in
    `RowsGood.later`, `RowsGood.push`) `RowsGood` so far; a later ledger; the new row's worth,
    conditional on its stage's sums.
  In `run_walk`, on the letters for the run's stages: `hsg`, `hln`: which stages the levels and
    their lines are; `hcall`, `het`, `hform`, `hfm`, `hpt`: each level's call, end term and form,
    the next form, the points; `htail`, `hrounds`, `hq`, `hd`: counts; `I0`, `g0`: the invariant and
    `RowsGood` in front.

Users. This file is imported by Honest/K3/Law/CutOf.lean, Honest/K3/Law/LookHeard.lean and
Honest/K3/Law/LookLeftOf.lean.

Limits. `Cut` is not shown of any rounds here: `cut_of_rounds` (CutOf.lean) shows it.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Statements
import Johnson.Desc.ProofFile.Honest.K3.Law.Steps
import Johnson.Desc.ProofFile.Honest.K3.Law.Index
import Johnson.Desc.ProofFile.Honest.K3.RowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE addE subE mulE isZeroE)
open OnBytes.Model (Reading Aff Fork eqTab orderDefault)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open VerifiableInference.Desc.First.ProdV
  (layBack levelVars stepDown LevelOut level Carried levelEnds
  elementsAlone run_zero)
open ProofFile.Honest.K3.Forward (Quiet level_ret run_succ_ret)

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

variable {W : Type}

/-! ## The course's rounds, cut by stage -/

/-- A stage's own rounds among the lookup's. -/
def sliceOf (f : LFace) (x : List Fmt.RoundView) (s : Stage) : List Fmt.RoundView :=
  (x.drop (firstRound f s)).take (s.rounds f)

/-- **The course's rounds, cut by stage.** In the field stage, seen is bound by "∃" and held by what
functions return at it alone: some value: not said to be the run's own. -/
structure Cut (R : Course W) (x : List Fmt.RoundView) : Prop where
  /-- the rounds' challenges are the course's -/
  drawn : x.map (·.drawn) = R.ds
  /-- no position and no matrix entry is sampled -/
  alone : elementsAlone x = true
  /-- as many rounds as the stages take -/
  len : x.length = ((stages R.f).map (Stage.rounds R.f)).sum
  /-- each stage, played alone from the state in front of it, yields its own rounds. The seen that
  `cut_of_rounds` (Honest/K3/Law/CutOf.lean) lays is `R.seen` with rounds laid behind; no lemma that
  takes a `Cut` reads it -/
  stage : ∀ s ∈ stages R.f, ∃ seen, R.stage s (R.stateAt s) seen (R.draws s) =
    some (sliceOf R.f x s)
  /-- a stage that sends nothing: its one round -/
  quiet : ∀ s ∈ stages R.f, s.call R.f = none → ∃ r, sliceOf R.f x s = [r] ∧ Quiet (s.draws R.f) r

/-! ## Rounds in front, by a stage's number -/

/-- How many rounds the first n stages take. -/
def off (f : LFace) (n : Nat) : Nat := (((stages f).take n).map (Stage.rounds f)).sum

theorem off_at {f : LFace} {n : Nat} {s : Stage} (h : (stages f)[n]? = some s) :
    firstRound f s = off f n := by
  obtain ⟨hn, e⟩ := List.getElem?_eq_some_iff.1 h
  rw [← e]
  exact firstRound_getElem f n hn

theorem off_succ {f : LFace} {n : Nat} {s : Stage} (h : (stages f)[n]? = some s) :
    off f (n + 1) = off f n + s.rounds f := by
  unfold off
  rw [take_succ_get h]
  simp

theorem walk_sum_take_le (l : List Nat) (n : Nat) : (l.take n).sum ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop n l, List.sum_append]
  omega

theorem off_le (f : LFace) (n : Nat) : off f n ≤ ((stages f).map (Stage.rounds f)).sum := by
  unfold off
  rw [List.map_take]
  exact walk_sum_take_le _ n

theorem off_len (f : LFace) : off f (stages f).length = ((stages f).map (Stage.rounds f)).sum := by
  unfold off
  rw [List.take_length]

theorem mem_at {f : LFace} {n : Nat} {s : Stage} (h : (stages f)[n]? = some s) : s ∈ stages f :=
  List.mem_of_getElem? h

theorem slice_split (x : List Fmt.RoundView) (a n : Nat) :
    x.drop a = (x.drop a).take n ++ x.drop (a + n) := by
  rw [← dd]
  exact (List.take_append_drop n (x.drop a)).symm

theorem slice_len (x : List Fmt.RoundView) (a n : Nat) (h : a + n ≤ x.length) :
    ((x.drop a).take n).length = n := by
  rw [List.length_take, List.length_drop]
  omega

theorem alone_slice {x : List Fmt.RoundView} (h : elementsAlone x = true) (a n : Nat) :
    elementsAlone ((x.drop a).take n) = true := by
  unfold elementsAlone at h ⊢
  rw [List.all_eq_true] at h ⊢
  exact fun r hr => h r (List.mem_of_mem_drop (List.mem_of_mem_take hr))

/-- What a stage's number says of the rounds: those from the stage on are its own, then those from
the next stage on. -/
theorem split_at {R : Course W} {x : List Fmt.RoundView} (C : Cut R x) {n : Nat} {s : Stage}
    (hn : (stages R.f)[n]? = some s) :
    x.drop (off R.f n) = sliceOf R.f x s ++ x.drop (off R.f (n + 1)) ∧
      (sliceOf R.f x s).length = s.rounds R.f ∧ elementsAlone (sliceOf R.f x s) = true := by
  have h1 := off_at hn
  have h2 := off_succ hn
  have h3 := off_le R.f (n + 1)
  unfold sliceOf
  rw [h1, h2]
  exact ⟨slice_split _ _ _, slice_len _ _ _ (by rw [C.len]; omega), alone_slice C.alone _ _⟩

/-! ## Rows that are worth 0 -/

/-- **Where every stage's summand sums as it should, each of these rows is worth 0** in the world of
every ledger later than G, at mask entries that are the coins spent. -/
def RowsGood (R : Course W) (rows : Array Aff) (G : Fork) : Prop :=
  (∀ s ∈ stages R.f, 0 < s.tail R.f →
    Sums R s (rd (R.claimed s)) (rd (endTerm R.factor s (R.shown s)))) →
  ∀ y ∈ rows.toList, ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G H →
    MasksAre R mask → y.value Reading.gl (H.worldOf Reading.gl mask entry) = 0

theorem RowsGood.later {R : Course W} {rows : Array Aff} {G G' : Fork} (g : RowsGood R rows G)
    (l : Later G G') : RowsGood R rows G' :=
  fun hs y hy H mask entry hl hm => g hs y hy H mask entry (l.trans hl) hm

theorem RowsGood.push {R : Course W} {rows : Array Aff} {G : Fork} {s : Stage} {row : Aff}
    (g : RowsGood R rows G) (hs : s ∈ stages R.f) (ht : 0 < s.tail R.f)
    (z : Sums R s (rd (R.claimed s)) (rd (endTerm R.factor s (R.shown s))) →
      ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G H → MasksAre R mask →
        row.value Reading.gl (H.worldOf Reading.gl mask entry) = 0) :
    RowsGood R (rows.push row) G := by
  intro hS y hy H mask entry hl hm
  rw [Array.toList_push] at hy
  rcases List.mem_append.1 hy with h | h
  · exact g hS y h H mask entry hl hm
  · obtain rfl : y = row := by simpa using h
    exact z (hS s hs ht) H mask entry hl hm

theorem rowsGood_empty (R : Course W) (G : Fork) : RowsGood R #[] G := by
  intro _ y hy
  simp at hy

/-! ## One stage -/

theorem quiet_step {R : Course W} {x : List Fmt.RoundView} (C : Cut R x) {n : Nat} {s : Stage} {F : Fork}
    (hn : (stages R.f)[n]? = some s) (hc : s.call R.f = none) (I : Inv R n F) :
    ∃ r, x.drop (off R.f n) = r :: x.drop (off R.f (n + 1)) ∧ Quiet (s.draws R.f) r ∧
      Inv R (n + 1) F := by
  obtain ⟨r, e, q⟩ := C.quiet s (mem_at hn) hc
  obtain ⟨a, _, _⟩ := split_at C hn
  rw [e] at a
  exact ⟨r, a, q, quietStep W R n s F hn hc I⟩

theorem sum_step (SS : StageStep) {R : Course W} {x : List Fmt.RoundView} (hF : Fit R) (C : Cut R x)
    {n : Nat} {s : Stage} {F : Fork} (hn : (stages R.f)[n]? = some s) (ht : 0 < s.tail R.f)
    (I : Inv R n F) :
    ∃ xs h row G, x.drop (off R.f n) = xs ++ x.drop (off R.f (n + 1)) ∧
      xs.length = s.rounds R.f ∧ elementsAlone xs = true ∧
      MaskedSum.whole (R.form s) (R.call s) (fun _ v => endTerm R.factor s v) F xs =
        some (h, row, G) ∧
      isZeroE (h.r.getLastD zeroE) = false ∧ h.sEnd = R.endSlot s ∧ Inv R (n + 1) G ∧ Later F G ∧
      (Sums R s (rd (R.claimed s)) (rd (endTerm R.factor s (R.shown s))) →
        ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G H →
          MasksAre R mask → row.value Reading.gl (H.worldOf Reading.gl mask entry) = 0) := by
  obtain ⟨seen, e⟩ := C.stage s (mem_at hn)
  obtain ⟨a, b, c⟩ := split_at C hn
  obtain ⟨h, row, G, w, _, y, z, I', last⟩ := SS W R n s F seen _ hF hn ht I e
  exact ⟨_, h, row, G, a, b, c, w, y, z, I', MaskedSum.whole_keeps w, last⟩

theorem leaves_step (LS : LeavesStep) {R : Course W} {x : List Fmt.RoundView} (hF : Fit R) (C : Cut R x)
    {n : Nat} {F : Fork} (hn : (stages R.f)[n]? = some .leaves) (I : Inv R n F) :
    ∃ xs h G, x.drop (off R.f n) = xs ++ x.drop (off R.f (n + 1)) ∧
      xs.length = Stage.rounds R.f .leaves ∧ elementsAlone xs = true ∧
      MaskedSum.hear (R.form .leaves) (R.call .leaves) F xs = some (h, G) ∧
      h.r = R.r .leaves ∧ h.first = R.first + firstSlot R.f .leaves ∧ Inv R (n + 1) G ∧
      (∀ j, h.first ≤ j → j < h.first + Stage.own R.f .leaves → ¬ OnBytes.PscRun.Filled G j) ∧
      Later F G ∧
      (∀ cf : GE, Sums R .leaves (rd (R.claimed .leaves)) cf →
        ∀ (F' G' H : Fork) (y : Aff) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE),
          OnBytes.PscRun.Sized F' → Later G F' → MaskedSum.row h oneE {} F' = some (y, G') →
          Later G' H → MasksAre R mask →
          y.value Reading.gl (H.worldOf Reading.gl mask entry) = rd h.eps * (1 - cf)) := by
  obtain ⟨seen, e⟩ := C.stage .leaves (mem_at hn)
  obtain ⟨a, b, c⟩ := split_at C hn
  obtain ⟨h, G, w, y, z, I', fr, last⟩ := LS W R n F seen _ hF hn I e
  exact ⟨_, h, G, a, b, c, w, y, z, I', fr, MaskedSum.hear_keeps w, last⟩

/-! ## The call; the points -/

/-- **Conditional: at one part of keys.** The stage's call as it stands in the run is its shape with
the verifier's own variables at the run's points. -/
theorem walk_call_eq (R : Course W) (v : Nat) (hp : R.f.parts = [v]) (hF : Fit R) {s : Stage}
    (hs : s ∈ stages R.f) {k : Call} (hk : s.call R.f = some k) :
    R.call s = { k with vs := varsAt R.f s R.pts } := by
  have hsh : shapeAt R.a s = k := by
    unfold shapeAt
    rw [hk]
    rfl
  show ({ (shapeAt R.a s) with
    vs := withPoints (shapeAt R.a s).vs
      (pointsAt R.f s (ptsOf R.f R.a.base (R.t.heard ++ R.ds.take (firstRound R.f s)))) } : Call) =
    { k with vs := varsAt R.f s (ptsOf R.f R.a.base (R.t.heard ++ R.ds)) }
  rw [hsh, withPoints_varsAt R.f s k _ _ hk hs hF.ok, ← hF.base,
    varsAt_prefix R.f v hp R.t.heard R.ds s hs]

/-- The run's points are those of the rounds' challenges, behind what was heard in front. -/
theorem pts_eq {R : Course W} {x : List Fmt.RoundView} (hF : Fit R) (C : Cut R x) :
    R.pts = ptsOf R.f R.t.heard.length (allOf R.t.heard x []) := by
  show ptsOf R.f R.a.base (R.t.heard ++ R.ds) = _
  rw [← hF.base, ← C.drawn]
  simp [allOf]

/-! ## A run of levels -/

/-- **A run of levels of a product tree**, by letters: sg l, ln l: the stages of level number l and
of the LINE behind it; i0: the first one's number in the row; pt l, fm l: the point and the form in
front of level l. Conditional on `StageStep`. -/
theorem run_walk (SS : StageStep) {R : Course W} {x : List Fmt.RoundView} (hF : Fit R) (C : Cut R x)
    (m0 : Nat) (orders : Nat → List Nat) (sg ln : Nat → Stage) (i0 : Nat) (pt : Nat → Array E)
    (fm : Nat → Aff) (N : Nat)
    (hsg : ∀ l, l < N → (stages R.f)[i0 + 2 * l]? = some (sg l))
    (hln : ∀ l, l < N → (stages R.f)[i0 + 2 * l + 1]? = some (ln l))
    (hcall : ∀ l, l < N →
      R.call (sg l) = ⟨0, levelVars (m0 + l) (pt l) (orders (m0 + l)), some levelEnds⟩)
    (het : ∀ l v, endTerm R.factor (sg l) v = mulE (v.getD 0 zeroE) (v.getD 1 zeroE))
    (hform : ∀ l, l < N → R.form (sg l) = fm l)
    (hfm : ∀ l, l < N → fm (l + 1) = R.line (sg l) ((pt (l + 1)).getD 0 zeroE))
    (hpt : ∀ l, l ≤ N → pt l = lastPt m0 orders (pt 0) (x.drop (off R.f i0)) 0 l)
    (htail : ∀ l, l < N → 0 < (sg l).tail R.f)
    (hrounds : ∀ l, l < N → (sg l).rounds R.f = m0 + l + 3)
    (hq : ∀ l, l < N → (ln l).call R.f = none) (hd : ∀ l, l < N → (ln l).draws R.f = 1)
    (rows0 : Array Aff) (F0 : Fork) (I0 : Inv R i0 F0) (g0 : RowsGood R rows0 F0) :
    ∀ n, n ≤ N → ∃ c G,
      vRun m0 n orders { rows := rows0, point := pt 0, form := fm 0 } F0 (x.drop (off R.f i0)) =
        some (c, G, x.drop (off R.f (i0 + 2 * n))) ∧
      c.point = pt n ∧ c.form = fm n ∧ c.rows.size = rows0.size + n ∧ Inv R (i0 + 2 * n) G ∧
      RowsGood R c.rows G ∧ Later F0 G := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨_, F0, run_zero _ _ _ _ _, rfl, rfl, rfl, I0, g0, Later.refl F0⟩
  | succ n ih =>
    intro hn
    have hn' : n < N := by omega
    obtain ⟨c, G, e, p1, p2, p3, I, gd, lt⟩ := ih (by omega)
    obtain ⟨xs, h, row, G', a, b, al, w, y, z, I', lt', zr⟩ :=
      sum_step SS hF C (hsg n hn') (htail n hn') I
    obtain ⟨line, a2, q, I''⟩ := quiet_step C (hln n hn') (hq n hn') I'
    rw [hd n hn'] at q
    rw [a2] at a
    rw [hform n hn', hcall n hn', ← p1, ← p2] at w
    have het' : (fun (_ : List E) (v : List E) => endTerm R.factor (sg n) v) =
        fun _ v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE) := by
      funext _ v
      exact het n v
    rw [het'] at w
    rw [hrounds n hn'] at b
    have lv := level_ret w b al q y (x.drop (off R.f (i0 + 2 * n + 1 + 1)))
    rw [← a] at lv
    have rn := run_succ_ret e lv
    have hi : i0 + 2 * (n + 1) = i0 + 2 * n + 1 + 1 := by omega
    rw [hi]
    have hp1 := run_point rn
    rw [← hpt (n + 1) hn] at hp1
    refine ⟨_, G', rn, hp1, ?_, ?_, I'',
      (gd.later lt').push (mem_at (hsg n hn')) (htail n hn') zr, lt.trans lt'⟩
    · rw [hfm n hn', ← hp1]
      simp [Course.line, stepDown, z]
    · simp [p3]
      omega

#print axioms ProofFile.Honest.K3.Law.walk_sum_take_le
#print axioms ProofFile.Honest.K3.Law.mem_at
#print axioms ProofFile.Honest.K3.Law.slice_split
#print axioms ProofFile.Honest.K3.Law.slice_len
#print axioms ProofFile.Honest.K3.Law.alone_slice
#print axioms ProofFile.Honest.K3.Law.RowsGood.later
#print axioms ProofFile.Honest.K3.Law.RowsGood.push
#print axioms ProofFile.Honest.K3.Law.rowsGood_empty
#print axioms ProofFile.Honest.K3.Law.off_at
#print axioms ProofFile.Honest.K3.Law.off_succ
#print axioms ProofFile.Honest.K3.Law.off_le
#print axioms ProofFile.Honest.K3.Law.off_len
#print axioms ProofFile.Honest.K3.Law.split_at
#print axioms ProofFile.Honest.K3.Law.quiet_step
#print axioms ProofFile.Honest.K3.Law.sum_step
#print axioms ProofFile.Honest.K3.Law.leaves_step
#print axioms ProofFile.Honest.K3.Law.walk_call_eq
#print axioms ProofFile.Honest.K3.Law.pts_eq
#print axioms ProofFile.Honest.K3.Law.run_walk

end ProofFile.Honest.K3.Law
