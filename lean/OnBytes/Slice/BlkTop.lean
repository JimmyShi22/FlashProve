-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkTop.lean: a run of the program's link, taken apart into the runs of its blocks.

The program's check of an entry's chain is one block (OnBytes/Iop/Link.lean: `linkVerify`), made of
the link's steps, the batching, and the stages of the proximity test (OnBytes/Iop/Prox.lean:
`ioppVerify`, `ioppStagesVerify`): at each stage but the last a fold and a code switch, at the last
the base case. This file says that a run of the whole that succeeds is a run of each of these blocks
in turn, each from the context that the one before it has left.

It also says that a yes of a decision is such a run, from the context `startCtx`.

Each theorem opens the text of one definition: `linkVerify`, `ioppVerify`, `ioppStagesVerify` (its
two cases), `Blk.requireAllTested` and `Blk.runFrom` with `Blk.runNamed`
(OnBytes/Iop/Ground.lean).

Main definitions.
 `stageOthers`   what rides in a code switch's message beside the new tables.
 `startCtx`      the context from which a run on a view starts.
Main theorems: `linkVerify_inv`, `ioppVerify_inv`, `ioppStages_step_inv`, `ioppStages_last_inv`,
`requireAllTested_inv`, `decides_yields`.

Not claimed. Nothing on what the blocks compute. The calls between the blocks (a value that is
noted, a new group, a public condition) are listed as runs and not looked into, but for the
conditions.
-/
import OnBytes.Iop.GroundLaws
import OnBytes.Iop.Link

set_option autoImplicit false

namespace OnBytes.Slice
open Params (LinkShape IoppStage IoppChoice)

/-- The link: its steps, the proximity test on the group that they leave, and the last
question, whether every group is tested. -/
theorem linkVerify_inv (S : LinkShape) (first further : TableKey) (c c' : Ctx)
    (h : (linkVerify S first further).Yields c () c') :
    ∃ (x : LinkRun) (c1 c2 : Ctx), (linkStepsVerify S first further).Yields c x c1 ∧
      (ioppVerify x.group S.test S.choice x.mask).Yields c1 () c2 ∧
      Blk.requireAllTested.Yields c2 () c' := by
  unfold linkVerify at h
  obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, c2, h3, h4⟩ := (Blk.yields_bind _ _ _ _ _).1 h2
  exact ⟨x, c1, c2, h1, h3, h4⟩

/-- The proximity test: the public condition on the stages holds (`ioppOk`); the batching; the group
is the first stage's; the stages. -/
theorem ioppVerify_inv (g : Nat) (first : IoppStage) (rest : List IoppStage) (choice : IoppChoice)
    (mask : Option Nat) (c c' : Ctx)
    (h : (ioppVerify g (first :: rest) choice mask).Yields c () c') :
    ∃ (answers : Nat) (ca : Ctx) (S : Statement) (cb : Ctx) (row : GroupRow) (L : GroupLayout)
      (cd ce : Ctx) (G : Group) (cf : Ctx),
      Blk.samples.Yields c answers ca ∧ Blk.statement.Yields ca S cb ∧
      ioppOk S.codes (first :: rest) answers = true ∧
      (batVerify g).Yields cb (row, L) cd ∧ (Blk.note "BAT: target" row.target).Yields cd () ce ∧
      (Blk.group g).Yields ce G cf ∧
      (G.code == first.code && G.maskCode == first.maskCode && L.k == first.k &&
        L.h == first.h) = true ∧
      (ioppStagesVerify answers choice.masksRide first rest row L mask).Yields cf () c' := by
  unfold ioppVerify at h
  obtain ⟨answers, ca, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨S, cb, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
  obtain ⟨_, cc, m3, k3⟩ := (Blk.yields_bind _ _ _ _ _).1 k2
  obtain ⟨h3, e3⟩ := (Blk.yields_must _ _ _).1 m3
  obtain ⟨⟨row, L⟩, cd, h4, k4⟩ := (Blk.yields_bind _ _ _ _ _).1 k3
  obtain ⟨_, ce, h5, k5⟩ := (Blk.yields_bind _ _ _ _ _).1 k4
  obtain ⟨G, cf, h6, k6⟩ := (Blk.yields_bind _ _ _ _ _).1 k5
  obtain ⟨_, cg, m7, k7⟩ := (Blk.yields_bind _ _ _ _ _).1 k6
  obtain ⟨h7, e7⟩ := (Blk.yields_must _ _ _).1 m7
  rw [e3] at h4
  rw [e7] at k7
  exact ⟨answers, ca, S, cb, row, L, cd, ce, G, cf, h1, h2, h3, h4, h5, h6, h7, k7⟩

/-- What rides in a code switch's message beside the new tables: nothing, or the mask of the next
stage's fold, or, before the last stage, the base case's masking oracle. -/
def stageOthers (ride : Bool) (next : IoppStage) (rest : List IoppStage) : Array OracleNotice :=
  if !ride then #[]
  else if rest.isEmpty then #[baseMaskNotice next.code next.maskCode 1 0]
  else #[foldMaskNotice (ioppFoldShape next {})]

/-- A stage that is not the last: the fold; a new group; the code switch into it; the mask that
rode with it, if masks ride; the stages that are left. Between them, values are noted. -/
theorem ioppStages_step_inv (answers : Nat) (ride : Bool) (cur next : IoppStage)
    (rest : List IoppStage) (row : GroupRow) (L : GroupLayout) (foldMask : Option Nat) (c c' : Ctx)
    (h : (ioppStagesVerify answers ride cur (next :: rest) row L foldMask).Yields c () c') :
    ∃ (rows : SingleRows) (c1 c2 : Ctx) (to : Nat) (c3 : Ctx) (s : Switched) (row' : GroupRow)
      (L' : GroupLayout) (c4 c5 c6 c7 c8 : Ctx) (mask : Option Nat),
      (foldVerify (ioppFoldShape cur L) row foldMask).Yields c rows c1 ∧
      (Blk.note "FOLD: target" rows.target).Yields c1 () c2 ∧
      (Blk.newGroup next.code next.maskCode).Yields c2 to c3 ∧
      (csVerify rows (switchTargetStage next.code next.maskCode next.k next.h answers) to
        (stageOthers ride next rest)).Yields c3 (s, row', L') c4 ∧
      (Blk.note "CS: target" row'.target).Yields c4 () c5 ∧
      (Blk.noteBy "CS: c'[0]" fun _ => row'.c.entry 0).Yields c5 () c6 ∧
      (Blk.note "CS: d'[0]" (row'.d.getD 0 zeroE)).Yields c6 () c7 ∧
      (Blk.note "CS: d's last entry" (row'.d.back?.getD zeroE)).Yields c7 () c8 ∧
      ((ride = true ∧ s.others[0]? = mask ∧ mask.isSome = true) ∨ (ride = false ∧ mask = none)) ∧
      (ioppStagesVerify answers ride next rest row' L' mask).Yields c8 () c' := by
  rw [ioppStagesVerify] at h
  obtain ⟨rows, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, c2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
  obtain ⟨to, c3, h3, k3⟩ := (Blk.yields_bind _ _ _ _ _).1 k2
  obtain ⟨⟨s, row', L'⟩, c4, h4, k4⟩ := (Blk.yields_bind _ _ _ _ _).1 k3
  obtain ⟨_, c5, h5, k5⟩ := (Blk.yields_bind _ _ _ _ _).1 k4
  obtain ⟨_, c6, h6, k6⟩ := (Blk.yields_bind _ _ _ _ _).1 k5
  obtain ⟨_, c7, h7, k7⟩ := (Blk.yields_bind _ _ _ _ _).1 k6
  obtain ⟨_, c8, h8, k8⟩ := (Blk.yields_bind _ _ _ _ _).1 k7
  cases ride with
  | true =>
    obtain ⟨mask, c9, m1, k9⟩ := (Blk.yields_bind _ _ _ _ _).1 k8
    obtain ⟨o, ca, m2, m3⟩ := (Blk.yields_bind _ _ _ _ _).1 m1
    obtain ⟨e2, f2⟩ := (Blk.yields_get _ _ _ _).1 m2
    obtain ⟨e3, f3⟩ := (Blk.yields_pure _ _ _ _).1 m3
    rw [f3, f2] at k9
    exact ⟨rows, c1, c2, to, c3, s, row', L', c4, c5, c6, c7, c8, mask, h1, h2, h3, h4, h5, h6,
      h7, h8, Or.inl ⟨rfl, by rw [e2, e3], by rw [e3]; rfl⟩, k9⟩
  | false =>
    obtain ⟨mask, c9, m1, k9⟩ := (Blk.yields_bind _ _ _ _ _).1 k8
    obtain ⟨e1, f1⟩ := (Blk.yields_pure _ _ _ _).1 m1
    rw [f1] at k9
    exact ⟨rows, c1, c2, to, c3, s, row', L', c4, c5, c6, c7, c8, mask, h1, h2, h3, h4, h5, h6,
      h7, h8, Or.inr ⟨rfl, e1⟩, k9⟩

/-- The last stage: its one main row and one mask row as single rows, and the base case. -/
theorem ioppStages_last_inv (answers : Nat) (ride : Bool) (cur : IoppStage) (row : GroupRow)
    (L : GroupLayout) (baseMask : Option Nat) (c c' : Ctx)
    (h : (ioppStagesVerify answers ride cur [] row L baseMask).Yields c () c') :
    ∃ R : SingleRows, ioppLastRows cur L row = some R ∧
      (baseVerify R baseMask 0).Yields c () c' := by
  rw [ioppStagesVerify] at h
  obtain ⟨R, c1, m1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨e1, f1⟩ := (Blk.yields_get _ _ _ _).1 m1
  rw [f1] at k1
  exact ⟨R, e1, k1⟩

/-! ## The start and the end of a run on a view -/

/-- The last question changes nothing. -/
theorem requireAllTested_inv (c c' : Ctx) (h : Blk.requireAllTested.Yields c () c') : c' = c := by
  unfold Blk.requireAllTested at h
  obtain ⟨S, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, e1⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨_, e2⟩ := (Blk.yields_must _ _ _).1 k1
  rw [e2, e1]

/-- The context from which a run on a view starts. -/
def startCtx (s : Start) (v : Fmt.View) : Ctx :=
  { ch := { dry := false, entries := s.entries, samples := s.samples, firstTree := s.firstTree,
            left := v.rounds, opened := v.opened },
    st := s.st, book := s.book, keepNotes := false }

/-- At the start no round is closed. -/
theorem startCtx_pending (s : Start) (v : Fmt.View) : (startCtx s v).ch.pending = v.rounds := rfl

/-- A yes of a decision is a run from the start after which no named test has failed. -/
theorem decides_yields (b : Blk Unit) (s : Start) (v : Fmt.View) (h : b.decides s v = true) :
    ∃ c' : Ctx, b.Yields (startCtx s v) () c' ∧ c'.failed = none := by
  obtain ⟨c', hr, _, _, _, _, _, hf⟩ := (Blk.decides_iff b s v).1 h
  refine ⟨c', ?_, hf⟩
  unfold Blk.runFrom Blk.runNamed at hr
  split at hr
  · exact hr
  · have hn : (none : Option (Unit × Ctx)) = some ((), c') := hr
    cases hn

end OnBytes.Slice

#print axioms OnBytes.Slice.requireAllTested_inv
#print axioms OnBytes.Slice.startCtx_pending
#print axioms OnBytes.Slice.decides_yields
#print axioms OnBytes.Slice.linkVerify_inv
#print axioms OnBytes.Slice.ioppVerify_inv
#print axioms OnBytes.Slice.ioppStages_step_inv
#print axioms OnBytes.Slice.ioppStages_last_inv
