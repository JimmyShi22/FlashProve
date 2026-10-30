-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/KeepsClose.lean: the closing of a link of a request's chain
(`ReqFrame.close`, OnBytes/Iop/Req.lean; `ChainCheck.close`, OnBytes/Model/ReqChain.lean), taken
apart whole where it succeeds on a view: the rounds at a link's end that belong to no sub-proof.

What it is for. A link's routine ends in `ChainCheck.close`. The rounds that this call takes are the
frame's own: the batching round of the link's group, then the fold of the group: the sum and the
draw of its coefficient, then one round for each row variable. To tie these rounds to a typed block
one needs each of these calls as a success of its own, at its own contexts, in order. The like for
a link's first call is OnBytes/Tie/Pv/Keeps/KeepsFirst.lean.

Main names:
  `CloseParts f cEnd c r c' …`: all calls of `ReqFrame.close` in a run: the link and its group; the
    test that the link's moments are through; `batVerify` on the link's group, from c to c4; the
    test that the group's layout has the group's numbers; `foldVerify`, on the row and the layout
    that the batching returned and on the frame's mask, from c6 to c7; the two notes; what is
    returned; at each context between: no dry run, and no mark of a failed test if there is none
    at cEnd.
  `close_parts`: `ReqFrame.close`, taken apart whole.
  `ChainCloseParts`, `chain_close_parts`: the same for `ChainCheck.close`: its test; the equation's
    row; the row is added to the group; then `CloseParts`; what is returned: the state with the
    closed frame, and no link under way.
Limits: one direction: from the call's success. Nothing is said on what a call's success means.

-/
import OnBytes.Tie.Pv.Keeps.KeepsFirstLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5.Close

open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5

/-- All calls of ReqFrame.close in a run on a view. -/
structure CloseParts (f : ReqFrame) (cEnd c : Ctx) (r : ReqFrame) (c' : Ctx)
    (L : Params.ReqLink) (G : ReqGroup) (row : GroupRow) (layout : GroupLayout)
    (rows : SingleRows) (c4 c6 c7 : Ctx) : Prop where
  link : f.shape.link[f.link]? = some L
  group : f.groups[f.link]? = some G
  due : (f.next == ReqNext.laterOrClose && f.moment == reqMoments L) = true
  bat : batVerify f.group c = .ok ((row, layout), c4)
  same : (layout.k == G.k && layout.h == G.h) = true
  note1 : Blk.note "REQ: the group row's target" row.target c4 = .ok ((), c6)
  fold : foldVerify (f.foldShape f.link layout) row f.mask c6 = .ok (rows, c7)
  note2 : Blk.note "REQ: FOLD's target" rows.target c7 = .ok ((), c')
  result : r = { f with rows := rows, mask := none, link := f.link + 1, next := .first }
  v4 : c4.ch.dry = false
  v6 : c6.ch.dry = false
  v7 : c7.ch.dry = false
  m0 : cEnd.failed = none → c.failed = none
  m4 : cEnd.failed = none → c4.failed = none
  m6 : cEnd.failed = none → c6.failed = none
  m7 : cEnd.failed = none → c7.failed = none

/-- **ReqFrame.close, taken apart whole.** -/
theorem close_parts (f : ReqFrame) {c : Ctx} {r : ReqFrame} {c' cEnd : Ctx}
    (d : View (m := Blk) c) (B : Clean (m := Blk) cEnd → Clean (m := Blk) c')
    (h : Runs f.close c r c') :
    ∃ L G row layout rows c4 c6 c7, CloseParts f cEnd c r c' L G row layout rows c4 c6 c7 := by
  unfold ReqFrame.close at h
  peel1_from h d B 1
  obtain ⟨t1, i1⟩ := runs_blkGet r1
  subst i1
  obtain ⟨t2, i2⟩ := runs_blkGet r2
  subst i2
  obtain ⟨t3, i3⟩ := runs_must r3
  subst i3
  obtain ⟨t5, i5⟩ := runs_must r5
  subst i5
  obtain ⟨iE, iE'⟩ := runs_pure' h
  subst iE
  subst iE'
  exact ⟨_, _, _, _, _, _, _, _,
    { link := t1, group := t2, due := t3, bat := r4, same := t5, note1 := r6, fold := r7,
      note2 := r8, result := rfl, v4 := d4, v6 := d6, v7 := d7, m0 := b0, m4 := b4, m6 := b6,
      m7 := b7 }⟩

/-- All calls of ChainCheck.close in a run on a view. -/
structure ChainCloseParts (k : ChainCheck) (eq : ReqEquation) (cEnd c : Ctx) (r : ChainCheck)
    (c' : Ctx) (rw : Row) (fr : ReqFrame) (c2 c3 : Ctx) : Prop where
  due : (k.inLink && k.moments == k.momentsDue) = true
  row : k.rows.row k.frame eq c = .ok (rw, c2)
  added : Blk.addRow k.group rw c2 = .ok ((), c3)
  closed : k.frame.close c3 = .ok (fr, c')
  v2 : c2.ch.dry = false
  v3 : c3.ch.dry = false
  m2 : cEnd.failed = none → c2.failed = none
  m3 : cEnd.failed = none → c3.failed = none

/-- **ChainCheck.close, taken apart whole.** -/
theorem chain_close_parts (k : ChainCheck) (eq : ReqEquation) {c : Ctx} {r : ChainCheck}
    {cOut cEnd : Ctx} (d : View (m := Blk) c) (B : Clean (m := Blk) cEnd → Clean (m := Blk) cOut)
    (h0 : k.close eq c = .ok (r, cOut)) :
    ∃ rw fr k2 k3 L G row layout rows k4 k6 k7,
      ChainCloseParts k eq cEnd c r cOut rw fr k2 k3 ∧
      CloseParts k.frame cEnd k3 fr cOut L G row layout rows k4 k6 k7 ∧
      r = { k with frame := fr, inLink := false } := by
  have hr : Runs (k.close eq) c r cOut := h0
  unfold ChainCheck.close at hr
  peel1_from hr d B 1
  obtain ⟨t1, i1⟩ := runs_must r1
  subst i1
  obtain ⟨iE, iE'⟩ := runs_pure' hr
  subst iE
  subst iE'
  obtain ⟨L, G, row, layout, rows, k4, k6, k7, P⟩ := close_parts k.frame d3 b4 r4
  exact ⟨_, _, _, _, L, G, row, layout, rows, k4, k6, k7,
    { due := t1, row := r2, added := r3, closed := r4, v2 := d2, v3 := d3, m2 := b2, m3 := b3 },
    P, rfl⟩

#print axioms close_parts
#print axioms chain_close_parts

end OnBytes.L5.Close
