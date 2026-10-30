-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/KeepsLaterFinish.lean: the two calls of a request's chain's frame that
OnBytes/Tie/Pv/Keeps/KeepsFirst.lean and KeepsClose.lean leave: the sending of a link's next moment
(`ReqFrame.later`, `ChainCheck.later`) and what follows the last link (`ReqFrame.finish`,
`ChainCheck.finish`), each taken apart whole where it succeeds on a view.

What it is for. To tie the rounds that these calls take to typed blocks one needs each inner call
as a success of its own, at its own contexts, in order. `later`: one sending with its own round of
answers. `finish`: the last code switch, in whose message the first mask of the last proximity test
rides, and that test.

Main names:
  `LaterParts f cEnd c r c' L ids j c3`: the link; the test that a moment is left; `sendVerify` on
    the notices of the moment's messages, from c to c3; `joinOwn`; what is returned.
  `later_parts`, `chain_later_parts`: `ReqFrame.later` and `ChainCheck.later`, taken apart whole.
  `FinishParts f cEnd c r c' G g s mask c3 c4`: the test that all links are closed; the last group;
    `beginLink`, from c to c3; `csSigmaVerify` on the rows that the last closing returned, with the
    one notice of the test's first mask, from c3 to c4; the mask's number; `ioppVerify`, from c4 to
    c'; what is returned.
  `finish_parts`, `chain_finish_parts`: `ReqFrame.finish` and `ChainCheck.finish`, taken apart
    whole.
  `FinishParts.rows_eq`: the switch is called on f.rows.
Limits: one direction: from the call's success. Nothing is said on what a call's success means.

-/
import OnBytes.Tie.Pv.Keeps.KeepsFirstLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5.Rest

open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5

/-- All calls of ReqFrame.later in a run on a view. -/
structure LaterParts (f : ReqFrame) (cEnd c : Ctx) (r : ReqFrame × Array Nat) (c' : Ctx)
    (L : Params.ReqLink) (ids : Array Nat) (j : ReqFrame) (c3 : Ctx) : Prop where
  link : f.shape.link[f.link]? = some L
  due : (f.next == ReqNext.laterOrClose && decide (f.moment < reqMoments L)) = true
  sent : sendVerify (ReqFrame.notices (f.atMoment f.moment)) true c = .ok (ids, c3)
  joined : ({ f with moment := f.moment + 1 } : ReqFrame).joinOwn (f.atMoment f.moment) ids c3 =
    .ok (j, c')
  result : r = (j, ids)
  v3 : c3.ch.dry = false
  m0 : cEnd.failed = none → c.failed = none
  m3 : cEnd.failed = none → c3.failed = none

/-- **ReqFrame.later, taken apart whole.** -/
theorem later_parts (f : ReqFrame) {c : Ctx} {r : ReqFrame × Array Nat} {c' cEnd : Ctx}
    (d : View (m := Blk) c) (B : Clean (m := Blk) cEnd → Clean (m := Blk) c')
    (h : Runs f.later c r c') : ∃ L ids j c3, LaterParts f cEnd c r c' L ids j c3 := by
  unfold ReqFrame.later at h
  peel1_from h d B 1
  obtain ⟨t1, i1⟩ := runs_blkGet r1
  subst i1
  obtain ⟨t2, i2⟩ := runs_must r2
  subst i2
  obtain ⟨iE, iE'⟩ := runs_pure' h
  subst iE
  subst iE'
  exact ⟨_, _, _, _,
    { link := t1, due := t2, sent := r3, joined := r4, result := rfl, v3 := d3, m0 := b0,
      m3 := b3 }⟩

/-- **ChainCheck.later, taken apart whole.** -/
theorem chain_later_parts (k : ChainCheck) {c : Ctx} {chk : ChainCheck} {cOut cEnd : Ctx}
    (d : View (m := Blk) c) (B : Clean (m := Blk) cEnd → Clean (m := Blk) cOut)
    (h0 : k.later c = .ok (chk, cOut)) :
    ∃ r L ids j k3, LaterParts k.frame cEnd c r cOut L ids j k3 ∧
      (k.inLink && decide (k.moments < k.momentsDue)) = true ∧
      chk = { k with frame := r.1, sent := r.2, moments := k.moments + 1 } := by
  have hr : Runs k.later c chk cOut := h0
  unfold ChainCheck.later at hr
  peel1_from hr d B 1
  obtain ⟨t1, i1⟩ := runs_must r1
  subst i1
  obtain ⟨iE, iE'⟩ := runs_pure' hr
  subst iE
  subst iE'
  obtain ⟨L, ids, j, k3, P⟩ := later_parts k.frame d1 b2 r2
  exact ⟨_, L, ids, j, k3, P, t1, rfl⟩

/-- All calls of ReqFrame.finish in a run on a view. -/
structure FinishParts (f : ReqFrame) (cEnd c : Ctx) (r : ReqFrame) (c' : Ctx) (G : ReqGroup)
    (g : ReqFrame) (s : Switched) (mask : Nat) (c3 c4 : Ctx) : Prop where
  due : (f.next == ReqNext.first && f.link == f.shape.link.length) = true
  group : f.groups[f.link]? = some G
  begin : f.beginLink c = .ok (g, c3)
  switch : csSigmaVerify g.rows G.target g.group #[foldMaskNotice (g.foldShape g.link {})] c3 =
    .ok (s, c4)
  maskIs : s.others[0]? = some mask
  test : ioppVerify g.group g.shape.last g.shape.choice (some mask) c4 = .ok ((), c')
  result : r = { g with next := .done, mask := none }
  v3 : c3.ch.dry = false
  v4 : c4.ch.dry = false
  m0 : cEnd.failed = none → c.failed = none
  m3 : cEnd.failed = none → c3.failed = none
  m4 : cEnd.failed = none → c4.failed = none

/-- **ReqFrame.finish, taken apart whole.** -/
theorem finish_parts (f : ReqFrame) {c : Ctx} {r : ReqFrame} {c' cEnd : Ctx}
    (d : View (m := Blk) c) (B : Clean (m := Blk) cEnd → Clean (m := Blk) c')
    (h : Runs f.finish c r c') :
    ∃ G g s mask c3 c4, FinishParts f cEnd c r c' G g s mask c3 c4 := by
  unfold ReqFrame.finish at h
  peel1_from h d B 1
  obtain ⟨t1, i1⟩ := runs_must r1
  subst i1
  obtain ⟨t2, i2⟩ := runs_blkGet r2
  subst i2
  obtain ⟨t5, i5⟩ := runs_blkGet r5
  subst i5
  obtain ⟨iE, iE'⟩ := runs_pure' h
  subst iE
  subst iE'
  exact ⟨_, _, _, _, _, _,
    { due := t1, group := t2, begin := r3, switch := r4, maskIs := t5, test := r6, result := rfl,
      v3 := d3, v4 := d4, m0 := b0, m3 := b3, m4 := b4 }⟩

/-- The last switch is called on what the last closing has returned. -/
theorem FinishParts.rows_eq {f : ReqFrame} {cEnd c : Ctx} {r : ReqFrame} {c' : Ctx} {G : ReqGroup}
    {g : ReqFrame} {s : Switched} {mask : Nat} {c3 c4 : Ctx}
    (P : FinishParts f cEnd c r c' G g s mask c3 c4) : g.rows = f.rows ∧ g.link = f.link := by
  obtain ⟨n, -, e⟩ := beginLink_same f P.begin
  rw [e]
  exact ⟨rfl, rfl⟩

/-- **ChainCheck.finish, taken apart whole.** -/
theorem chain_finish_parts (k : ChainCheck) {c cOut cEnd : Ctx}
    (d : View (m := Blk) c) (B : Clean (m := Blk) cEnd → Clean (m := Blk) cOut)
    (h0 : k.finish c = .ok ((), cOut)) :
    ∃ r G g s mask k3 k4, FinishParts k.frame cEnd c r cOut G g s mask k3 k4 ∧
      (!k.inLink && k.link == k.links) = true := by
  have hr : Runs k.finish c () cOut := h0
  unfold ChainCheck.finish at hr
  peel1_from hr d B 1
  obtain ⟨t1, i1⟩ := runs_must r1
  subst i1
  obtain ⟨-, iE'⟩ := runs_pure' hr
  subst iE'
  obtain ⟨G, g, s, mask, k3, k4, P⟩ := finish_parts k.frame d1 b2 r2
  exact ⟨_, G, g, s, mask, k3, k4, P, t1⟩

#print axioms later_parts
#print axioms chain_later_parts
#print axioms finish_parts
#print axioms chain_finish_parts

end OnBytes.L5.Rest
