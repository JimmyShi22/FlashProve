-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/KeepsFirst.lean: the first call of a link of a request's chain
(`ReqFrame.first`, OnBytes/Iop/Req.lean; `ChainCheck.first`, OnBytes/Model/ReqChain.lean), taken
apart whole where it succeeds on a view: the rounds at a link's beginning that belong to no
sub-proof.

What it is for. `LinkStep.first` (OnBytes/Tie/Pv/Keeps/KeepsChain.lean) says that the call
succeeded, from which context and to which. The rounds that it takes are: the round REPLY where the
link has plain scalars; then, at the first link, a sending with its own round of answers; at every
later link the code switch from the group before: a sending whose round of answers is closed by the
positions. To tie these rounds to typed blocks one needs each of these calls as a success of its
own, at its own contexts, in order.

Main names:
  `firstOthers f`: the oracle messages that go beside the carrying message in the link's first
    prover's message.
  `FirstParts f cEnd c r c' …`: all calls of `ReqFrame.first` in a run: the link and its group; the
    frame behind `beginLink`; the scalars received; the round REPLY was closed if and only if the
    link has plain scalars; at link 0 `sendVerify`, else `csSigmaVerify`, on that very list, from
    the context behind REPLY; the mask; `joinOwn`; what is returned; at each context between: no dry
    run, and no mark of a failed test if there is none at cEnd.
  `first_parts`: `ReqFrame.first`, taken apart whole.
  `joinOwn_same`, `FirstParts.plain_eq`: the frame that is returned holds the scalars received, the
    mask and the kept messages.
  `check_first_parts`: the same from `ChainCheck.first`; the state that it returns has the scalars
    received as its plain scalars.
One tactic is declared: `others_by t` closes a goal on `firstOthers f` by the fact t on the list as
the case at hand has it (the first link, or a later one).
Limits: one direction: from the call's success. Nothing is said on what a call's success means.

-/
import OnBytes.Tie.Pv.Keeps.KeepsChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5

open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- The oracle messages that go beside the carrying message in a link's first prover's message. -/
def firstOthers (f : ReqFrame) : Array OracleNotice :=
  ReqFrame.notices (f.atMoment 0) ++ #[foldMaskNotice (f.foldShape f.link {})] ++
    (if f.link == 0 then f.shape.atStart.toArray else #[])

/-- All calls of ReqFrame.first in a run on a view. -/
structure FirstParts (f : ReqFrame) (cEnd c : Ctx) (r : ReqFrame × Array Nat) (c' : Ctx)
    (L : Params.ReqLink) (G : ReqGroup) (g : ReqFrame) (plain : List E) (kept ids : Array Nat)
    (mask : Nat) (j : ReqFrame) (c4 c5 c6 c7 : Ctx) : Prop where
  isFirst : (f.next == ReqNext.first) = true
  link : f.shape.link[f.link]? = some L
  group : f.groups[f.link]? = some G
  begin : f.beginLink c = .ok (g, c4)
  heard : Blk.recvEs L.plain c4 = .ok (plain, c5)
  reply : (L.plain != 0) = true → Blk.closeEmpty "REPLY" c5 = .ok ((), c6)
  noReply : ¬(L.plain != 0) = true → c6 = c5
  sendFirst : (g.link == 0) = true →
    sendVerify (firstOthers f) true c6 = .ok (ids, c7) ∧ kept = g.keptBefore
  switch : ¬(g.link == 0) = true → ∃ s : Switched,
    csSigmaVerify g.rows G.target g.group (firstOthers f) c6 = .ok (s, c7) ∧
      kept = s.kept ∧ ids = s.others
  sizes : (ids.size == (firstOthers f).size) = true
  maskIs : ids[(f.atMoment 0).length]? = some mask
  joined : ({ g with plain := plain, keptBefore := kept, mask := some mask,
                     atStart := g.atStart ++ ids.extract ((f.atMoment 0).length + 1) ids.size }
    : ReqFrame).joinOwn (f.atMoment 0) (ids.extract 0 (f.atMoment 0).length) c7 = .ok (j, c')
  result : r = ({ j with next := .laterOrClose }, ids.extract 0 (f.atMoment 0).length)
  v4 : c4.ch.dry = false
  v5 : c5.ch.dry = false
  v6 : c6.ch.dry = false
  v7 : c7.ch.dry = false
  m0 : cEnd.failed = none → c.failed = none
  m4 : cEnd.failed = none → c4.failed = none
  m5 : cEnd.failed = none → c5.failed = none
  m6 : cEnd.failed = none → c6.failed = none
  m7 : cEnd.failed = none → c7.failed = none

theorem firstOthers_zero (f : ReqFrame) (h : (f.link == 0) = true) :
    firstOthers f = ReqFrame.notices (f.atMoment 0) ++ #[foldMaskNotice (f.foldShape f.link {})] ++
      f.shape.atStart.toArray := by
  unfold firstOthers
  rw [if_pos h]

theorem firstOthers_succ (f : ReqFrame) (h : ¬(f.link == 0) = true) :
    firstOthers f = ReqFrame.notices (f.atMoment 0) ++ #[foldMaskNotice (f.foldShape f.link {})] ++
      #[] := by
  unfold firstOthers
  rw [if_neg h]

/-- Closes a goal on `firstOthers f` by a fact on the list as the case at hand has it. -/
macro "others_by " t:term : tactic =>
  `(tactic| first
    | (rw [firstOthers_zero _ (by assumption)]; exact $t)
    | (rw [firstOthers_succ _ (by assumption)]; exact $t))

/-- **ReqFrame.first, taken apart whole.** -/
theorem first_parts (f : ReqFrame) {c : Ctx} {r : ReqFrame × Array Nat} {c' cEnd : Ctx}
    (d : View (m := Blk) c) (B : Clean (m := Blk) cEnd → Clean (m := Blk) c')
    (h : Runs f.first c r c') :
    ∃ L G g plain kept ids mask j c4 c5 c6 c7,
      FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7 := by
  unfold ReqFrame.first at h
  peel1_from h d B 1
  all_goals (
    obtain ⟨t1, i1⟩ := runs_must r1
    subst i1
    obtain ⟨t2, i2⟩ := runs_blkGet r2
    subst i2
    obtain ⟨t3, i3⟩ := runs_blkGet r3
    subst i3
    obtain ⟨i8a, i8⟩ := runs_pure' r8
    subst i8a
    subst i8
    obtain ⟨t9, i9⟩ := runs_must r9
    subst i9
    obtain ⟨t10, i10⟩ := runs_blkGet r10
    subst i10
    obtain ⟨iE, iE'⟩ := runs_pure' h
    subst iE
    subst iE')
  all_goals first
    | (
      obtain ⟨-, i6⟩ := runs_pure' r6
      subst i6
      first
        | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _,
            { isFirst := t1, link := t2, group := t3, begin := r4, heard := r5,
              reply := fun hx => absurd hx ‹¬(a2.plain != 0) = true›, noReply := fun _ => rfl,
              sendFirst := fun _ => ⟨by others_by r7, rfl⟩,
              switch := fun hx => absurd ‹(a4.link == 0) = true› hx,
              sizes := by others_by t9, maskIs := t10, joined := r11, result := rfl,
              v4 := d4, v5 := d5, v6 := d6, v7 := d7, m0 := b0, m4 := b4, m5 := b5, m6 := b6,
              m7 := b7 }⟩
        | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _,
            { isFirst := t1, link := t2, group := t3, begin := r4, heard := r5,
              reply := fun hx => absurd hx ‹¬(a2.plain != 0) = true›, noReply := fun _ => rfl,
              sendFirst := fun hx => absurd hx ‹¬(a4.link == 0) = true›,
              switch := fun _ => ⟨a7, by others_by r7, rfl, rfl⟩,
              sizes := by others_by t9, maskIs := t10, joined := r11, result := rfl,
              v4 := d4, v5 := d5, v6 := d6, v7 := d7, m0 := b0, m4 := b4, m5 := b5, m6 := b6,
              m7 := b7 }⟩)
    | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _,
        { isFirst := t1, link := t2, group := t3, begin := r4, heard := r5,
          reply := fun _ => r6, noReply := fun hx => absurd ‹(a2.plain != 0) = true› hx,
          sendFirst := fun _ => ⟨by others_by r7, rfl⟩,
          switch := fun hx => absurd ‹(a4.link == 0) = true› hx,
          sizes := by others_by t9, maskIs := t10, joined := r11, result := rfl,
          v4 := d4, v5 := d5, v6 := d6, v7 := d7, m0 := b0, m4 := b4, m5 := b5, m6 := b6,
          m7 := b7 }⟩
    | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _,
        { isFirst := t1, link := t2, group := t3, begin := r4, heard := r5,
          reply := fun _ => r6, noReply := fun hx => absurd ‹(a2.plain != 0) = true› hx,
          sendFirst := fun hx => absurd hx ‹¬(a4.link == 0) = true›,
          switch := fun _ => ⟨a7, by others_by r7, rfl, rfl⟩,
          sizes := by others_by t9, maskIs := t10, joined := r11, result := rfl,
          v4 := d4, v5 := d5, v6 := d6, v7 := d7, m0 := b0, m4 := b4, m5 := b5, m6 := b6,
          m7 := b7 }⟩

/-- joinOwn turns the list of the link's own oracle messages alone. -/
theorem joinOwn_same (f : ReqFrame) (sent : List Params.ReqMessage) (ids : Array Nat) {c : Ctx}
    {j : ReqFrame} {c' : Ctx} (h : Runs (f.joinOwn sent ids) c j c') :
    j = { f with own := f.own ++ ids } := by
  unfold ReqFrame.joinOwn at h
  obtain ⟨_, c1, _, h⟩ := HasRuns.runs_bind h
  obtain ⟨_, c2, _, h⟩ := HasRuns.runs_bind h
  exact (runs_pure' h).1

/-- The frame that the call returns holds the scalars that were received, and the mask. -/
theorem FirstParts.plain_eq {f : ReqFrame} {cEnd c : Ctx} {r : ReqFrame × Array Nat} {c' : Ctx}
    {L : Params.ReqLink} {G : ReqGroup} {g : ReqFrame} {plain : List E} {kept ids : Array Nat}
    {mask : Nat} {j : ReqFrame} {c4 c5 c6 c7 : Ctx}
    (h : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7) :
    r.1.plain = plain ∧ r.1.mask = some mask ∧ r.1.keptBefore = kept := by
  have e := joinOwn_same _ _ _ h.joined
  rw [h.result, e]
  exact ⟨rfl, rfl, rfl⟩

/-- **ChainCheck.first, taken apart whole.** -/
theorem check_first_parts (k : ChainCheck) {c : Ctx} {chk : ChainCheck} {cOut cEnd : Ctx}
    (d : View (m := Blk) c) (B : Clean (m := Blk) cEnd → Clean (m := Blk) cOut)
    (h0 : k.first c = .ok (chk, cOut)) :
    ∃ r L G g plain kept ids mask j c4 c5 c6 c7,
      FirstParts k.frame cEnd c r cOut L G g plain kept ids mask j c4 c5 c6 c7 ∧
      chk = { k with frame := r.1, sent := r.2, inLink := true, moments := 1 } ∧
      chk.plain = plain.toArray := by
  have hr : Runs k.first c chk cOut := h0
  unfold ChainCheck.first at hr
  peel1_from hr d B 1
  obtain ⟨-, i1⟩ := runs_must r1
  subst i1
  obtain ⟨iE, iE'⟩ := runs_pure' hr
  subst iE
  subst iE'
  obtain ⟨L, G, g, plain, kept, ids, mask, j, k4, k5, k6, k7, P⟩ := first_parts k.frame d1 b2 r2
  exact ⟨_, L, G, g, plain, kept, ids, mask, j, k4, k5, k6, k7, P, rfl,
    congrArg List.toArray P.plain_eq.1⟩

#print axioms first_parts
#print axioms check_first_parts

end OnBytes.L5
