-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Att/AttBorders.lean: the contexts of a run of the verifier on bytes at the borders of
the nine places of an attention link.

A link of a request's chain is planned as nine stretches of rounds: the code switch; the lookup on
the calls; the sub-proof's own rounds; the sending of the reads; the draw of the matrix; the sending
of the digits; the lookup on the digits; the batching element; the closing of the link. This file
names, on the port's side alone, the contexts of a run between these stretches, with the port's own
call that takes each stretch.

Main names:
  AttBorders: ten contexts b0 to b9, three more (s5, s8, s9) at which a call begins behind calls
    that take no round, and the link's end bE. Between them the successes of ChainCheck.first,
    Forest.pad, the three routines of the own rounds (OwnCut, OnBytes/Tie/Pv/Att/HearCut.lean),
    rootInH, drawMatrixF, rootInH, Forest.pad, t2Batch and doorH. At s5, s8, s9 and bE the rounds
    that are left are those of b4, b7, b8 and b9. In none of the fourteen contexts is a message open
    (PscRun.Clean, OnBytes/Tie/Pv/Psc/PscView.lean). What holds of the entry and the draws of every
    round that is still to be taken at b0 holds of those at each later context (PendAll,
    OnBytes/Tie/Pv/Keeps/KeepsPend.lean: NzCtx and OkCtx are of that form).
  Rests c c': a call from c to c' has begun no round and taken none. Rests.trans, Rests.clean.

Limits: a record, a definition and two consequences. That a run has such contexts is not shown in
this file. No typed letter occurs.
-/
import OnBytes.Tie.Pv.Att.HearCut
import OnBytes.Tie.Pv.Keeps.KeepsPend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Attention

/-- The contexts of a run at the borders of the nine places of an attention link. -/
structure AttBorders (P : Attention.Plan) (check chk : ChainCheck) (f : Attention.First)
    (Fa F0 F1 F2 G F3 F4a F4b F4 F5 F6 F12 F13 : Fork) (L1 L2 L3 L4 L' : LinkCtx)
    (tl1 tlM : HTailF2) (g : Forest.Heard) (laid : Nat)
    (b0 b1 b2 m1 m2 b3 b4 s5 b5 b6 b7 s8 b8 s9 b9 bE : Ctx) : Prop where
  /-- place 1: the code switch -/
  first : check.first b0 = .ok (chk, b1)
  /-- place 2: the lookup on the calls -/
  look : Forest.pad (P.S.calls.map (·.call)) P.fs.pub P.lid Fa b1 = .ok ((f.g, F0), b2)
  /-- place 3: the own rounds -/
  own : OwnCut P f F0 F1 F2 G b2 m1 m2 b3
  /-- place 4: the sending of the reads -/
  reads : rootInH [P.iU3] L1 G b3 = .ok ((((), L2), F3), b4)
  at5 : s5.ch.left = b4.ch.left
  /-- place 5: the draw of the matrix -/
  draw : tl1.drawMatrixF F3 s5 = .ok ((tlM, F4a), b5)
  /-- place 6: the sending of the digits -/
  digits : rootInH [tlM.ix.ZZ, tlM.ix.BZ] L2 F4a b5 = .ok ((((), L3), F4b), b6)
  /-- place 7: the lookup on the digits -/
  look7 : Forest.pad #[tlM.z1.call, tlM.z2.call] tlM.f9.pub tlM.lidb F4b b6 = .ok ((g, F4), b7)
  at8 : s8.ch.left = b7.ch.left
  /-- place 8: the batching element -/
  batch : t2Batch F5.next L3 F5 s8 = .ok ((((), L4), F6), b8)
  at9 : s9.ch.left = b8.ch.left
  /-- place 9: the closing of the link -/
  door : doorH laid L4 F12 s9 = .ok ((((), L'), F13), b9)
  atE : bE.ch.left = b9.ch.left
  clean0 : PscRun.Clean b0
  clean1 : PscRun.Clean b1
  clean2 : PscRun.Clean b2
  clean3 : PscRun.Clean b3
  clean4 : PscRun.Clean b4
  clean5' : PscRun.Clean b5
  clean6 : PscRun.Clean b6
  clean7 : PscRun.Clean b7
  clean8' : PscRun.Clean b8
  clean9' : PscRun.Clean b9
  clean5 : PscRun.Clean s5
  clean8 : PscRun.Clean s8
  clean9 : PscRun.Clean s9
  cleanE : PscRun.Clean bE
  /-- what holds of every round that is still to be taken at b0 holds of those at the later ones -/
  pend : ∀ Q : Fmt.Entry → Fmt.Drawn → Prop, Keeps.Pend.PendAll Q b0 →
    Keeps.Pend.PendAll Q b1 ∧ Keeps.Pend.PendAll Q b2 ∧ Keeps.Pend.PendAll Q b3 ∧
    Keeps.Pend.PendAll Q b4 ∧ Keeps.Pend.PendAll Q s5 ∧ Keeps.Pend.PendAll Q b5 ∧
    Keeps.Pend.PendAll Q b6 ∧ Keeps.Pend.PendAll Q b7 ∧ Keeps.Pend.PendAll Q s8 ∧
    Keeps.Pend.PendAll Q b8 ∧ Keeps.Pend.PendAll Q s9 ∧ Keeps.Pend.PendAll Q b9 ∧
    Keeps.Pend.PendAll Q bE

/-- A call has begun no round and taken none: the open message and the rounds that are left are as
they were. -/
def Rests (c c' : Ctx) : Prop := c'.ch.cur = c.ch.cur ∧ c'.ch.left = c.ch.left

theorem Rests.trans {a b c : Ctx} (h : Rests a b) (k : Rests b c) : Rests a c :=
  ⟨k.1.trans h.1, k.2.trans h.2⟩

theorem Rests.clean {c c' : Ctx} (h : Rests c c') (d : c'.ch.dry = false) (k : PscRun.Clean c) :
    PscRun.Clean c' := ⟨d, h.1.trans k.2⟩

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.Rests.clean
