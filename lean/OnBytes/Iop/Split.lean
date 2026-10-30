-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Split.lean: the block SPLIT: a row that reads oracle messages of two groups becomes
one row on each group.
C++ counterpart: blocks/iop/split.h (split_verify).

A proximity test reads one group. So a row <a1, messages of G1> + <a2, messages of G2> = t can go
into neither test. It is replaced by
    on G1:  <a1, ..> + kappa = t'          on G2:  <a2, ..> - kappa = t - t',
where kappa is a mask entry and the prover shows t'. The oracle message that holds kappa has mask
rows only and is a member of both groups. The two new rows add up to the old one. This needs both
tests to speak of the same kappa: the mask message was sent and sampled before t' is sent, which is
meant to fix kappa, and both tests take in its sample rows. Without that, a word close to two code
words with different kappa could let a false row pass as two true ones.

Order. t' comes before the first challenge of the test on either group: Blk.addRow refuses a row on
a group whose test has begun. The first test on a group that holds the mask message closes its
ledger, so one mask message serves the splits before one set of tests and no later ones.

The block's own text makes no test on a value. Blk.addRow tests of each new row that it has the
coefficient 0 on every entry of its group's messages that masks an answer to a sample. Round:
"SPLIT", in which the verifier says nothing.

Main definition: splitVerify.

Not claimed here: soundness or hiding.
-/
import OnBytes.Iop.Ground

namespace OnBytes

/-- SPLIT: splits a plain row between the groups g1 and g2, with the next free mask entry of
maskMessage, and adds the two halves to the groups as open rows. Fails unless the groups differ, the
row is plain, maskMessage has mask rows only and is a member of both groups, and each oracle message
of the row is a member of exactly one of the two. -/
def splitVerify (row : Row) (g1 g2 maskMessage : Nat) : Blk Unit := do
  let G1 ← Blk.group g1
  let G2 ← Blk.group g2
  let m ← Blk.oracle maskMessage
  Blk.must (g1 != g2 && row.kind == .plain && m.shape.mainRows == 0)
  Blk.must (G1.members.contains maskMessage && G2.members.contains maskMessage)
  Blk.must (row.oracles.all fun o => G1.members.contains o != G2.members.contains o)
  let inFirst (o : Nat) : Bool := G1.members.contains o
  let half (first : Bool) : Row :=
    { terms := row.terms.filter fun t => inFirst t.oracle == first
      units := row.units.filter fun u => inFirst u.oracle == first
      runs := row.runs.filter fun w => inFirst w.oracle == first
      forms := row.forms.filter fun f => inFirst f.oracle == first }
  let kappa ← Blk.takeMask maskMessage
  let share ← Blk.recvE
  Blk.closeEmpty "SPLIT"
  Blk.addRow g1 { (half true).addUnit maskMessage .mask kappa oneE with target := share }
  Blk.addRow g2 { (half false).addUnit maskMessage .mask kappa (negE oneE) with
    target := subE row.target share }

end OnBytes
