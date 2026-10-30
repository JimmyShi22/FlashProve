-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/PossAtK2.lean: code switching (the kind K2): THE POSITIONS THAT A SWITCH's
DECLARED ROUNDS SAMPLE ARE ITS PARAMETER `positions`, at every size; so at a sub-protocol that
sits over the kind; and what is then left of "`possAt bs n m = d`". Four theorems. No sub-protocol
imports this file.
Why. `Numbers.atBlocks` (Johnson/Desc/First/NumbersAtBlocks.lean) reads, for the class "position"
of rows, `possAt bs n m`: it finds among the sub-protocols the one of the kind K2 at segment m and
sums `entry.poss` over its declared rounds (`possOf`, Johnson/Desc/First/RowsAtPlan.lean). The
switch's debts (`rows_debts`, Johnson/Top/H0/Tw/K2C/RowsDebts.lean) ask that this be the switch's
own number of positions. No evaluation is wanted for that: it is so by the kind's text.
  `possOf_k2`: `K2.rounds p` (Johnson/Top/H0/Tw/K2C/Kind.lean) declares two rounds: `SEND seed`,
  whose entry names no positions, and `LOC`, with `poss := p.positions`.
  `possOf_sits`: so at every b with `Sits b (codeSwitchKind p) enter leave` (Johnson/Desc/K12/Law/Sits.lean):
  its field `rounds`.
  `possAt_found`: where the search finds b, `possAt bs n m = possOf b`.
  `possAt_sits`: **so `possAt bs n m = p.positions`, where the search finds a sub-protocol that
  sits over `codeSwitchKind p`.**
Limits. WHAT IS LEFT, BY NAME: hf: that the search at segment m finds that sub-protocol: a fact on
the places of the sub-protocols in order. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H0.Tw.K2C.Kind
import Johnson.Desc.K12.Law.Sits
import Johnson.Desc.First.NumbersAtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open VerifiableInference.Desc (Block)
open H2K.JointK (Sits)

/-- The kind's two declared rounds sample `p.positions` positions. -/
theorem possOf_k2 {Cl : Type} (p : P2) : possOf (codeSwitchKind (Cl := Cl) p) = p.positions := by
  unfold possOf
  show ((rounds p).map fun d => d.entry.poss).sum = p.positions
  simp [rounds]

/-- So does every sub-protocol that sits over the kind. -/
theorem possOf_sits {St Cl Cl' : Type} {b : Block St Cl} {p : P2} {enter : St → Except String S}
    {leave : St → S → Except String St} (h : Sits b (codeSwitchKind (Cl := Cl') p) enter leave) :
    possOf b = p.positions := by
  unfold possOf
  rw [h.rounds]
  exact possOf_k2 p

/-- Where the search finds b, the table's number is b's. -/
theorem possAt_found {St Cl : Type} {bs : List (Block St Cl)} {n m : Nat} {b : Block St Cl}
    (hf : (bs.find? fun b => b.place.kind == .K2 && b.place.link.getD n == m) = some b) :
    possAt bs n m = possOf b := by
  unfold possAt
  rw [hf]
  rfl

/-- **The table's number of positions at segment m is the switch's own.** -/
theorem possAt_sits {St Cl Cl' : Type} {bs : List (Block St Cl)} {n m : Nat} {b : Block St Cl}
    {p : P2} {enter : St → Except String S} {leave : St → S → Except String St}
    (hf : (bs.find? fun b => b.place.kind == .K2 && b.place.link.getD n == m) = some b)
    (h : Sits b (codeSwitchKind (Cl := Cl') p) enter leave) : possAt bs n m = p.positions := by
  rw [possAt_found hf, possOf_sits h]

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.possOf_k2
#print axioms VerifiableInference.Desc.First.K2.possOf_sits
#print axioms VerifiableInference.Desc.First.K2.possAt_found
#print axioms VerifiableInference.Desc.First.K2.possAt_sits
