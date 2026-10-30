-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/LitRows.lean: the records of Row.lean at the switches of a proof's first
chain, written out for both examples, 5 and 25; and: among the 25 five are different. Definitions,
and three small theorems. No test is evaluated here.

The long lists are not written anew: a record takes its setting, codes, lists and radius from the
written values of Johnson/G/PackLit.lean, LinkLit.lean, BatAtFull.lean, SwitchAtSmall.lean and
SwitchPricesLit.lean, by its number. What is written here: which group stands in front, which group
prices the samples, which members are kept, one tree, and the rider: one mask row under mask code 0,
no sample.
  rowLit: a record from these values
  tableSmallLit, tableFullLit: the 5 and the 25 records, in the order of the chain
  full0, fullOdd, fullEven, full23, full24; full_is: the five different records of the full example;
      the 25 are these, in a written order: by definition
  full_all: a test that says yes at the five says yes at all 25. smallAt, small_all: the like for
      the 5 of the small example
WHY: a file that lets Lean's kernel evaluate a test at all 25 records in one theorem takes several
GiB; at five records, a theorem each, checked one after another (the files that evaluate set
Elab.async false), it stays light.
Limits: written numbers. That these are the planner's at the two examples' public files is not shown
by a theorem. Only the switches of a proof's first chain. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.Row
import Johnson.G.SwitchPricesLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params Johnson.G

/-- A record from written values: number i of the lists in front and of the sendings; g: the group
in front; pg: the group that prices the samples. -/
def rowLit (cs : Codes) (links sends : List (List (OracleShape × ℕ))) (rad i : ℕ) (g pg : GroupSize)
    (kept : List ℕ) : SwRow :=
  { set := setLit, cs := cs, lo := links.getD i [], g := g, rad := rad, l := sends.getD i []
    o := Johnson.G.oOf cs pg (sends.getD i []), roots := 1, kept := kept,
    rider := { maskRows := 1, maskCode := 0, answers := 0 } }

/-- The 5 switches of the small example. -/
def tableSmallLit : List SwRow :=
  [rowLit codesSmall2 linksSmallLit swSendsSmall radSmall 0 (grpSmall 9 8 false) (grpSmall 9 8
      false) [1, 2],
    rowLit codesSmall2 linksSmallLit swSendsSmall radSmall 1 (grpSmall 7 2 false) (grpSmall 9 8
        false) [2],
    rowLit codesSmall2 linksSmallLit swSendsSmall radSmall 2 (grpSmall 9 8 false) (grpSmall 9 8
        false) [3, 4],
    rowLit codesSmall2 linksSmallLit swSendsSmall radSmall 3 (grpSmall 7 2 false) (grpSmall 9 8
        false) [2],
    rowLit codesSmall2 linksSmallLit swSendsSmall radSmall 4 (grpSmall 8 1 false) (grpSmall 1 1
        true) []]

/-- The 25 switches of the full example: the links alternate; the first has no target in front; the
last leads into the last test. -/
def tableFullLit : List SwRow :=
  (List.range 25).map fun i =>
    if i = 24 then rowLit codesFull2 linksFullLit swSendsFull radFull i (grpFull 8 1 false) (grpFull
        1 1 true) []
    else if i % 2 = 1 then rowLit codesFull2 linksFullLit swSendsFull radFull i (grpFull 7 4 false)
        (grpFull 8 16 false) [2]
    else rowLit codesFull2 linksFullLit swSendsFull radFull i (grpFull 8 16 false) (grpFull 8 16
        false) (if i = 0 then [1, 2] else [3, 4])

/-! ### The different records, each once

Among the 25 records of the full example five are different. A test is evaluated at each of the five
in a theorem of its own, and holds at all 25 by `full_all`: so a file that evaluates a test stays
light. -/

/-- Number 0. -/
def full0 : SwRow :=
  rowLit codesFull2 linksFullLit swSendsFull radFull 0 (grpFull 8 16 false) (grpFull 8 16 false)
    [1, 2]

/-- The odd numbers up to 21. -/
def fullOdd : SwRow :=
  rowLit codesFull2 linksFullLit swSendsFull radFull 1 (grpFull 7 4 false) (grpFull 8 16 false) [2]

/-- The even numbers from 2 to 22. -/
def fullEven : SwRow :=
  rowLit codesFull2 linksFullLit swSendsFull radFull 2 (grpFull 8 16 false) (grpFull 8 16 false)
    [3, 4]

/-- Number 23. -/
def full23 : SwRow :=
  rowLit codesFull2 linksFullLit swSendsFull radFull 23 (grpFull 7 4 false) (grpFull 8 16 false) [2]

/-- Number 24. -/
def full24 : SwRow :=
  rowLit codesFull2 linksFullLit swSendsFull radFull 24 (grpFull 8 1 false) (grpFull 1 1 true) []

/-- The 25 records are these five, in this order. -/
theorem full_is : tableFullLit =
    [full0, fullOdd, fullEven, fullOdd, fullEven, fullOdd, fullEven, fullOdd, fullEven, fullOdd,
    fullEven, fullOdd, fullEven, fullOdd, fullEven, fullOdd, fullEven, fullOdd, fullEven, fullOdd,
    fullEven, fullOdd, fullEven, full23, full24] := rfl

/-- **A test that says yes at the five different records says yes at all 25.** -/
theorem full_all (T : SwRow → Bool) (h0 : T full0 = true) (h1 : T fullOdd = true)
    (h2 : T fullEven = true) (h3 : T full23 = true) (h4 : T full24 = true) :
    (tableFullLit.all T) = true := by
  rw [full_is]
  simp only [List.all_cons, List.all_nil, h0, h1, h2, h3, h4, Bool.and_self]

/-- The small example's record number i. -/
def smallAt (i : ℕ) : SwRow := tableSmallLit.getD i full24

/-- **A test that says yes at each of the 5 records of the small example.** -/
theorem small_all (T : SwRow → Bool) (h0 : T (smallAt 0) = true) (h1 : T (smallAt 1) = true)
    (h2 : T (smallAt 2) = true) (h3 : T (smallAt 3) = true) (h4 : T (smallAt 4) = true) :
    (tableSmallLit.all T) = true := by
  have e : tableSmallLit = [smallAt 0, smallAt 1, smallAt 2, smallAt 3, smallAt 4] := rfl
  rw [e]
  simp only [List.all_cons, List.all_nil, h0, h1, h2, h3, h4, Bool.and_self]

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.full_is
#print axioms VerifiableInference.Desc.First.K2Caller.full_all
#print axioms VerifiableInference.Desc.First.K2Caller.small_all
