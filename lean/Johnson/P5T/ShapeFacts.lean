-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/ShapeFacts.lean: THREE CLOSED FACTS ON THE WRITTEN SHAPE OF A REQUEST AT THE FULL SIZE
(`shapeFull`, by Johnson/Goal/Numbers/RequestWritten.lean), AT EACH OF ITS 25 SEGMENTS: BY LEAN's
KERNEL. One definition with code and four theorems. No public file is read.
  `segShapeB bound L`: at one segment's part L of the shape: the number of its moments is at most
  bound; every oracle message has a moment below bound; some message has mask rows.
  `shape_ok`: **25 segments; the test accepts each at the bound 3.**
  `shape_counts`: 99 oracle messages in all; every segment has just 3 moments and just 1 message
  with mask rows.
  `shape_tight`: two negative tests and a count: at the bound 2 the first clause holds at no
  segment, and the second at none; at number 25 no segment stands.
  `shape_mem`: so the test accepts whatever stands at a number of the written shape.
Every number here was printed by the evaluator before it was typed.
Limits. The written value alone: that it is a verifier's is another file's
(Johnson/P5T/ShapeAtMg.lean). The full size alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Numbers.RequestWritten
import OnBytes.Iop.Req

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open OnBytes
open VerifiableInference.Desc.ReqLit (shapeFull)

/-- The three clauses at one segment's part of the shape. -/
def segShapeB (bound : Nat) (L : Params.ReqLink) : Bool :=
  decide (reqMoments L ≤ bound) && (L.messages.all fun x => decide (x.moment < bound)) &&
    L.messages.any fun x => x.shape.maskRows != 0

set_option maxRecDepth 1000000 in
/-- **By the kernel: 25 segments; the test accepts each at the bound 3.** -/
theorem shape_ok : (shapeFull.link.length, shapeFull.link.all (segShapeB 3)) = (25, true) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: what it ranges over. -/
theorem shape_counts :
    ((shapeFull.link.map fun L => L.messages.length).foldl (· + ·) 0,
      shapeFull.link.all fun L => reqMoments L == 3,
      shapeFull.link.all fun L => (L.messages.filter fun x => x.shape.maskRows != 0).length == 1) =
      (99, true, true) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: at the bound 2 each of the first two clauses holds at no segment; at number 25 no
segment stands. -/
theorem shape_tight :
    ((shapeFull.link.filter fun L => decide (reqMoments L ≤ 2)).length,
      (shapeFull.link.filter fun L => L.messages.all fun x => decide (x.moment < 2)).length,
      (shapeFull.link[25]?).isSome) = (0, 0, false) := by decide +kernel

/-- The test accepts whatever stands at a number of the written shape. -/
theorem shape_mem {m : Nat} {L : Params.ReqLink} (h : shapeFull.link[m]? = some L) :
    segShapeB 3 L = true :=
  List.all_eq_true.1 (congrArg Prod.snd shape_ok) L (List.mem_of_getElem? h)

end P5T

#print axioms P5T.shape_ok
#print axioms P5T.shape_counts
#print axioms P5T.shape_tight
#print axioms P5T.shape_mem
