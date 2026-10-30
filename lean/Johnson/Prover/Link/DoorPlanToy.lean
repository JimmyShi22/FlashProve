-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorPlanToy.lean: A TEST: DoorPlan (Johnson/Prover/Link/DoorPay.lean) CAN BE
MET: it holds at the toy's shape tinyP (Johnson/Prover/Link/ToyLink.lean) and the place's numbers
that the description itself makes of it (p12, Johnson/Prover/Link/ToyParts.lean).
DoorPlan: twenty-one facts on the link's public shape, the codes and the place's numbers alone. It
is one of the premises of door_premises (DoorPay.lean), which leads from the yes of the link's six
front blocks to TestFront, BatOwes and FrontOwes: three premises of door_yes (FormDoorLaws.lean: the
proximity test's front, the batching, the frame's question and the first fold say yes in a row).

What is checked when the file compiles.
  doorPlan_toy   A THEOREM: DoorPlan at these numbers, by the kernel's own evaluation of the public
      test (doorPlanOk, Johnson/Prover/Link/DoorPlanOk.lean).
  #guard lines   the test says yes; its list has 21 clauses (fixed by doorPlanL's own text: a
      tripwire); and FIVE CONTROLS: with one argument or one field turned (a pair of numbers, a
      stage, two Booleans, a number) just the clauses that are named here refuse. Why just these is
      not argued here.

Limits. One shape, small numbers. Nothing at the sizes of the programs. A #guard line is run by
Lean's evaluator (compiled code, outside the kernel) and leaves no theorem. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DoorPlanOk
import Johnson.Prover.Link.ToyParts

set_option autoImplicit false

namespace Johnson.Prover.Link.Toy
open OnBytes OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.K12 Desc.K15

/-- the numbers of the first and of the second stage's codes; `default` where the place's list `idx`
has no such entry -/
def iT : Nat × Nat := p12.idx.getD 0 default
def nT : Nat × Nat := p12.idx.getD 1 default

/-- the names of the clauses that refuse -/
def planNo (S : LinkShape) (K : Codes) (p : P12) (cur nxt : Fmt.M1.Stage) (i n : Nat × Nat) :
    List String :=
  ((doorPlanL S K p cur nxt i n).filter (!·.2)).map (·.1)

#guard doorPlanOk tinyLink tinyCodes p12 (st 0) (st 1) iT nT
#guard (doorPlanL tinyLink tinyCodes p12 (st 0) (st 1) iT nT).length = 21
-- controls
#guard planNo tinyLink tinyCodes p12 (st 0) (st 1) iT iT = ["idx1", "base1", "mask1"]
#guard planNo tinyLink tinyCodes p12 (st 1) (st 1) iT nT =
  ["base", "maskC", "layK", "layH", "freshRows"]
#guard planNo { tinyLink with masksAhead := false } tinyCodes p12 (st 0) (st 1) iT nT = ["ahead"]
#guard planNo tinyLink tinyCodes { p12 with early := false } (st 0) (st 1) iT nT = ["early"]
#guard planNo tinyLink tinyCodes { p12 with nums := { p12.nums with free := 2 } } (st 0) (st 1) iT
  nT = ["free"]

/-- **DoorPlan holds at the toy's numbers.** -/
theorem doorPlan_toy : DoorPlan tinyLink tinyCodes p12 (st 0) (st 1) iT nT :=
  doorPlan_of_ok (by decide +kernel)

end Johnson.Prover.Link.Toy

#print axioms Johnson.Prover.Link.Toy.doorPlan_toy
