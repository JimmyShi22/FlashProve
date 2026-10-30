-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/K3Some.lean: what is left of the named test `P5J.At.k3SeatsB`
(Johnson/P5J/Rad3Seat3Tests.lean) once four of its six tests at each segment are paid: the two that
read the radii. One definition, one theorem with its proof. It stands in a file of its own, over
that file alone, so that a sheet can evaluate the test under its own name.

Main names. Zp: a public part. lay: the layout file's bytes.
  `At.k3SomeB Zp lay`: at every written segment l: `At.callsSomeB Zp lay l` and
    `At.digSomeB Zp lay l`.
  `At.k3SomeB_of`: the whole test gives it.

Limits. It is not shown to accept at any public part. Nothing on soundness.

-/
import Johnson.P5J.Rad3Seat3Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)

/-- What is left of `At.k3SeatsB`: at every segment the two of its six tests that read the radii. -/
def At.k3SomeB (Zp : ProofFile.Pub) (lay : ByteArray) : Bool :=
  (List.range At.links.length).all fun l => At.callsSomeB Zp lay l && At.digSomeB Zp lay l

/-- The whole test gives what is left of it. -/
theorem At.k3SomeB_of {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} {lay : ByteArray}
    (h : At.k3SeatsB Zp cF lay = true) : At.k3SomeB Zp lay = true := by
  refine List.all_eq_true.2 fun l hl => ?_
  obtain ⟨-, -, a, -, b, -⟩ := At.k3SeatsB_at Zp cF lay h l (List.mem_range.1 hl)
  simp only [Bool.and_eq_true]
  exact ⟨a, b⟩

end P5J

#print axioms P5J.At.k3SomeB_of
