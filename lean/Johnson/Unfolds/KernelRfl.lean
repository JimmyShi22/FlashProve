-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/KernelRfl.lean: the tactic `kernel_rfl`. It closes a goal `a = b` with the term
`Eq.refl b` and does not ask the elaborator whether a and b are the same. Lean's kernel is asked,
when the theorem is added, as of every proof.

What it does. A tactic hands Lean a proof term. `rfl` first lets the elaborator compare the two
sides; the kernel compares them a second time when the declaration is added. `kernel_rfl` leaves the
first comparison out. `decide +kernel` does the like for a decision, but takes no goal with free
variables; this tactic takes them.

It proves nothing by itself. Where a and b are not the same by computation, or the kernel does not
get far enough to see that they are, the kernel refuses the declaration ("(kernel) declaration type
mismatch", "(kernel) deep recursion detected"). The tactic adds no axiom and cannot pass the kernel
by: while the kernel's check is on (term (5)), no theorem WITH A PROOF comes of it that the kernel
has not checked. Johnson/Unfolds/KernelRflControl.lean holds the refusal at three false equations by
tests that the build itself checks.

What a user must know. A theorem by `kernel_rfl` counts only in a file that compiles without an
error, with its own answer to `#print axioms` read by name.

Why it is wanted. At a closed computation with free letters in it (a maker of the public part, run
at all values of the parameter file's free numbers at once) `decide +kernel` does not apply, and the
elaborator's comparison is far slower than the kernel's. Measured once, at one statement that the
kernel checks in 40 s: `rfl` met the default limit of heartbeats after 18 s; with the limit lifted
it was not through after 300 s.

Which side. `Eq.refl b`, not `Eq.refl a`: in our uses a is a long computation and b its short value
(`true`), so the stored proof holds the short side alone. The kernel's work is one comparison of a
with b either way.

The terms of its use in this library.
  (1) It is to be defined once, here: no other file is to define its like.
  (2) The control beside it compiles only if the kernel refuses three false equations laid by it.
  (3) Every theorem that uses it has its line `#print axioms`, and the answer holds nothing but
      `propext`, `Classical.choice`, `Quot.sound`.
  (4) The release's audit counts its uses.
  (5) The option that switches the kernel's check off stands nowhere in the library, the lakefile
      or a build's command line; nor does any other means of adding a declaration unchecked.
  (6) In the whole library no named declaration stands under `#guard_msgs`: a negative test is an
      `example`, or is stated positively (`… = false`).
Nothing here enforces (4), (5), (6), a search for copies of the seven lines, or a replay of the
compiled files through a kernel.

Limits. Meta code: seven lines that run in the elaborator. It fails at goals that are equations
only after unfolding. Its failure comes behind the proof, at the declaration: `first`, `try` and the
like never see it. What the kernel's comparison costs is the user's to measure. With free letters
in a term the kernel has been seen to fail at a computation that it bears without them ("deep
recursion detected"); the cause is not known. This file may be imported by no module below the
verifier program's root: the audit's step on the program's source takes no code that programs Lean.

-/
import Lean.Elab.Tactic

namespace Johnson.Unfolds

open Lean Elab Tactic in
/-- Closes `a = b` with `Eq.refl b`. The elaborator does not compare a with b: the kernel does, when
the declaration is added, and refuses it where they differ. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (α, _, b) := t.eq? | throwError "kernel_rfl: the goal is no equation"
  let u ← Meta.getLevel α
  g.assign (mkApp2 (mkConst ``Eq.refl [u]) α b)
  replaceMainGoal []

end Johnson.Unfolds
