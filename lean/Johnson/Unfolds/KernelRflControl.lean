-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/KernelRflControl.lean: THE CONTROL OF `kernel_rfl` (Johnson/Unfolds/KernelRfl.lean):
this file compiles only if Lean's KERNEL refuses what the tactic lays at these three false
equations.

How. Each negative test is an `example` under `#guard_msgs`, with the message that Lean must log
written out in front of it: the file fails if the message is another one, or none. The messages of
N1 to N4 begin "(kernel)": so it is the kernel that has refused, not the tactic and not the
elaborator; and they show the laid term's type (`5 = 5`): so they also hold which side is laid.
  N1: a false equation on numbers, closed.
  N2: a false equation with a free letter.
  N3: a test of our kind (a Bool, made by `List.all`) that comes out `false`, stated `= true`,
      beside a free letter that nothing opens.
  N4: a TRUE equation that the kernel cannot see by computation (it hangs on the free letter): it is
      refused as well. The tactic can fail at a truth.
  N5: a goal that is no equation: here the tactic itself refuses.
  E: on "Why `example`" below, not on the kernel: behind the negative tests no constant `_example`
      is in the environment.
  P1, P2: two positive tests, closed and with a free letter. Their answers to `#print axioms` are
      written out under `#guard_msgs` too: the file fails if a positive test leans on anything.

Why `example`. The negative tests are examples: an example leaves no constant. THIS FILE DECLARES NO
NAME BUT P1 AND P2. NO FILE, ROOT OR ROLL-UP IMPORTS IT: it is compiled as a target of its own.

Limits. Three false equations, no more. That a NAMED false theorem is refused is not tested here, by
design. The messages are those of the toolchain at which the library stands (v4.29.1): another
toolchain may word them otherwise, and the file then fails until they are written anew. N3's message
holds the sign "↦": it leans on the lakefile's option pp.unicode.fun = true.

-/
import Johnson.Unfolds.KernelRfl

set_option autoImplicit false

namespace Johnson.Unfolds.KernelRflControl

/-! ## Negative tests -/

/--
error: (kernel) declaration type mismatch, 'Johnson.Unfolds.KernelRflControl._example' has type
  5 = 5
but it is expected to have type
  2 + 2 = 5
-/
#guard_msgs in
example : (2 + 2 : Nat) = 5 := by kernel_rfl

/--
error: (kernel) declaration type mismatch, 'Johnson.Unfolds.KernelRflControl._example' has type
  ∀ (n : Nat), 4 = 4
but it is expected to have type
  ∀ (n : Nat), [n, 1, 2].length = 4
-/
#guard_msgs in
example (n : Nat) : (n :: [1, 2]).length = 4 := by kernel_rfl

/--
error: (kernel) declaration type mismatch, 'Johnson.Unfolds.KernelRflControl._example' has type
  ∀ (n : Nat), true = true
but it is expected to have type
  ∀ (n : Nat), ((List.range 3).all fun i ↦ decide (i < 2) && [n, i].length == 2) = true
-/
#guard_msgs in
example (n : Nat) :
    ((List.range 3).all fun i => decide (i < 2) && (n :: [i]).length == 2) = true := by
  kernel_rfl

/--
error: (kernel) declaration type mismatch, 'Johnson.Unfolds.KernelRflControl._example' has type
  ∀ (n : Nat), false = false
but it is expected to have type
  ∀ (n : Nat), decide (n + 1 = n) = false
-/
#guard_msgs in
example (n : Nat) : decide (n + 1 = n) = false := by kernel_rfl

/--
error: kernel_rfl: the goal is no equation
-/
#guard_msgs in
example : True := by kernel_rfl

/--
error: Unknown identifier `_example`
-/
#guard_msgs in
#check _example

/-! ## Positive tests -/

/-- P1: closed. -/
theorem closed_yes : ((List.range 3).all fun i => decide (i < 3)) = true := by kernel_rfl

/-- P2: with a free letter that nothing opens. -/
theorem free_yes (n : Nat) :
    ((List.range 3).all fun i => decide (i < 3) && (n :: [i]).length == 2) = true := by
  kernel_rfl

end Johnson.Unfolds.KernelRflControl

/-- info: 'Johnson.Unfolds.KernelRflControl.closed_yes' does not depend on any axioms -/
#guard_msgs in
#print axioms Johnson.Unfolds.KernelRflControl.closed_yes

/-- info: 'Johnson.Unfolds.KernelRflControl.free_yes' does not depend on any axioms -/
#guard_msgs in
#print axioms Johnson.Unfolds.KernelRflControl.free_yes
