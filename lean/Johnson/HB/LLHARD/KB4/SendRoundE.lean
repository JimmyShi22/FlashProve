-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/SendRoundE.lean: the number of the round that sends a chain's n-th tree, in a
way that Lean's kernel can evaluate at a long list of rounds. General in the list: no value is
treated.

Two routines of the tests on the plan have one text: sendRound (Johnson/Desc/Block.lean, read by
beforeAt) and BookPlan.roundOfRoot (Johnson/Desc/BookPlan.lean, read by inTime). Each descends along
the rounds and adds 1 on the way back: a recursion as deep as the number of the sending round, and
an answer that is a tower of additions of that height. The twin carries the number along, made a
numeral at each step (Johnson.G.force, Johnson/G/Eager.lean), and returns it at once.

Main names.
  sendRoundE a l n: the twin: a plus the round's number.
  sendRoundE_eq: sendRoundE a l n = (sendRound l n).map (· + a).
  sendRound_eq, roundOfRoot_eq: so each of the two routines is sendRoundE 0.
  sendRound_of, roundOfRoot_of: the routine's value from an evaluation of the twin.
Limits. That the kernel gets through a given list is seen where a theorem is checked, not shown
here. Nothing on soundness.

-/
import Johnson.Desc.Block
import Johnson.G.Eager

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc
open Johnson.G (force force_eq)

/-- a plus the number of the round that sends the oracle message number n, both from 0. -/
def sendRoundE : Nat → List Fmt.DeclaredRound → Nat → Option Nat
  | _, [], _ => none
  | a, r :: l, n =>
    if n < r.entry.roots then some a
    else force (a + 1) fun a' => force (n - r.entry.roots) fun n' => sendRoundE a' l n'

theorem sendRoundE_eq (l : List Fmt.DeclaredRound) :
    ∀ a n, sendRoundE a l n = (sendRound l n).map (· + a) := by
  induction l with
  | nil => intro a n; rfl
  | cons r l ih =>
    intro a n
    unfold sendRoundE sendRound
    split
    · simp
    · rw [force_eq, force_eq, ih, Option.map_map]
      congr 1
      funext x
      simp only [Function.comp]
      omega

theorem sendRound_eq (l : List Fmt.DeclaredRound) (n : Nat) : sendRound l n = sendRoundE 0 l n := by
  rw [sendRoundE_eq]
  cases sendRound l n <;> rfl

/-- The two routines have one text. -/
theorem roundOfRoot_sendRound (l : List Fmt.DeclaredRound) :
    ∀ n, BookPlan.roundOfRoot l n = sendRound l n := by
  induction l with
  | nil => intro n; rfl
  | cons r l ih =>
    intro n
    unfold BookPlan.roundOfRoot sendRound
    rw [ih]

theorem roundOfRoot_eq (l : List Fmt.DeclaredRound) (n : Nat) :
    BookPlan.roundOfRoot l n = sendRoundE 0 l n := by
  rw [roundOfRoot_sendRound, sendRound_eq]

theorem sendRound_of {l : List Fmt.DeclaredRound} {n : Nat} {x : Option Nat}
    (h : sendRoundE 0 l n = x) : sendRound l n = x := (sendRound_eq l n).trans h

theorem roundOfRoot_of {l : List Fmt.DeclaredRound} {n : Nat} {x : Option Nat}
    (h : sendRoundE 0 l n = x) : BookPlan.roundOfRoot l n = x := (roundOfRoot_eq l n).trans h

end Johnson.KB4

#print axioms Johnson.KB4.sendRoundE_eq
#print axioms Johnson.KB4.sendRound_eq
#print axioms Johnson.KB4.roundOfRoot_sendRound
#print axioms Johnson.KB4.roundOfRoot_eq
#print axioms Johnson.KB4.sendRound_of
#print axioms Johnson.KB4.roundOfRoot_of
