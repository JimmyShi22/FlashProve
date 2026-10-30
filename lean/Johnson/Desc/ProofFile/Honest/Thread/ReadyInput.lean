-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ReadyInput.lean: a condition on the input of a prover's side in
the first or the second chain: it is an input that `ready` (Honest/Frame.lean) could prepare, as far
as the index, the instance and the trace go, at an instance that passes the description's test. It
is meant as a value of the parameter `valid` of a `Thread` (Honest/Thread/Thr.lean). General in the
description and the prover: no kind, no choice of fields and no size is named. One definition, two
lemmas.

  `ReadyInput`            the condition
  `tests_inRange`         where `readyTests` returns, the index is in range
  `readyInput_of_ready`   the input that `ready` prepares meets the condition, if the instance
     passes `FileDescription.okStart`

Why. `ready` makes the input from its arguments and from the prover's own function `trace`: the
input's trace is `H.trace` at the input's own index and instance. So a lemma that needs to know what
the trace is can take it from this condition, with the index named by the field `w₀`, and where the
invariant is entered the condition costs no hypothesis beyond "`ready` returns" and
"`okStart` passes".

Limits.
  * The condition holds of no input at a request at which the prover's `trace` is `none`. `ready`
    returns an error at such a request before any part is played, and every statement that has the
    invariant at this `valid` among its hypotheses says nothing there. At the full-size choice of
    fields (`fullIn`, Honest/AtPureFullIn.lean) the trace is `none`, among others, wherever a range
    condition of the integer program fails on the request's tokens.
  * It does not say that the trace is a correct run of a model: that depends on the prover's
    `trace`.
  * The field `rc` is free.
  * At a prover whose `trace` is `none` everywhere the condition holds of nothing, and every
    statement that has the invariant at this `valid` among its hypotheses holds vacuously.
  * It reads the private input: a value of the thread's `valid`, of the real world: never to be
    quoted as public, nor as what a simulator knows.
  * At the proof file's description `okStart` holds tests on the table's key: its seeds' words, its
    record's words, its item: so this value of `valid` bears a clause on the key, against rule (V)
    of Honest/Thread/Thr.lean; nothing on the key may be drawn from it.
  * Owed, from the committer's construction, at every index, every value of `rc` and every seed: the
    made key passes all of them: a public-looking fact that reads hidden values: expected to hold
    always: until it is a theorem it is a named premise.
  * Where a statement states a distribution over `rc` or the seed with the instance's key written as
    the made key, "`okStart` at that instance" is a condition on `rc`: it stands in front of such a
    law only with the fact of the bullet above proved, or with its failure's measure beside it: the
    last sentences of rule (V).
  * Nothing here puts the condition into a `Thread`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **An input that `ready` could prepare, as far as the index, the instance and the trace go**, at
an instance that passes the description's test: the instance passes `FileDescription.okStart`; the index is
in range; the trace is the prover's own `trace` at the input's own index and instance. It is a
definition: meant as a value of the parameter `valid`. It holds of no input at a request at which
that `trace` is `none`. -/
def ReadyInput (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (v : Local W₀ Rc Xi Tr) : Prop :=
  F.okStart v.x = true ∧ H.inRange v.w₀ = true ∧ H.trace v.w₀ v.x = some v.trace

/-- Where `readyTests` returns, the index is in range. -/
theorem tests_inRange {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    (h : readyTests F B H w₀ = .ok ()) : H.inRange w₀ = true := by
  unfold readyTests at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h5
  simpa using h5

/-- **The input that `ready` prepares meets the condition**, if the instance passes
`FileDescription.okStart`. -/
theorem readyInput_of_ready {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins B} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F B H w₀ rc x c = .ok R) (hx : F.okStart x = true) : ReadyInput F H R.own := by
  obtain ⟨ht, tr, htr, ho, -⟩ := ready_ok hR
  rw [ho]
  show F.okStart x = true ∧ H.inRange w₀ = true ∧ H.trace w₀ x = some tr
  exact ⟨hx, tests_inRange ht, htr⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.tests_inRange
#print axioms ProofFile.Honest.readyInput_of_ready
