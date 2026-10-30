-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Fmt.Blake2b
import Run.Blake2b.SaltedThm
/-!
# BLAKE2b: the form for compiled code, and a message in two parts

`blake2bF` is `Run.Blake2b.blake2bSalted` (Run/Blake2b/Salted.lean), which reads bytes with
machine-word indices. `blake2bF_eq`: it is equal to `blake2b` for all arguments.
`absorb` gives the state after the whole blocks of a beginning, `finish` the digest from such a
state and the rest of the message. A program that hashes many messages with one beginning calls
`absorb` once. `finish_absorb`: the two together are `blake2b` on the whole message, if the
beginning's length is a multiple of 128 and the rest is not empty. Where one of the two conditions
fails, the equation can fail (Run/Blake2b/Test/Salted.lean has an example of each).
The theorems are equations between functions. That a compiled program computes these functions is no
theorem: a run, like a test (#guard), is an evaluation and leaves no theorem.
Source. `finish` has the two arms of `blake2bSalted` (Run/Blake2b/Salted.lean), with `resumeBytes`
for `stateSalted`: it follows, at one remove, what that file names as its source. `blake2bF` and
`absorb` only call functions of that file.
That file's head says (its lines 14 to 16, copied here):
All five definitions are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the BLAKE2
reference source code package (reference C implementations), Copyright 2012, Samuel Neves, used here
under CC0 1.0 Universal (SPDX: CC0-1.0) as the head of Hash.lean says.
-/
namespace Fmt

open Run.Blake2b (State firstStateSalted absorbBytes resumeBytes)

/-- `blake2b` in the form for compiled code. -/
def blake2bF (dlen : Nat) (salt pers msg : ByteArray) : ByteArray :=
  Run.Blake2b.blake2bSalted salt pers msg dlen

/-- A BLAKE2b state (`Run.Blake2b.State`) after some whole blocks of a message are compressed. -/
abbrev B2.Mid : Type := State

/-- From `firstStateSalted dlen salt pers`, the state after the `pre.size / 128` whole blocks of
`pre` are compressed. Bytes of `pre` after its last whole block are not read; `dlen` is not checked.
If `pre` has a whole block, at least one more byte of the message must follow: see `finish`. -/
def absorb (dlen : Nat) (salt pers pre : ByteArray) : B2.Mid :=
  absorbBytes (firstStateSalted dlen salt pers) pre (pre.size / 128)

/-- The first `dlen` bytes of the digest of the message that came as far as `s` and ends with the
bytes of `rest`; the empty array if `dlen` is 0 or above 64. `dlen` must be the one that `s` began
with, and `s.f0` must be 0. If `s` has blocks compressed into it, `rest` must not be empty: see
`resumeBytes`. -/
def finish (dlen : Nat) (s : B2.Mid) (rest : ByteArray) : ByteArray :=
  if dlen = 0 ∨ dlen > 64 then ByteArray.empty
  else (resumeBytes s rest).h.bytes dlen

namespace Spec

/-- The statement of `Fmt.blake2bF_eq`. -/
def blake2bF_eq : Prop :=
  ∀ (dlen : Nat) (salt pers msg : ByteArray),
    blake2bF dlen salt pers msg = blake2b dlen salt pers msg

/-- The statement of `Fmt.finish_absorb`. -/
def finish_absorb : Prop :=
  ∀ (dlen : Nat) (salt pers pre rest : ByteArray), pre.size % 128 = 0 → 0 < rest.size →
    finish dlen (absorb dlen salt pers pre) rest = blake2b dlen salt pers (pre ++ rest)

end Spec

/-- The form for compiled code is equal to `blake2b`, for all arguments. -/
theorem blake2bF_eq : Spec.blake2bF_eq := by
  intro dlen salt pers msg
  unfold blake2bF blake2b
  exact (Run.Blake2b.blake2bSaltedPlain_eq salt pers msg dlen).symm

/-- A beginning of whole blocks, then a rest that is not empty: the digest of the whole message. -/
theorem finish_absorb : Spec.finish_absorb := by
  intro dlen salt pers pre rest hp hr
  unfold finish absorb blake2b
  rw [Run.Blake2b.blake2bSaltedPlain_eq]
  unfold Run.Blake2b.blake2bSalted
  rw [Run.Blake2b.stateSalted_append salt pers pre rest dlen hp hr]

end Fmt

#print axioms Fmt.blake2bF_eq
#print axioms Fmt.finish_absorb
