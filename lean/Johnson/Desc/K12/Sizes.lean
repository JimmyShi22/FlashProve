-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Sizes.lean: the proximity test (the kind K12): its test on the plan alone: the
sizes of its stages fit together (`sizesOk`). Definitions with code; no theorem. It imports the
format's types of a code and a stage alone.

A stage is two codes (main C, mask Z) and two numbers: 2^k main rows, 2^h mask rows. A code has
words of length 2^a, messages of l entries and a random tail of r entries. From a stage to the next
(primed):
  l = 2^k' l'                                    the folded main message fills the next main rows;
  2^h' l_Z' ≥ 2 l_Z + r + 2 r_Z + answers        the next mask rows take the two folded mask rows'
                                                 messages, the tails of all three folded rows, and
                                                 the pad;
  answers ≤ l_Z'                                 a mask row is at least as long as the pad.
At a stage by itself: both codes are in order; both message lengths are powers of two; the mask code
is not longer than the main code; k ≤ 60; h ≤ k; at the last stage k = 0 (so h = 0); at every other
1 ≤ k and 2 k + 1 - h ≤ l_Z (room for the hiding polynomial's coefficients). Of the list: at least
two stages; at least one answer.

Where it comes from: the verifier program's ioppOk with what it calls (OnBytes/Iop/Prox.lean,
Ground.lean), taken over clause by clause. Two things differ. There a stage names its codes by their
numbers in a list, and a clause asks that they are there; here a stage holds its codes. There a code
in order has three clauses more (l ≤ 2^a, r ≤ 2^a, l + r ≤ 2^a): each follows from
l + r ≤ 2^min(a, 32), so they are left out.
Limits: nothing says what these conditions are good for: that is the kind's law's matter.
Terms: lean/GLOSSARY.md.

-/
import Fmt.M1Types

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12
open Fmt.M1 (Code Stage)

/-- The greatest logarithm of a code's length, and the greatest number of row variables. -/
def mostA : Nat := 60

/-- n is a power of two. -/
def pow2 (n : Nat) : Bool := 2 ^ Nat.log2 n == n

/-- The three numbers describe a code: 1 ≤ a ≤ 60; the message has an entry; message and tail
together are no longer than a word, and no longer than 2^32 (one coset of points). -/
def codeOk (c : Code) : Bool :=
  decide (1 ≤ c.a) && decide (c.a ≤ mostA) && decide (1 ≤ c.l) &&
    decide (c.l + c.r ≤ 2 ^ min c.a 32)

/-- The conditions on a stage by itself. last: it is the last. -/
def stageOk (last : Bool) (s : Stage) : Bool :=
  codeOk s.C && codeOk s.Z && pow2 s.C.l && pow2 s.Z.l && decide (s.Z.a ≤ s.C.a) &&
    decide (s.k ≤ mostA) && decide (s.h ≤ s.k) &&
    (if last then s.k == 0 else decide (1 ≤ s.k) && decide (2 * s.k + 1 - s.h ≤ s.Z.l))

/-- The conditions from a stage p to the next, s. -/
def stepOk (answers : Nat) (p s : Stage) : Bool :=
  s.C.l * 2 ^ s.k == p.C.l &&
    decide (2 * p.Z.l + p.C.r + 2 * p.Z.r + answers ≤ s.Z.l * 2 ^ s.h) && decide (answers ≤ s.Z.l)

/-- The conditions on consecutive stages, given the stage before the first of them, if any. A
stage's own conditions are asked first: so no power is taken of a k above 60. -/
def stagesOk (answers : Nat) : Option Stage → List Stage → Bool
  | _, [] => true
  | before, s :: rest =>
    stageOk rest.isEmpty s &&
      (match before with
        | none => true
        | some p => stepOk answers p s) &&
      stagesOk answers (some s) rest

/-- **The sizes of a proximity test's stages fit together.** -/
def sizesOk (stages : List Stage) (answers : Nat) : Bool :=
  decide (2 ≤ stages.length) && decide (1 ≤ answers) && stagesOk answers none stages

end VerifiableInference.Desc.K12
