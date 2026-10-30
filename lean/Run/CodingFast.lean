-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingFast.lean: the typed oracle functions of Run/CodingFn.lean under a name for runs: the form
that computes each answer's hash once.

One definition, one theorem.

Main names:
  `famFast O D K`: := famP (fun _ => L) O D K of Run/CodingFnThin.lean: the answer first as bytes
    (data), then decoded.

Why the file is so short: a form that is not part of this library has a family of its own, which
keeps a chain answer's blocks in an array and writes a leaf's and a node's digest as "the digest of
bytes computed before". Run/CodingFnThin.lean's head says, from the compiler's own output and from
counts with a trace, why that does not do for a leaf or a node: where a branch of a match has a
function's type the whole branch, the hash with it, is computed again at every bit. So the name
stands for famP.
Measured, once each, on the file of this folder that runs the verifier on a toy's files under Lean's
evaluator (eight guards, all green each time): famOf 141 seconds; that other form 21 and 26 seconds;
famP 6.5 seconds.

Limits: this file does not say how often the oracle is asked in a whole run. It does not say
anything on evaluation in Lean's kernel. The tag is "test" here (the default of the record `PageD`);
in Run/CodingFnThin.lean the tag is a variable. What the head of Run/CodingFnThin.lean says under
"Limits" on the evaluator holds here too.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingFnThin

set_option autoImplicit false

namespace Run
open Compile Compile.Batch Iop Rom

variable {I X : Type} {L : BatchProtocol I X}

/-- The family of typed oracle functions for runs. -/
def famFast (O : ByteArray → ByteArray) (D : PageD L) (K : Nat) : Fam (spec 256 K L) :=
  famP (fun _ => L) O D K

theorem famFast_eq (O : ByteArray → ByteArray) (D : PageD L) (K : Nat) :
    famFast O D K = famOf O D K := famP_eq O D K

end Run
