-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseToy1.lean: a small example of this library's own through the generic parsers: a file, a
lenient or strict reader, a typed argument string, and the compiled verifier with BLAKE2b behind its
oracles. (`ParseEx.file`, Run/ParseChain.lean: an example file of this library's own, 512 bytes.)

The example is this library's own, and so is the file. They are not the programs' (the C++
implementation that comes with this Lean code).

Sources. The file was made outside Lean, with the format page's own reference program
(format_rules.py, a Python script that belongs to the page, not the C++ prover); it has not been
held against the page as it ships, and may differ from it.

1. What the file contains. Definitions that can be evaluated.
    `Toy1.T`: The example's typing (`Typing`, Run/ParseChain.lean): salts of 40 bytes; plain parts:
      round 0 nothing, round 1 the nonce, round 2 the element s; the position x of round 1's oracle
      is column x of tree 0; a column of three words is a symbol.
    `Toy1.runLax c file`, `Toy1.runStrict c file`, `Toy1.runFull c file`: Three run functions. Each
      runs the reader with the format's hash, then the verifier: `Run.Toy1.V` or, in `runFull`,
      `Run.Toy1.VF`. Both are `Compile.Batch.verifyOneProtocol` at the example, its term untouched.
      `OComp.det` runs the verifier with the typed oracle functions that a single oracle on the
      format's strings induces (`famOf`, Run/CodingFn.lean). These are written here as `famFast`,
      which is `famOf` by a theorem (`famFast_eq`, Run/CodingFast.lean). `famFast` keeps each hash's
      bytes as a value; the evaluations are several times faster.
    `runLax` and `runStrict` use the wiring with pruned openings (`Run.Toy1.V`: the opened leaves of
    a tree share one set of sibling digests; one pruned walk a tree). `runFull` uses the wiring with
    whole paths (`Run.Toy1.VF`: a whole path for each opened leaf, the form of the wirings in the
    compiler's top theorems), after the parser that fills whole paths with real values
    (Run/ParseFull.lean).

2. What is checked when the file compiles. Nine tests (#guard). The honest file is accepted by all
three run functions. On altered copies, each test names the stage that refused.

3. Theorems. None.

4. What is not claimed.
   In this file the oracles are typed oracle functions, not the one oracle through a coding. The
   same example over a single oracle, through an encoding of the queries with its inverse and both
   laws, is in Run/ToyOne.lean.
   It is this library's own example.
   The typed verifier accepts any first 256 bits of a leaf's salt: that they are the run's value is
   the parser's doing.
   What part 4 of Run/ToyQ.lean's head says is not claimed of `V` is not claimed here either, of `V`
   or of `VF`.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ParseFull
import Run.ToyQ
import Rom.Cache
import Run.CodingFast

set_option autoImplicit false

namespace Run.Toy1
open Iop Rom Compile Compile.Batch

/-- The example's typing. -/
def T : Typing (BatchInteractiveOracleProof.ofProto QT) where
  saltBytes := 40
  plains := fun rs =>
    match rs[0]?, rs[1]? with
    | some a, some b =>
        match b.vals with
        | [.e s] => some ((), ((), a.nonce), s, ())
        | _ => none
    | _, _ => none
  place := fun p =>
    match p with
    | .inr (.inl x) => (0, x.val)
    | _ => (1, 0)
  sym := fun p col =>
    match p, col with
    | .inr (.inl _), [a, b, c] => some (a, b, c)
    | _, _ => none

/-- The description (`Fmt.Spec`) as a reader needs it, at the claim c. -/
def specOf (c : E3) : _root_.Fmt.Spec := ParseEx.spec c

/-- The outcome of a run: the reader refused, the verifier refused, or accepted. -/
inductive Who where
  | reader
  | verifier
  | accepted
  deriving DecidableEq, Repr

/-- The verifier's run on what a reader returns. -/
def runOn (c : E3) (x : Option (List (Dig 256) × OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto QT))) : Who :=
  match x with
  | none => .reader
  | some (cms, π) =>
    if (V cms c π).det (famFast _root_.Fmt.oracle PD 2) then .accepted else .verifier

/-- The same at the wiring without the flag for pruned sets. -/
def runOnF (c : E3) (x : Option (List (Dig 256) × OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto QT))) : Who :=
  match x with
  | none => .reader
  | some (cms, π) =>
    if (VF cms c π).det (famFast _root_.Fmt.oracle PD 2) then .accepted else .verifier

/-- The run, through the lenient reader. -/
def runLax (c : E3) (file : ByteArray) : Who :=
  runOn c (parseLaxW (m := Id) _root_.Fmt.formatHash (specOf c) T file)

/-- The run, through the page's own reader (the strict one). -/
def runStrict (c : E3) (file : ByteArray) : Who :=
  runOn c (parseW (m := Id) _root_.Fmt.formatHash (specOf c) T file)

/-- The run at the wiring without the flag, through the parser that fills whole paths. -/
def runFull (c : E3) (file : ByteArray) : Who :=
  runOnF c (parseFullW (m := Id) _root_.Fmt.formatHash (specOf c) T file)

end Run.Toy1

open Run Run.Toy1 Run.ParseEx in
#guard runLax (1, 2, 3) file == .accepted
open Run Run.Toy1 Run.ParseEx in
#guard runFull (1, 2, 3) file == .accepted
-- whole paths serve the wiring with the flag too; paths filled from the pruned set alone do not
-- serve the wiring without it where two opened leaves' ways meet (the second half is not tested
-- here)
open Run Run.Toy1 Run.ParseEx in
#guard runOn (1, 2, 3) (parseFullW (m := Id) _root_.Fmt.formatHash (specOf (1, 2, 3)) T file) == .accepted
open Run Run.Toy1 Run.ParseEx in
#guard runStrict (1, 2, 3) file == .accepted
-- a byte of a column: the verifier refuses behind the lenient reader and behind the one that fills
-- paths; the strict reader refuses itself (all 21 files: Run/ParseToy1All.lean)
open Run Run.Toy1 Run.ParseEx in
#guard runLax (1, 2, 3) (flip file 72) == .verifier && runStrict (1, 2, 3) (flip file 72) == .reader
open Run Run.Toy1 Run.ParseEx in
#guard runFull (1, 2, 3) (flip file 72) == .verifier
-- the last message: only the protocol's decision can refuse, so the verifier refuses, after either
-- reader
open Run Run.Toy1 Run.ParseEx in
#guard runLax (1, 2, 3) (flip file 488) == .verifier && runStrict (1, 2, 3) (flip file 488) == .verifier
-- the file's end; a word that is no element: the reader refuses (run through the lenient reader
-- alone)
open Run Run.Toy1 Run.ParseEx in
#guard runLax (1, 2, 3) (file.extract 0 511) == .reader && runLax (1, 2, 3) (file ++ _root_.Fmt.zeroBytes 1) == .reader
open Run Run.Toy1 Run.ParseEx in
#guard runLax (1, 2, 3) (setWord file 72 18446744069414584321) == .reader
