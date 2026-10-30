-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M2EngineDefs.lean: what the test files Run/M2EngineT1.lean to T4, R1, R2, F1 to F12 share.
Definitions only.

These files run the programs' proof files for the second toy (a chain of three links) through ten
run functions (differing in reader, typed or single oracle, challenges, pruned openings or whole
paths: Run/M2EngineF1.lean, part 1). The programs are the C++ implementation that comes with this
Lean code. A run function maps a file to an outcome; the outcome names the first stage that refuses,
or "accepted".

Sources. Written for these test files; nothing here is taken from a text of the programs.

1. What the file contains.
     `sh`: An outcome as a letter: A accepted; V the verifier (for `onBytes`: the decision); R the
       reader; L outside the limits of the generic construction (Run/PlanQ*.lean), or, for the run
       functions over a single oracle, of the encoding of the queries (`OKQ`, Run/PageQ.lean).
     `onBytes`: A run function without a compiled verifier: the strict reader in its fast form
       (Fmt/Rules8Fast.lean), then the decision on what it has read.
     `voices`: A run function on a list of files: one letter per file.
     `tests`: The conditions under which the theorems on the run functions hold, as one test:
       `ok S`, `OKQ S`, `fourBounds S (kOf S)` on the description, and `smallB`, `smallF` at every
       file of a list. The test on roots, which `core_lax`, `core_one` and `core_tree` ask besides,
       is made in Run/M2EngineRoots.lean.

2. What is checked when the file compiles. Nothing.

3. Theorems. None.

4. What is not claimed. Nothing is proved or run here.

Terms: lean/GLOSSARY.md.
-/
import Run.PageQKeepC
import Run.PageQKeep
import Run.PageQFull
import Run.PlanQSP
import Run.PlanQSFP
import Run.LaxDom
import Run.FullDom
import Run.OneIsTypedTop
import Fmt.Rules8Fast

set_option autoImplicit false

namespace Run.PQ.M2E
open Run.PQ

def sh : Who → Char
  | .accepted => 'A'
  | .verifier => 'V'
  | .reader => 'R'
  | .limits => 'L'

/-- the verifier on bytes as a run function -/
def onBytes (S : _root_.Fmt.Spec) (d : PQ.View → Bool) (b : ByteArray) : Who :=
  match _root_.Fmt.wholeChainF S b with
  | none => .reader
  | some o => if d (_root_.Fmt.viewOf S.firstTree o) then .accepted else .verifier

def voices (S : _root_.Fmt.Spec) (d : PQ.View → Bool) (l : List (String × ByteArray))
    (run : _root_.Fmt.Spec → (PQ.View → Bool) → ByteArray → Who) : String :=
  String.ofList (l.map fun x => sh (run S d x.2))

def tests (S : _root_.Fmt.Spec) (l : List (String × ByteArray)) : Bool :=
  ok S && OKQ S && fourBounds S (kOf S) && l.all fun x => smallB S x.2 && smallF S x.2

end Run.PQ.M2E
