-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQToy1.lean: a test of the generic construction: at a small description defined in this
library (`ParseEx.spec`, Run/ParseChain.lean) it gives the outcomes of an example that is written
out directly.

The generic construction is that of Run/PlanQTypes.lean, Run/PlanQWire.lean, Run/PlanQPage.lean and
Run/PlanQRun.lean: from a description and a decision to a protocol, its wiring and run functions.
Run/ToyQ.lean writes one example out directly (rounds, wiring, spelling of queries);
Run/ParseToy1.lean runs it on a file and on altered copies. Here nothing typed is written: only the
description (Run/ParseChain.lean: `ParseEx.spec`) and a decision on the untyped view.

1. What the file contains. Definitions that can be evaluated.
   `dec c v`: The last round's one item s is c + the sum of the opened columns (three words each, as
     an element of the extension field).
   The claim c is a parameter: its bytes stand in the description's statement, and `dec c` is the
     decision at c; the typed protocol has no statement. The term that is evaluated is
     `Compile.Batch.vTS` at the interface whose Test is this protocol (Run/PlanQRun.lean).

2. What is checked when the file compiles. Seven tests (#guard). The first five are at the claim (1,
2, 3). The limits hold at this description. The honest file is accepted with each of the two readers
(strict and lenient). On the honest file and on four altered copies (`flip file i`; two of them are
among the altered copies of Run/ParseToy1.lean's tests), the outcome (reader, verifier, accepted) of
the generic construction is that of the example written out directly, with each of the two readers.
With the lenient reader two of these copies end in the outcome "verifier". The last two: at the
claim (1, 2, 4), and with the statement's bytes alone moved to it, the run with the strict reader
does not accept the file.

3. Theorems. None.

4. What is not claimed. The example and its file are this library's own, not the programs'. The
example's decision can be met for every claim (the last message is sent after the positions are
drawn): it tests the construction, not a proof system. It has one round with a tree, and only
positions are drawn.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQRun
import Run.ParseToy1

set_option autoImplicit false

namespace Run.PQ.T1
open Run.PQ

abbrev E3 : Type := UInt64 × UInt64 × UInt64

def colE : List UInt64 → E3
  | [a, b, c] => (a, b, c)
  | _ => (0, 0, 0)

/-- The decision, on the view. -/
def dec (c : E3) (v : View) : Bool :=
  match (v.rounds[1]?).map _root_.Fmt.RoundView.vals with
  | some [_root_.Fmt.ItemValue.e s] => s == v.opened.foldl (fun a x => Run.Toy1.addE a (colE x.2.2)) c
  | _ => false

def same (a : Who) (b : Run.Toy1.Who) : Bool :=
  match a, b with
  | .reader, .reader => true
  | .verifier, .verifier => true
  | .accepted, .accepted => true
  | _, _ => false

def S (c : E3) : _root_.Fmt.Spec := Run.ParseEx.spec c

/-- Tests whether the generic construction and the example written out directly have the same
outcome on one file, with each of the two readers. -/
def agree (c : E3) (file : ByteArray) : Bool :=
  same (runStrict (S c) (dec c) file) (Run.Toy1.runStrict c file) &&
    same (runLax (S c) (dec c) file) (Run.Toy1.runLax c file)

end Run.PQ.T1

open Run Run.PQ Run.PQ.T1 Run.ParseEx in
#guard ok (S (1, 2, 3))
open Run Run.PQ Run.PQ.T1 Run.ParseEx in
#guard runStrict (S (1, 2, 3)) (dec (1, 2, 3)) file == .accepted && runLax (S (1, 2, 3)) (dec (1, 2, 3)) file == .accepted
open Run Run.PQ Run.PQ.T1 Run.ParseEx in
#guard agree (1, 2, 3) file
open Run Run.PQ Run.PQ.T1 Run.ParseEx in
#guard [72, 96, 264, 488].all fun i => agree (1, 2, 3) (flip file i)
open Run Run.PQ Run.PQ.T1 Run.ParseEx in
#guard runLax (S (1, 2, 3)) (dec (1, 2, 3)) (flip file 72) == .verifier && runLax (S (1, 2, 3)) (dec (1, 2, 3)) (flip file 488) == .verifier
open Run Run.PQ Run.PQ.T1 Run.ParseEx in
#guard runStrict (S (1, 2, 4)) (dec (1, 2, 4)) file != .accepted
-- the statement's bytes alone moved, the decision at the old claim: the chain's first value moves: not accepted
open Run Run.PQ Run.PQ.T1 Run.ParseEx in
#guard runStrict (S (1, 2, 4)) (dec (1, 2, 3)) file != .accepted
