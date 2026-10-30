-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSBare.lean: tests of the limits of the generic construction (`Run.PQ.ok`,
Run/PlanQTypes.lean) on made-up chains that send a tree and never open it.

A chain is a proof's sequence of rounds, told by a description (`Fmt.Spec`, Fmt/Rules8.lean). The
generic construction makes, from a description within the limits and a decision, a protocol in the
form that the compiled verifier takes.

1. What the file contains.
   `one`: A chain of two rounds: a root, after which one element is drawn; an element. The tree is
     opened nowhere.
   `three`: A chain that sends three trees and opens the second alone.
   `file`: A file of the chain `one`: 32 bytes at the place of the chain's random bytes (each 7), 32
     bytes at the place of the root (each 9), one element of the extension field.

2. What is checked when the file compiles. Six tests (#guard). Both descriptions are in order
   (`Fmt.Spec.ok`) and lie within the limits. A tree that is opened nowhere is typed as `bareShape`
   (Run/PlanQTypes.lean: depth 0, one word a column), an opened tree as it is opened. The compiled
   verifier, behind the strict reader and behind the lenient reader, accepts the file (`runStrictS`,
   `runLaxS`, Run/PlanQS.lean, at the chain `one`, with the decision "always yes"). A file that is
   one byte short is refused by the readers. A tree that is opened twice stays outside the limits
   (tested at one chain, `Fmt.Toy8K2.specT`).

3. Theorems. None.

4. What is not claimed. Nothing on soundness. The root in the file is the root of no tree: nothing
   under it is read, so no reader and no verifier looks at it beyond its length; it enters the
   chain's queries like any message. (What the protocol knows of a tree that is never opened: part 4
   of the head of Run/PlanQTypes.lean.) (Limits of the two run functions: part 4 of the head of
   Run/PlanQS.lean.)

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQSToy
import Fmt.Rules8Known2

set_option autoImplicit false

namespace Run.PQ.Bare
open _root_.Fmt (Entry Round Shape Spec)

/-- the plan's entry of a round that sends a root, after which one element is drawn -/
def eRoot : Entry := { name := "toy: a root", msg := 32, roots := 1, drawE := 1 }

/-- a round that sends a root and opens nothing -/
def rRoot : Round := { entry := eRoot, kind := .elems, items := [.root] }

/-- the last round: an element, and nothing drawn -/
def rLast : Round := { entry := _root_.Fmt.Toy8K2.e3, kind := .nothing, items := [.e] }

/-- the shape under which the chain "three" opens its second tree -/
def shMid : Shape := { a := 4, W := 3, tree := 1 }

/-- one tree, opened nowhere -/
def one : Spec := _root_.Fmt.Toy8K2.mk 0 [rRoot, rLast]

/-- three trees, of which the second alone is opened -/
def three : Spec :=
  _root_.Fmt.Toy8K2.mk 0
    [rRoot,
      { entry := _root_.Fmt.Toy8K2.e1 32 1, kind := .positions,
        items := [.root], opens := [(shMid, .own 1)] },
      rRoot, rLast]

/-- a file of the chain "one" -/
def file : ByteArray :=
  ByteArray.mk (Array.replicate 32 7) ++
    ByteArray.mk (Array.replicate 32 9) ++ _root_.Fmt.ext (1, 2, 3)

end Run.PQ.Bare

open Run.PQ Run.PQ.Bare in
#guard one.ok && three.ok && ok one && ok three
open Run.PQ Run.PQ.Bare in
#guard (rds one).map (·.tree) == [some (bareShape one.firstTree 0), none]
open Run.PQ Run.PQ.Bare in
#guard (rds three).map (·.tree) == [some (bareShape three.firstTree 0), some shMid, some (bareShape three.firstTree 2), none]
open Run Run.PQ Run.PQ.Bare in
#guard runStrictS one TS.yes file == .accepted && runLaxS one TS.yes file == .accepted
open Run Run.PQ Run.PQ.Bare in
#guard runStrictS one TS.yes (file.extract 0 (file.size - 1)) == .reader && runLaxS one TS.yes (file.extract 0 (file.size - 1)) == .reader
-- a tree that is opened twice
open Run.PQ in
#guard !ok _root_.Fmt.Toy8K2.specT
