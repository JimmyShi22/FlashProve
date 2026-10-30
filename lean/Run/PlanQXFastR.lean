-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQXFastR.lean: the run function for an entry file with both fast forms, with a proof that the
verdict is the same. (The fast forms: why: the heads of Fmt/Rules8XFast.lean (thousands of hash
calls) and Run/PlanQXFast.lean (a hash for every bit).)

1. What the file contains.
   `runEntryF D dec r0 file`: Run/PlanQXRun.lean's `runEntry` with the proof's reader using the fast
     form of the hash (Fmt/Rules8XFast.lean: `wholeChainXF`) and the verifier using the oracle
     functions made for evaluation (Run/PlanQXFast.lean: `VXK`).

2. What is checked when the file compiles. Only the types and the proof.

3. Theorems.
   `runEntryF_eq`: runEntryF D dec r0 file = runEntry D dec r0 file, for every description,
     decision, root and file.

4. What is not claimed. It is not claimed how often the evaluator computes what. Everything that
   Run/PlanQXRun.lean does not claim.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQXFast
import Fmt.Rules8XFast

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- The run function with both fast forms: from an entry file to an outcome. -/
def runEntryF (D : XD) (dec : View → Bool) (r0 file : ByteArray) : Who :=
  if D.ok then
    match readHead file with
    | none => .reader
    | some (r1, rest) =>
      match (_root_.Fmt.wholeChainXF (D.atR r0 r1) rest).bind
          (toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec) with
      | none => .reader
      | some π => if VXK D dec r0 r1 π then .accepted else .verifier
  else .limits

def Spec.runEntryF_eq : Prop :=
  ∀ (D : XD) (dec : View → Bool) (r0 file : ByteArray),
    runEntryF D dec r0 file = runEntry D dec r0 file

theorem runEntryF_eq : Spec.runEntryF_eq := fun D dec r0 file => by
  rw [← runEntryK_eq]
  unfold runEntryF runEntryK
  have e : ∀ (S : _root_.Fmt.SpecX) (b : ByteArray),
      _root_.Fmt.wholeChainXF S b = _root_.Fmt.wholeChainX (m := Id) _root_.Fmt.formatHash S b :=
    _root_.Fmt.X8.wholeXF_eq
  simp only [e]
  rfl

end Run.PQ
