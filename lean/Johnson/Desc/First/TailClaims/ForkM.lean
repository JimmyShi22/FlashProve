-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/ForkM.lean: the ground of the smallness test's claims and weights as
plain functions: routines on a sub-proof's state alone, which may refuse under a name.

The Lean verifier program writes these routines in `SubM` (OnBytes/Model/Hide.lean), a state over
its context. The routines of this folder close no round. Of the context they use one thing: to fail.
So they are written here over the sub-proof's state (`Fork`) alone. A refusal is a value that keeps
the program's name for it, so that a control can say which guard refused.

Main names:
  `ForkM α`     a routine: Fork → Except String (α × Fork).
  `mustAs`, `testAs`   fail under the name unless the condition holds. The program's `testAs` is
                idle in a dry run; there is no dry run here, so the two are one function.
  `get`         the program's unwrapping without a name: it fails under the name given here, by our
                habit "routine:line" of the program's text.
  `change`, `take`, `ask`   lifts of the program's plain functions on `Fork`, as in `SubM`.
  `kap`, `push`, `lin`, `claims`, `paid`   as in `SubM`.
  `t2Lin`       one claim with runs (OnBytes/Model/Trees.lean).
Limits: definitions alone. The plain functions on `Fork` are the program's own, by name.

-/
import OnBytes.Model.Trees

set_option autoImplicit false

namespace VerifiableInference.Desc.First.TailClaims

open OnBytes OnBytes.Model

/-- A routine on a sub-proof's state that may refuse under a name. -/
abbrev ForkM (α : Type) : Type := StateT Fork (Except String) α

namespace ForkM

/-- Refuses under the name. -/
def refuse {α : Type} (name : String) : ForkM α := fun _ => .error name

/-- Fails under the name unless b is true (the program's `mustAs`, OnBytes/Model/Frame.lean). -/
def mustAs (name : String) (b : Bool) : ForkM Unit := if b then pure () else refuse name

/-- Fails under the name unless b is true (the program's `testAs`; no dry run here). -/
def testAs (name : String) (b : Bool) : ForkM Unit := mustAs name b

/-- Unwraps x, or fails under the name (the program's `SubM.get`, which has no name). -/
def get {α : Type} (name : String) (x : Option α) : ForkM α :=
  match x with
  | some a => pure a
  | none => refuse name

/-- Changes the state by a step that may refuse (`SubM.change`). -/
def change (name : String) (f : Fork → Option Fork) : ForkM Unit := fun F =>
  match f F with
  | some G => .ok ((), G)
  | none => .error name

/-- Changes the state by a step that may refuse and that returns a value (`SubM.take`). -/
def take {α : Type} (name : String) (f : Fork → Option (α × Fork)) : ForkM α := fun F =>
  match f F with
  | some x => .ok x
  | none => .error name

/-- Reads a value off the state by a function that may refuse (`SubM.ask`). -/
def ask {α : Type} (name : String) (f : Fork → Option α) : ForkM α := fun F =>
  match f F with
  | some a => .ok (a, F)
  | none => .error name

/-- `Fork.kap` as a routine. -/
def kap (name : String) : ForkM E := take name (·.kap)

/-- `Fork.push` as a routine. -/
def push (name : String) (w : E) (a : Aff) : ForkM Unit := change name (·.push w a)

/-- `Fork.lin` as a routine. -/
def lin (name : String) (f : Aff) : ForkM Unit := change name (·.lin f)

/-- The number of claims added so far. -/
def claims : ForkM Nat := fun F => .ok (F.nClaim, F)

/-- `Fork.paid` as a routine. -/
def paid (i : Nat) : ForkM Unit := fun F => .ok ((), F.paid i)

/-- Adds one claim: the form a plus the runs is 0 (the program's `t2Lin`,
OnBytes/Model/Trees.lean:323-326). -/
def t2Lin (a : Aff) (runs : Array Run2) : ForkM Unit := do
  let k ← kap "t2Lin:324"
  push "t2Lin:325" k a
  change "t2Lin:326" (·.pushRuns k runs)

end ForkM

end VerifiableInference.Desc.First.TailClaims
