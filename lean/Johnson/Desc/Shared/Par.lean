-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Shared/Par.lean: the shared chain's parameters, taken from the planner, and the
decision on the shared chain at these parameters.

Definitions only; no theorem is stated. The words are explained in State.lean, and what has been run
and what is not checked is told in Fold.lean.

The fold in Fold.lean takes its parameters Par as an argument, the plan's entries among them. A run
has shown what that leaves open: with the entry for a proximity test's last round changed to count
fewer positions, down to one, and the view cut to fit, the fold says yes. How hard that test tests
was then up to whoever supplied the entries. Here no argument holds an entry. All of Par except the
key is computed from the setting s, the codes, and the sizes x : Params.LinSized. For a proof file
these are z.set, z.codes and z.batch of z : Params.ProofSized.
  The entries are those of the rounds of Params.sharedPlan s codes x
    (OnBytes/Params/DeriveLin.lean), the planner's own routine for the plan of a shared chain. Where
    that routine refuses there are no parameters, and the decision is no.
  The shape is x.shape, the number of answers to a sample is s.samples, and the first tree is 0.

What the caller must supply, and this file does not check:
  The setting s, the codes and the sizes x. They are what the program's planner computes from the
    three public files (the lines of the policy, and the shapes in the layout and in the
    matrix-shape file): Params.sized, which Params.configure calls
    (OnBytes/Params/Configure.lean:129-131). Whoever calls this decision must pass that result and
    nothing else.
  The key of the table. OnBytes.Slice.keyOf (OnBytes/Slice/KeyOfRec.lean) builds a key from a
    record.

Owed. That these entries equal the list which the program reads back out of its parameter
bytes has been evaluated at two stored proofs and is not proved.

No hash is called here.

Main names: entriesOf s codes x; parOfZ s codes x key; runSharedZ s codes x key v, which returns the
state at the chain's end, for the start of another chain; descSharedZ s codes x key v, the decision.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.
What this comment says of the code rests on reading and is not machine-checked.


-/
import Johnson.Desc.Shared.Fold
import OnBytes.Params.DeriveLin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Shared
open OnBytes OnBytes.Params

/-- The entries for the shared chain's rounds as the planner's routine sharedPlan plans them;
nothing where it refuses. -/
def entriesOf (s : Setting) (codes : Codes) (x : LinSized) : Option (List Fmt.Entry) :=
  match sharedPlan s codes x with
  | .ok P => some (P.rounds.map (·.entry))
  | .error _ => none

/-- The fold's parameters, from the setting, the codes, the sizes and the table's key. -/
def parOfZ (s : Setting) (codes : Codes) (x : LinSized) (key : TableKey) : Option Par :=
  (entriesOf s codes x).map fun es =>
    { S := x.shape, key := key, samples := s.samples, firstTree := 0, entries := es }

/-- The shared chain's run at these parameters. It returns the state at the chain's end, which the
start of another chain can use. -/
def runSharedZ (s : Setting) (codes : Codes) (x : LinSized) (key : TableKey) (v : Fmt.View) :
    Option (DState Loc) :=
  (parOfZ s codes x key).bind fun p => runShared callG p codes v

/-- The decision on a shared chain's view. -/
def descSharedZ (s : Setting) (codes : Codes) (x : LinSized) (key : TableKey) (v : Fmt.View) :
    Bool :=
  (runSharedZ s codes x key v).isSome

end Desc.Shared
