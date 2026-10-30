-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/EPubAt.lean: THE PROMISE's PUBLIC TEST AT A BORDER, BY THE BORDER's NUMBER, AS
ONE TERM WITH CODE. One definition, two theorems. It imports the table of joints alone. No Mathlib.

Why. The promise at a border (`onAt`, Johnson/Desc/First/Borders.lean) has among its tests
`pubHeld`: every public item that is open there, or tied to an item that is open there, holds of the
verifier's state. The walk along the verifier's run that shows the promise's half on the state wants
that test as a function of the border's number and the state.

What is said. `ePubAt pub M links ps k a`: at border k of the list of places ps: every public item
that the rows M hold open there, and every one that is tied to an item open there, is accepted by
pub at a. `ePubAt_pubHeld`: at a filling's own pub and rows it IS the promise's `pubHeld` at the
sets that the promise at border k reads (by rfl). `ePubAt_mem`: where it accepts, each such item is
accepted.

Limits. A definition and its unfoldings. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

variable {P W : Type}

/-- **The promise's public test at border k.** -/
def ePubAt (pub : Pub → P × S → Bool) (M : More) (links : List ModelPart) (ps : List Place) (k : Nat)
    (a : P × S) : Bool :=
  (((pubSets M links ps)[k]?.getD []) ++
    pubOfItems ((openSets links ps (start links))[k]?.getD [])).all fun q => pub q a

/-- At a filling's own letters it is the promise's test. -/
theorem ePubAt_pubHeld (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (k : Nat)
    (a : P × S) :
    ePubAt Mg.pub Mg.more links ps k a =
      pubHeld Mg ((openSets links ps (start links))[k]?.getD [])
        ((pubSets Mg.more links ps)[k]?.getD []) a := rfl

/-- Where it accepts, each item is accepted. -/
theorem ePubAt_mem (pub : Pub → P × S → Bool) (M : More) (links : List ModelPart) (ps : List Place)
    (k : Nat) (a : P × S) (h : ePubAt pub M links ps k a = true) (q : Pub)
    (hq : q ∈ (pubSets M links ps)[k]?.getD [] ∨
      q ∈ pubOfItems ((openSets links ps (start links))[k]?.getD [])) : pub q a = true :=
  List.all_eq_true.1 h q (List.mem_append.2 hq)

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.ePubAt_pubHeld
#print axioms VerifiableInference.Desc.First.ePubAt_mem
