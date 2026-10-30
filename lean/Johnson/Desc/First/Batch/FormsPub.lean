-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/FormsPub.lean: THE BOOL HALF OF THE FILLING OF THE TABLE OF JOINTS' FOUR
LETTERS forms, formsT, totalB, total (Johnson/Desc/Sound/BordersForms.lean): what the three public
items that are tied to them say of the record, AS A FUNCTION WITH CODE. A definition and three
lemmas. No Mathlib.

Why. The field `pub` of a meaning of the items (`Meaning`, Johnson/Desc/First/Borders.lean) is a
Bool
on the record, and is to be evaluated on a walk. The filling itself has code too; but it stands over
Mathlib, and to call it a sheet must hand in every letter of its sentences. This half reads none of
these: a sheet can call it alone.
  `pubForms Rd runs ah N base`: at formsIn m k r: the public test `formsIn` of EACH RUN that
    `runs m k r` gives, at the segment's readers `Rd m` and its whole group's seats; AT A RUN OF
    WHICH
    ah SAYS YES: `formsInA` (Johnson/Desc/First/Batch/Ahead.lean): its forms may name an array of
    the segment's own that is
    not yet sent, by the plan's seat; at formsInT m k r: `formsInT`, at its first sending's seats;
    at
    totalIn m: `totalIn`; AT EVERY OTHER PUBLIC ITEM: base: what was there before.
  `pubForms_formsIn`, `pubForms_formsInT`, `pubForms_totalIn`: what it gives at its three, by
  unfolding.
Limits: definitions. Where `runs m k r` is empty the Bool is true, as the item is idle. Nothing on
soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.Ahead
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open VerifiableInference.Desc.First (S Pub Numbers)

/-- **The Bool half of the filling.** base: the public items' Bools as they were. -/
def pubForms {P : Type} (Rd : Nat → Readers) (runs : Nat → Nat → String → List (Nat × String))
    (ah : Nat → String → Bool) (N : Numbers) (base : Pub → P × S → Bool) (q : Pub) (a : P × S) :
    Bool :=
  match q with
  | .formsIn m k r => (runs m k r).all fun p =>
      if ah p.1 p.2 then formsInA (Rd m) (N.sent m) (N.group m) p.1 p.2 a.2
      else formsIn (Rd m) (N.group m) p.1 p.2 a.2
  | .formsInT m k r => (runs m k r).all fun p => formsInT (Rd m) (N.sent m 0) p.1 p.2 a.2
  | .totalIn m => totalIn (N.group m) a.2
  | q => base q a

section
variable {P : Type} (Rd : Nat → Readers) (runs : Nat → Nat → String → List (Nat × String))
  (ah : Nat → String → Bool) (N : Numbers) (base : Pub → P × S → Bool)

theorem pubForms_formsIn (m k : Nat) (r : String) (a : P × S) :
    pubForms Rd runs ah N base (.formsIn m k r) a =
      (runs m k r).all fun p =>
        if ah p.1 p.2 then formsInA (Rd m) (N.sent m) (N.group m) p.1 p.2 a.2
        else formsIn (Rd m) (N.group m) p.1 p.2 a.2 := rfl

theorem pubForms_formsInT (m k : Nat) (r : String) (a : P × S) :
    pubForms Rd runs ah N base (.formsInT m k r) a =
      (runs m k r).all fun p => formsInT (Rd m) (N.sent m 0) p.1 p.2 a.2 := rfl

theorem pubForms_totalIn (m : Nat) (a : P × S) :
    pubForms Rd runs ah N base (.totalIn m) a = totalIn (N.group m) a.2 := rfl

end

end VerifiableInference.Desc.K9
