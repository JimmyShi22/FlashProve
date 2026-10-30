--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ground/Shape/MoreMarks.lean: THE TWO MARKS BESIDE THE SHAPE (`stTidyB`, `stPlainB`,
Johnson/Desc/Ground/Shape/Marks.lean) ARE KEPT BY THE GROUND's TWO FURTHER FUNCTIONS: the adding of
rows one behind the other (`addRowsP`) and the taking of the next free mask entries (`takeMasksP`).
With Marks.lean's eleven that is all thirteen functions of the ground whose names end in P. No
statement here names a kind, a chain or a frame for an honest side.

Main names. `addRows_tidy`, `addRows_plain` (the new rows are plain), `takeMasks_tidy`,
`takeMasks_plain`.

By what. Induction over the list, and over the count, with Marks.lean's `addRow_tidy`,
`addRow_plain`, `takeMask_tidy`, `takeMask_plain`.

Limits. As in Marks.lean: what the two marks do not pay is said there. Nothing on completeness, on
soundness or on what is hidden.


-/
import Johnson.Desc.Ground.Shape.Marks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground.Sh
open OnBytes OnBytes.Slice Desc.Plain
open VerifiableInference.Desc VerifiableInference.Desc.Ground

variable {L : Type}

theorem addRowsFrom_tidy (g : Nat) : ∀ (rows : List OnBytes.Row) (d d' : DState L),
    addRowsFrom g rows d = some d' → stTidyB d.st = true → stTidyB d'.st = true
  | [], d, d', h, ht => by
    cases h
    exact ht
  | r :: l, d, d', h, ht => by
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.1 h
    exact addRowsFrom_tidy g l e d' h (addRow_tidy d e g r he ht)

theorem addRows_tidy (d d' : DState L) (g : Nat) (rows : List OnBytes.Row)
    (h : addRowsP d g rows = some d') (ht : stTidyB d.st = true) : stTidyB d'.st = true := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_tidy g rows d d' h ht
  · cases h

theorem addRowsFrom_plain (g : Nat) : ∀ (rows : List OnBytes.Row) (d d' : DState L),
    addRowsFrom g rows d = some d' → stPlainB d.st = true →
    (∀ r ∈ rows, rowPlainB r = true) → stPlainB d'.st = true
  | [], d, d', h, hp, _ => by
    cases h
    exact hp
  | r :: l, d, d', h, hp, hr => by
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.1 h
    exact addRowsFrom_plain g l e d' h (addRow_plain d e g r he hp (hr r List.mem_cons_self))
      fun x hx => hr x (List.mem_cons_of_mem _ hx)

theorem addRows_plain (d d' : DState L) (g : Nat) (rows : List OnBytes.Row)
    (h : addRowsP d g rows = some d') (hp : stPlainB d.st = true)
    (hr : ∀ r ∈ rows, rowPlainB r = true) : stPlainB d'.st = true := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_plain g rows d d' h hp hr
  · cases h

theorem takeMasksInto_tidy (o : Nat) : ∀ (n : Nat) (d d' : DState L) (acc : Array Nat)
    (l : List Nat), takeMasksInto o n d acc = some (l, d') → stTidyB d.st = true →
    stTidyB d'.st = true
  | 0, d, d', acc, l, h, ht => by
    cases h
    exact ht
  | n + 1, d, d', acc, l, h, ht => by
    rw [takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e he
      exact takeMasksInto_tidy o n e d' _ l h (takeMask_tidy d e o i he ht)

theorem takeMasks_tidy (d d' : DState L) (o count : Nat) (l : List Nat)
    (h : takeMasksP d o count = some (l, d')) (ht : stTidyB d.st = true) :
    stTidyB d'.st = true :=
  takeMasksInto_tidy o count d d' #[] l h ht

theorem takeMasksInto_plain (o : Nat) : ∀ (n : Nat) (d d' : DState L) (acc : Array Nat)
    (l : List Nat), takeMasksInto o n d acc = some (l, d') → stPlainB d.st = true →
    stPlainB d'.st = true
  | 0, d, d', acc, l, h, hp => by
    cases h
    exact hp
  | n + 1, d, d', acc, l, h, hp => by
    rw [takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e he
      exact takeMasksInto_plain o n e d' _ l h (takeMask_plain d e o i he hp)

theorem takeMasks_plain (d d' : DState L) (o count : Nat) (l : List Nat)
    (h : takeMasksP d o count = some (l, d')) (hp : stPlainB d.st = true) :
    stPlainB d'.st = true :=
  takeMasksInto_plain o count d d' #[] l h hp

end VerifiableInference.Desc.Ground.Sh

#print axioms VerifiableInference.Desc.Ground.Sh.addRowsFrom_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.addRows_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.addRowsFrom_plain
#print axioms VerifiableInference.Desc.Ground.Sh.addRows_plain
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasksInto_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasks_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasksInto_plain
#print axioms VerifiableInference.Desc.Ground.Sh.takeMasks_plain
