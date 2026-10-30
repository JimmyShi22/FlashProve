-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/FillKeeper.lean: THE TABLE's OWN LAYER OF ITS FILLING: three public items that no
kind claims, each with its test on the record, laid into a `Meaning` over whatever is there. Small;
no Mathlib. A file BESIDE the table of joints: it turns nothing of it.

Why. `Meaning.pub` (Johnson/Desc/First/Borders.lean) is a letter: what each public item says of the
record. It is filled in layers: each kind's files lay their own items and hand every other item on.
Three items are made at a place of one kind and asked by several others: they are laid here.

What is said. `ledgerB`: a ledger is open, and its three arrays have as many entries as it has
slots. `freeAboveB n`: a ledger is open; every slot from its next free number on is free; it has n
slots (n: the plan's number for the segment). `unheardB`: the record holds no reply. `pubKeeper`:
THE LAYER's HALF WITH CODE: `ledger m`, `freeAbove m`, `unheard` are these; every other item is
handed on to a function that it is given: so the layers' halves can be composed and RUN without a
`Meaning`. `fillKeeper`: the layer: `pub` is that half over what was there; every other field as it
was. `fillKeeper_pub` (by the make), `_ledger`, `_freeAbove`, `_unheard`: what it lays, at every
`Meaning`. `fillKeeper_else`: what it leaves.

Limits. (1) nsOf is a letter: the plan's number of slots by segment; where it answers nothing
`freeAbove` is false. (2) Nothing says here who makes or keeps the three. (3) Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- A ledger is open, and its three arrays have as many entries as it has slots. -/
def ledgerB (s : S) : Bool :=
  s.fork?.any fun G => G.vp.size == G.ns && G.mf.size == G.ns && G.gotF.size == G.ns

/-- A ledger is open; every slot from its next free number on is free; it has n slots. -/
def freeAboveB (n : Nat) (s : S) : Bool :=
  s.fork?.any fun G =>
    ((List.range (G.ns - G.next)).all fun j => !G.gotF.getD (G.next + j) true) && G.ns == n

/-- The record holds no reply. -/
def unheardB (s : S) : Bool := s.out.reply.isNone

/-- Is the item one of this layer's? -/
def keeperItem : Pub → Bool
  | .ledger _ => true
  | .freeAbove _ => true
  | .unheard => true
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. nsOf: the plan's number of
slots of a segment's ledger. -/
def pubKeeper {P : Type} (nsOf : Nat → Option Nat) (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .ledger _ => ledgerB a.2
    | .freeAbove m => (nsOf m).any fun n => freeAboveB n a.2
    | .unheard => unheardB a.2
    | q => f q a

/-- **The table's own layer.** -/
def fillKeeper {P W : Type} (nsOf : Nat → Option Nat) (Mg : Meaning P W) : Meaning P W :=
  { Mg with pub := pubKeeper nsOf Mg.pub }

section
variable {P W : Type} (nsOf : Nat → Option Nat) (Mg : Meaning P W)

/-- The layer's `pub` is its half with code, by the make. -/
theorem fillKeeper_pub : (fillKeeper nsOf Mg).pub = pubKeeper nsOf Mg.pub := rfl

theorem fillKeeper_ledger (m : Nat) (a : P × S) :
    (fillKeeper nsOf Mg).pub (.ledger m) a = ledgerB a.2 := rfl

theorem fillKeeper_freeAbove (m : Nat) (a : P × S) :
    (fillKeeper nsOf Mg).pub (.freeAbove m) a = (nsOf m).any fun n => freeAboveB n a.2 := rfl

theorem fillKeeper_unheard (a : P × S) : (fillKeeper nsOf Mg).pub .unheard a = unheardB a.2 := rfl

/-- Every other item is handed on. -/
theorem fillKeeper_else (q : Pub) (h : keeperItem q = false) (a : P × S) :
    (fillKeeper nsOf Mg).pub q a = Mg.pub q a := by
  cases q <;> first | rfl | (simp [keeperItem] at h)

end

end VerifiableInference.Desc.First
