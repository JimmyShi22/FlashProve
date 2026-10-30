-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4PlanFit.lean: TWO TESTS ON THE PLAN, WITH CODE, FOR K4's ROW AT THE TABLE OF
JOINTS (Johnson/Desc/First/Borders.lean), and what a yes of each gives. Small; no Mathlib. A file
BESIDE the table: it turns nothing of it.

What is said. `isK4At links pl`: the place pl is piece 3 of a segment that links says is a layers'.
`k4NextFit links ps`: behind every such place of the list ps stands a place at piece 4 of the same
segment. `k4ToldFit links ps told`: at every such place the block tells no tree (told: what each
block of the chain tells, block by block, as in Johnson/Desc/First/BookFit.lean). `k4NextFit_at`,
`k4ToldFit_at`: what a yes gives at one such place: the lines next · link' · piece' of K4's row's
record of lines, and "K4's block tells nothing".

Limits. links, ps and told are letters: that they are the real description's is not said here. The
tests have run nowhere yet. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.FillK4
open VerifiableInference.Desc (Place Oracle)

/-- The place is piece 3 of a layers' segment. -/
def isK4At (links : List ModelPart) (pl : Place) : Bool :=
  match pl.link with
  | some m => links[m]? == some .layers && pl.piece == 3
  | none => false

/-- Behind every place of K4's stands piece 4 of the same segment. -/
def k4NextFit (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all fun k =>
    match ps[k]? with
    | some pl =>
      !isK4At links pl ||
        (match ps[k + 1]? with
          | some pl' => pl'.link == pl.link && pl'.piece == 4
          | none => false)
    | none => true

/-- At every place of K4's the block tells no tree. -/
def k4ToldFit (links : List ModelPart) (ps : List Place) (told : List (List Oracle)) : Bool :=
  (List.range ps.length).all fun k =>
    match ps[k]? with
    | some pl => !isK4At links pl || (told[k]?.any fun os => os.isEmpty)
    | none => true

variable {links : List ModelPart} {ps : List Place} {k m : Nat} {pl : Place}

theorem isK4At_of (link : pl.link = some m) (sub : links[m]? = some .layers)
    (piece : pl.piece = 3) : isK4At links pl = true := by
  unfold isK4At
  rw [link]
  simp [sub, piece]

/-- **What the first test's yes gives at a place of K4's.** -/
theorem k4NextFit_at (h : k4NextFit links ps = true) (here : ps[k]? = some pl)
    (link : pl.link = some m) (sub : links[m]? = some .layers) (piece : pl.piece = 3) :
    ∃ pl', ps[k + 1]? = some pl' ∧ pl'.link = some m ∧ pl'.piece = 4 := by
  have hk : k < ps.length := (List.getElem?_eq_some_iff.mp here).1
  have h' := List.all_eq_true.1 h k (List.mem_range.2 hk)
  rw [here] at h'
  simp only [isK4At_of link sub piece, Bool.not_true, Bool.false_or] at h'
  cases e : ps[k + 1]? with
  | none => simp [e] at h'
  | some pl' =>
    simp only [e, Bool.and_eq_true, beq_iff_eq] at h'
    exact ⟨pl', rfl, h'.1.trans link, h'.2⟩

/-- **What the second test's yes gives at a place of K4's.** -/
theorem k4ToldFit_at {told : List (List Oracle)} (h : k4ToldFit links ps told = true)
    (here : ps[k]? = some pl) (link : pl.link = some m) (sub : links[m]? = some .layers)
    (piece : pl.piece = 3) : told[k]? = some [] := by
  have hk : k < ps.length := (List.getElem?_eq_some_iff.mp here).1
  have h' := List.all_eq_true.1 h k (List.mem_range.2 hk)
  rw [here] at h'
  simp only [isK4At_of link sub piece, Bool.not_true, Bool.false_or] at h'
  cases e : told[k]? with
  | none => simp [e] at h'
  | some os =>
    simp only [e, Option.any_some, List.isEmpty_iff] at h'
    rw [h']

end VerifiableInference.Desc.First.FillK4

#print axioms VerifiableInference.Desc.First.FillK4.k4NextFit_at
#print axioms VerifiableInference.Desc.First.FillK4.k4ToldFit_at
