-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameItemsBack.lean: THE BRIDGE from "each field of the meaning goes back over a
relation between two statements" (FieldsBack, Johnson/Desc/Sound/ItemsRide.lean) to what the frame's
ties take of the items that are open behind a block (LettersRide's field "items", FrameTied.lean):
so that debt is one sentence a FIELD, not one an item.

  StepRel rel base In   the relation between two statements that a tie hands to its payer: one
                    public part; rel of the two states (the ties hand in: the step's own yes); the
                    strings stay below base; In (the table's promise) at the statement in front
  items_of_fields   from FieldsBack at StepRel, and three facts on every item that is open behind:
                    it has no part of a segment of its own; it is no part of a segment's relation
                    that "own" names; the trees that its pins name have "low"

Limits. FieldsBack is owed by whoever fills the fields. The three facts are of the table and of the
plan's numbers. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameTied
import Johnson.Desc.Sound.ItemsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound (FieldsBack holds_back notOwn lowItem)
open VerifiableInference.Desc.First (S Item Part Meaning Numbers)

section
variable {P W : Type}

/-- The relation between two statements that a tie hands to its payer. -/
def StepRel (rel : S → S → Prop) (base : Nat) (In : P × S → Strs → Prop) :
    P × S → Strs → P × S → Strs → Prop :=
  fun a y b y' => b.1 = a.1 ∧ rel a.2 b.2 ∧ Stays base y y' ∧ In a y

/-- **From the fields to LettersRide's field "items".** -/
theorem items_of_fields {N : Numbers} {Mg : Meaning P W} {rel : S → S → Prop} {base : Nat}
    {In : P × S → Strs → Prop} {Op : Item → Prop} (own : Nat → Part → Bool) (low : Nat → Prop)
    (H : FieldsBack Mg own low (StepRel rel base In))
    (hO : ∀ i, Op i → i.part = none ∧ notOwn own i ∧ lowItem N low i) :
    ∀ p s t y y' w i, rel s t → Stays base y y' → In (p, s) y → Op i →
      i.holds N Mg (p, t) y' w → i.holds N Mg (p, s) y w := by
  intro p s t y y' w i hr hy hI hop h
  obtain ⟨h1, h2, h3⟩ := hO i hop
  exact holds_back N Mg own low _ H i h1 h2 h3 (p, s) y (p, t) y' w ⟨rfl, hr, hy, hI⟩ h

end

#print axioms items_of_fields

end Johnson.Desc.First.Walk.Tied
