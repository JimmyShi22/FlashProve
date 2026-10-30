-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/RuleForm.lean: THE FORM OF A KIND's RULE OF BAD ELEMENTS: five definitions, no
statement. A LIGHT FILE: it imports the view's rounds and the field's elements alone, so that a
kind's files can state its law in this form without the rule of composition.

What is said. A rule is a function bad : List Fmt.RoundView → List E, from a front to a list of elements. A
FRONT: the rounds in front, whole, as the view shows them; of this round the message and the
elements of its draw that stand before the one in question (`cutTo`: positions, matrix entries and
the digest are struck). `NoBadFrom bad h t`, `NoBad bad t`: no element that a round of t draws is in
the rule's list at its front: every element of the round's draw is asked. `NoBadStruck`: the form in
which the rule sees nothing of the round's own draw; `strikeLast`: the rule that makes it a case of
`NoBad` (Johnson/Desc/Sound/RuleErr.lean: `StruckIsCase`).

Limits: definitions alone. Two writings of one field element are two elements for "is in the list".
What a rule is worth in a block's errors: Johnson/Desc/Sound/RuleErr.lean.

Terms: lean/GLOSSARY.md.

-/
import Fmt.View
import OnBytes.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes (E)

/-- A round with its draw cut to the first j elements; positions, matrix entries and the digest
struck. -/
def cutTo (r : Fmt.RoundView) (j : Nat) : Fmt.RoundView := { r with drawn := ⟨r.drawn.elems.take j, [], [], none⟩ }

/-- No element that a round of t draws is bad at its front: h, the rounds of t in front of it,
whole, and the round itself cut in front of the element. -/
def NoBadFrom (bad : List Fmt.RoundView → List E) (h t : List Fmt.RoundView) : Prop :=
  ∀ i r, t[i]? = some r → ∀ j x, r.drawn.elems[j]? = some x →
    E.ofTriple x ∉ bad (h ++ t.take i ++ [cutTo r j])

/-- **No drawn element is bad.** -/
def NoBad (bad : List Fmt.RoundView → List E) (t : List Fmt.RoundView) : Prop := NoBadFrom bad [] t

/-- Other files' form: the rule sees nothing of the round's own draw. -/
def NoBadStruck (bad : List Fmt.RoundView → List E) (t : List Fmt.RoundView) : Prop :=
  ∀ i r, t[i]? = some r → ∀ x, x ∈ r.drawn.elems →
    E.ofTriple x ∉ bad (t.take i ++ [{ r with drawn := ⟨[], [], [], none⟩ }])

/-- A front with its last round's draw struck. -/
def strikeLast (g : List Fmt.RoundView) : List Fmt.RoundView :=
  g.dropLast ++ (g.getLast?.map fun r => cutTo r 0).toList

end VerifiableInference.Desc.Sound
