-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/HostSum.lean: the entries at a link's end as one sum, at which the laws that the last
block asks of the entries of all messages hold by definition.

A link has three tuples of messages: the early ones, the reads' message, the digits' message. Each
is read as entries: Ja, Jb, Jc. Together they are the committed entries. Beside them stand two kinds
of entries that are no committed entries: the cells behind the committed symbols, and the entries of
the typed smallness test under its own names (Cb/Pv/Tail/Claims.lean).

Main names:
  `JAll`, `entsOf`: the committed entries and their values at a tuple of all messages.
  `JEnd`, `msgEnd`: all entries at the link's end and their values.
  `i12E`: where the caller's entries stand: an early entry and a read at its own place among the
    committed ones, a cell among the cells. `isE`, `iJE`: the two other maps. `icE`: an entry of the
    digits' message at its own place.
  `h12E`, `hsE`, `hJE`, `hcE`: the value at the image of each map.

Limits: the same committed entry may stand under two names: as itself and under the test's name.
Nothing here says that these values agree.


Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.HostVal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail

variable {K : Type} [Field K] {s : Size} {Ja Jb Jc M₁ U₁ U₂ MM : Type}

/-- The committed entries of the three tuples of messages. -/
abbrev JAll (Ja Jb Jc : Type) : Type := Ja ⊕ (Jb ⊕ Jc)

/-- All entries at a link's end: the committed ones; the cells; the smallness test's entries under
its own names. -/
abbrev JEnd (s : Size) (Ja Jb Jc : Type) : Type := JAll Ja Jb Jc ⊕ (JCell s ⊕ J s)

section
variable (ra : M₁ → Ja → K) (rb : U₁ → Jb → K) (rc : U₂ → Jc → K) (p₁ : MM → M₁) (p₂ : MM → U₁)
  (p₃ : MM → U₂)

/-- The values of the committed entries. -/
def entsOf (m : MM) : JAll Ja Jb Jc → K :=
  Sum.elim (ra (p₁ m)) (Sum.elim (rb (p₂ m)) (rc (p₃ m)))

variable (sym : M₁ → Syms K s) (vl : MM → J s → K)

/-- The values of all entries at the link's end. -/
noncomputable def msgEnd (m : MM) : JEnd s Ja Jb Jc → K :=
  Sum.elim (entsOf ra rb rc p₁ p₂ p₃ m) (Sum.elim (cellValS (sym (p₁ m))) (vl m))

end

/-- Where the caller's entries stand. -/
def i12E : (Ja ⊕ JCell s) ⊕ Jb → JEnd s Ja Jb Jc
  | .inl (.inl a) => .inl (.inl a)
  | .inl (.inr c) => .inr (.inl c)
  | .inr b => .inl (.inr (.inl b))

/-- Where the smallness test's entries stand under its own names. -/
def isE (j : J s) : JEnd s Ja Jb Jc := .inr (.inr j)

/-- Where an entry of the digits' message stands. -/
def icE (j : Jc) : JEnd s Ja Jb Jc := .inl (.inr (.inr j))

/-- Where the committed entries stand. -/
def iJE (j : JAll Ja Jb Jc) : JEnd s Ja Jb Jc := .inl j

variable (ra : M₁ → Ja → K) (rb : U₁ → Jb → K) (rc : U₂ → Jc → K) (p₁ : MM → M₁) (p₂ : MM → U₁)
  (p₃ : MM → U₂) (sym : M₁ → Syms K s) (vl : MM → J s → K)

theorem h12E (m : MM) (j : (Ja ⊕ JCell s) ⊕ Jb) :
    msgEnd ra rb rc p₁ p₂ p₃ sym vl m (i12E j) =
      Sum.elim (msgV ra sym (p₁ m)) (rb (p₂ m)) j := by
  rcases j with (a | c) | b <;> rfl

theorem hsE (m : MM) (j : J s) : msgEnd ra rb rc p₁ p₂ p₃ sym vl m (isE j) = vl m j := rfl

theorem hcE (m : MM) (j : Jc) : msgEnd ra rb rc p₁ p₂ p₃ sym vl m (icE j) = rc (p₃ m) j := rfl

theorem hJE (m : MM) (j : JAll Ja Jb Jc) :
    msgEnd ra rb rc p₁ p₂ p₃ sym vl m (iJE j) = entsOf ra rb rc p₁ p₂ p₃ m j := rfl

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.h12E
#print axioms Cb.Pv.Tail.hJE
