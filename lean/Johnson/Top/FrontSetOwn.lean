-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontSetOwn.lean: a value of `FrontSet` (Johnson/Top/FrontSet.lean) whose test is one of
FORM: "a test isE, whose yeses are their own early parts, and a second test okI pass": UNDER ONE
HYPOTHESIS ON THE SPELLING.

THE LETTERS MEET; THIS IS NO TIE. A CONDITIONAL. One definition, one statement; general in the
interface with records, the spelling sp and the record r₀.

  `FrontSet.ownEarly`      okS x := isE x && okI x. `apart` from `hE` (what passes isE is its own
                           early part) and `hsp` (among what passes both tests the spelling fixes
                           the early part).
  `FrontSet.has_ownEarly`  the set has i wherever the early part of i passes both tests.

`hsp`, WITH `hE`, IS THE WHOLE CONTENT OF `apart` HERE: nothing is won by this file alone. What it
is for, when it could be had and when not: the head of Johnson/Flat/FrontSetOwnAt.lean, on `hraw`,
of which `hsp` is made there.

Not claimed. `hE`, `hsp` at any spelling; a test isR with its two laws `one`, `self`. Nothing on any
hash. Nothing on soundness.
-/
import Johnson.Top.FrontSet

set_option autoImplicit false

namespace OnBytes.K.Arm.ProofFront

open Iop

variable {I X : Type} {L : HolographicProtocol I X} {sp : X → ByteArray × ByteArray} {r₀ : L.Rec}

/-- **The set of what passes isE and okI**, where what passes isE is its own early part (hE): under
`hsp`; `one` and `self` on isR are handed on as the record's fields. -/
def FrontSet.ownEarly (isE okI : X → Bool) (hE : ∀ x, isE x = true → L.early x = x)
    (isR : L.Rec → Bool) (one : ∀ r, isR r = true → r = r₀) (self : isR r₀ = true)
    (hsp : ∀ x y, isE x = true → isE y = true → okI x = true → okI y = true → sp x = sp y →
      L.early x = L.early y) : FrontSet L sp r₀ where
  okS := fun x => isE x && okI x
  isR := isR
  apart := fun x y a b e => by
    have a' : (isE x && okI x) = true := a
    have b' : (isE y && okI y) = true := b
    rw [Bool.and_eq_true] at a' b'
    exact (hE x a'.1).symm.trans ((hsp x y a'.1 b'.1 a'.2 b'.2 e).trans (hE y b'.1))
  one := one
  self := self

/-- The set has i wherever the early part of i passes both tests. -/
theorem FrontSet.has_ownEarly (isE okI : X → Bool) (hE : ∀ x, isE x = true → L.early x = x)
    (isR : L.Rec → Bool) (one : ∀ r, isR r = true → r = r₀) (self : isR r₀ = true)
    (hsp : ∀ x y, isE x = true → isE y = true → okI x = true → okI y = true → sp x = sp y →
      L.early x = L.early y) (i : X) (h₁ : isE (L.early i) = true)
    (h₂ : okI (L.early i) = true) :
    (FrontSet.ownEarly (sp := sp) isE okI hE isR one self hsp).Has i := by
  show (isE (L.early i) && okI (L.early i)) = true
  rw [h₁, h₂]
  rfl

end OnBytes.K.Arm.ProofFront

#print axioms OnBytes.K.Arm.ProofFront.FrontSet.has_ownEarly
