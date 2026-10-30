-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ref/GlRefCodeSplit.lean: Book-keeping for proximity tests on several oracle messages at once.
Here: what nearness at other positions gives at the word's own positions.





Definitions, statements (`Cb.Gl.Bld.Spec`) and proofs. Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs.




Why: by a reading, in this protocol's technical report (lean/CREDITS.md) one oracle message holds
mask rows only (no main row), is sent once, as native short words of the mask code [2^a', m' + r'],
and is a member of two
groups of different lengths (by a reading of a print of the technical report; not held against the
report's latest edition). In the library such a message has long positions of its own,
Fin (2^a'), and a group reads it at its positions through x ↦ x modulo 2^a'
(`C.atPos (cpDn a' a)`).



Main names:











  `Spec.bld_near_atPos`: if every position of C is read at exactly m > 0 positions of
    `C.atPos pos'`, then two words that differ at no more than m e + (m - 1) positions of
    `C.atPos pos'` differ at no more than e positions of C.

Notation:
  `E` : `Type` (Cb/Gl/GlField.lean): the challenge field.




  `cpDn a b j` : `Fin (2 ^ a)` (Cb/Gl/GlCopy.lean): the short position under a long one.

Limits: no group, no shape is given.
This file says nothing on what encodings hide: no word is sent here.


Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBldShape
import Cb.Ld.LdBatShapeProofs
import Cb.Ld.LdBldCode
import Cb.Gen.JohnsonList
import Cb.Gl.GlCopyProofs
import Cb.Ld.LdBldCodeGrpProofs

set_option autoImplicit false

namespace Cb.Gl.Bld
open Code Prob Blocks

namespace Spec

/-- Nearness at other positions. -/
def bld_near_atPos : Prop :=
  ∀ (P P' : Type) [Fintype P] [Fintype P'] (C : LdCode E P) (pos' : P' → P) (m e : ℕ), 0 < m →
    (∀ y, cnt (fun x => pos' x = y) = m) →
    ∀ f g : C.Word, (C.atPos pos').Near (m * e + (m - 1)) f g → C.Near e f g

end Spec

theorem bld_near_atPos : Spec.bld_near_atPos := by
  intro P P' _ _ C pos' m e hm hpos f g h
  have e1 := CodeRep.cnt_comp_even pos' m hpos fun y => C.T f y ≠ C.T g y
  have h' : cnt (fun x => C.T f (pos' x) ≠ C.T g (pos' x)) ≤ m * e + (m - 1) := h
  rw [e1] at h'
  show cnt (fun y => C.T f y ≠ C.T g y) ≤ e
  by_contra hn
  have h2 := Nat.mul_le_mul_left m (Nat.succ_le_of_lt (not_le.1 hn))
  rw [Nat.mul_succ] at h2
  omega

end Cb.Gl.Bld
