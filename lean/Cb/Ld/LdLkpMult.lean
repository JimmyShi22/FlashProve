-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMult.lean: which vectors of multiplicities make a lookup complete, when the table is a
multiset.
This file is about completeness of a lookup argument whose table may have repeated entries: a
condition on the multiplicities (`Valid`; the other premises: the row of `Spec.ldLkpMult_mid`) under
which the claim after the first challenge holds at every challenge.

Definitions and statements (the statements in `Cb.Spec`); the proofs are in
Cb/Ld/LdLkpMultProofs.lean. Plain mathematics on keys, tables and bits (the parameters of
Cb/Gen/LkpAlg.lean); no protocol.

Why: Cb/Gen/LkpAlg.lean has one honest vector: the multiplicity of the entry u is the number of keys
that equal t u and no earlier entry. Where a table has repeats, other vectors serve as well; and one
use needs them. When several lookups ("functions" f < 2^g, each with its keys and its table) are
joined by a random shift (Cb/Ld/LdLkpShift.lean), the multiplicities are sent before the shift is
drawn, so they are taken function by function.
At a shift at which a shifted entry of a function f and one of a later function f' (f < f') coincide
the joint table has a repeat that no single table had, and the vector sent is not the "no earlier
entry" vector of the joint table (where a key of f' equals that entry of f'). The lookup would not
be complete there if its exact claim (`Lk.inP`, Cb/Ld/LdLkp.lean) asked for that vector.

Main names:
  `Valid n T w W key t M`: all M u j are bits; the bits at the idle positions W ≤ j < 2^w are 0; for
    every value x the multiplicities (`Cb.Lkp.multOf`) of the entries that equal x add up to the
    number of keys that equal x.
  `Spec.ldLkpMult_mid`: every key in the table, W ≤ 2^w, `Valid` ⇒ the claim after the first
    challenge (`Cb.Lkp.Mid`: bits, the number of keys, the identity of the two products) at every
    challenge.
  `Spec.ldLkpMult_idle`: `Valid` ⇒ the table's product at an idle position is 1, at every challenge.
  `Spec.ldLkpMult_honest`: the honest bits of Cb/Gen/LkpAlg.lean are valid (2^n < 2^W, every key in
    the table).
  `Spec.ldLkpMult_shift`: bits M f that are valid for the function f, for every f < 2^g ⇒ laid side
    by side (`shBit`) they are valid for the joint keys and the joint table of the random shift at
    every shift. Nothing is asked of the tags.

Notation:
  `n`: 2^n is the number of keys;
  `T`: 2^T the number of the table's entries;
  `w`: 2^w the number of bit positions;
  `W`: the bit positions j with W ≤ j < 2^w are the idle ones.

Limits: soundness does not read any of this: the relaxed claim of a lookup does not mention
multiplicities (`Lk.inR`, Cb/Ld/LdLkp.lean).
The remark that a multiset table admits more than one vector, and that the shift needs it, is ours.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpShift

set_option autoImplicit false

namespace Cb.LdLkp
open Finset Cb.Lkp

section
variable {E : Type} [Field E]

open Classical in
/-- The bits write a valid vector of multiplicities. -/
def Valid (n T w W : ℕ) (key t : ℕ → E) (M : ℕ → ℕ → E) : Prop :=
  Bits T w M ∧ (∀ u < 2 ^ T, ∀ j, W ≤ j → j < 2 ^ w → M u j = 0) ∧
  ∀ x : E, ∑ u ∈ (range (2 ^ T)).filter (fun u => t u = x), multOf W M u =
    ((range (2 ^ n)).filter fun b => key b = x).card

/-- the bits of several functions side by side, in the numbering of the joint table -/
def shBit (d : ℕ) (M : ℕ → ℕ → ℕ → E) : ℕ → ℕ → E := fun Y j => M (Y / 2 ^ d) (Y % 2 ^ d) j

end
end Cb.LdLkp

namespace Cb.Spec
open Finset Cb.Lkp Cb.LdLkp

/-- Under the hypotheses below, a valid vector makes the claim after the first challenge
(`Cb.Lkp.Mid`) hold at every challenge. -/
def ldLkpMult_mid : Prop :=
  ∀ (E : Type) [Field E] (n T w W : ℕ) (key t : ℕ → E) (M : ℕ → ℕ → E),
    W ≤ 2 ^ w → InTable n T key t → Valid n T w W key t M → ∀ al, Mid n T w W key t M al

def ldLkpMult_idle : Prop :=
  ∀ (E : Type) [Field E] (n T w W : ℕ) (key t : ℕ → E) (M : ℕ → ℕ → E),
    Valid n T w W key t M → ∀ al j, W ≤ j → j < 2 ^ w → tabProd T t M al j = 1

def ldLkpMult_honest : Prop :=
  ∀ (E : Type) [Field E] (n T w W : ℕ) (key t : ℕ → E),
    2 ^ n < 2 ^ W → InTable n T key t → Valid n T w W key t (hbit n W key t)

/-- Valid function by function ⇒ valid for the joint lookup, at every shift. -/
def ldLkpMult_shift : Prop :=
  ∀ (E : Type) [Field E] (g v d w W : ℕ) (key tab : ℕ → ℕ → E) (tag : ℕ → E) (M : ℕ → ℕ → ℕ → E),
    (∀ f < 2 ^ g, Valid v d w W (key f) (tab f) (M f)) →
    ∀ θ, Valid (g + v) (g + d) w W (shKey v key tag θ) (shTab d tab tag θ) (shBit d M)

end Cb.Spec
