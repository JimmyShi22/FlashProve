-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/RngLkp.lean: how the digits of the range check (Cb/Gen/RngAlg.lean) enter the lookup argument
(Cb/Gen/LkpAlg.lean) as keys for a table [0, q): plain mathematics.

Definitions and statements; the proofs are in Cb/Gen/RngLkpProofs.lean.

A table [0, q) is given to the lookup as the map u ↦ u mod q on 2^T indices (`tabMod`); a vector of
K digits is padded with zeros to 2^n keys (`pad`).

Main names:
  `Spec.inTable_tabMod`: the lookup's relation (`InTable`) for this table says that every key is the
    image of a natural number below q (`InTab`). It needs q ≤ 2^T (else the map misses entries of
    the table: the direction "key below q, so in the table" fails) and 0 < q.
  `Spec.inTable_pad`: if also K ≤ 2^n, padding with zeros changes nothing, since 0 is in the table:
    the relation for `pad K v` says that each of the first K entries of v is the image of a natural
    number below q.

Limits: this file says nothing on the sizes that the lookup itself asks (W ≤ 2^w, 2^n < 2^W,
2^T (2^W - 1) < p). The last two are conditions on the number of digits, on q and on the
characteristic, to be met by the parameters.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.RngAlg
import Cb.Gen.LkpAlg

set_option autoImplicit false

namespace Cb.Rng

/-- For 0 < q ≤ 2^T: the table [0, q) on 2^T indices. -/
def tabMod {E : Type} [Field E] (q : ℕ) : ℕ → E := fun u => ((u % q : ℕ) : E)

/-- The first K entries of a vector, then zeros. -/
def pad {E : Type} [Field E] (K : ℕ) (v : ℕ → E) : ℕ → E := fun b => if b < K then v b else 0

end Cb.Rng

namespace Cb.Spec
open Cb.Rng Cb.Lkp

def inTable_tabMod : Prop :=
  ∀ (E : Type) [Field E] (n T q : ℕ) (key : ℕ → E),
    0 < q → q ≤ 2 ^ T → (InTable n T key (tabMod q) ↔ ∀ b < 2 ^ n, InTab q (key b))

def inTable_pad : Prop :=
  ∀ (E : Type) [Field E] (n T q K : ℕ) (v : ℕ → E),
    0 < q → q ≤ 2 ^ T → K ≤ 2 ^ n → (InTable n T (pad K v) (tabMod q) ↔ ∀ b < K, InTab q (v b))

end Cb.Spec
