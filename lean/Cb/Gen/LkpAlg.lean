-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/LkpAlg.lean: the lookup argument for one table by a multiset identity, with the
multiplicities written in bits: its plain mathematics, without any protocol.

Definitions and statements (the proofs: Cb/Gen/LkpAlgProofs.lean).
The multiset identity is ∏_b (al - key b) = ∏_u (al - t u)^(m u), with m u the multiplicity that the
bits write for entry u (`multOf`).

The objects: 2^n keys, written key b; a table of 2^T entries, written t u (repeats allowed);
bits M u j, u < 2^T, j < 2^w, of which the first W ≤ 2^w positions write the multiplicity of u in
binary; a challenge al.
The relations, in the order in which each is reduced to the next (an arrow reads "is reduced to",
not "implies"): `InTable` (every key is an entry of the table) → `Mid` at al (all M are bits; the
multiplicities sum to the number of keys, in E; the two products agree at al) → the two grand
products with sent targets, the bits, the number of keys, `Rows`.

Main names:
  `keyProd`: the product of al - key b over the keys.
  `tabProd`, for the bit position j: the product over the table of 1 + M u j (al - 1 - t u), which
    is al - t u where the bit is 1, and 1 where it is 0.
  `Rows`: squaring and multiplying from the highest position down.
  `Spec.cnt_badAl_le`: if a key is outside the table, `Mid` holds for at most 2^n - 1 values of al
    (conditions: E finite, W ≤ 2^w, 2^n < 2^W and 2^T (2^W - 1) < p, the characteristic: then the
    sum of the multiplicities is an equation of integers).
  `Spec.planes`: with bits and W ≤ 2^w, the product over j < W of (`tabProd` at j) ^ 2^j is the
    product of (al - t u) ^ multiplicity (`multOf`): `Mid` is stated with the left side.
  `Spec.mid_of_rows`: error 0: for 1 ≤ W: `Bits`, `NumKeys`, true products and `Rows` give `Mid`.
  `Spec.relK_iff`, `Spec.relT_iff`, `Spec.key_end`, `Spec.tab_end`: the two grand products in the
    form of Cb/Gen/GpAlg.lean (one product of 2^n factors; 2^w products of 2^T factors, index
    (u|j)), and what their end claims say of the keys and of the bits.
  `Spec.honest_bits`, `Spec.honest_numKeys`, `Spec.honest_ident`, `Spec.honest_rows`: if `InTable`,
    2^n < 2^W and 1 ≤ W, the honest bits (`hbit`: binary digits of the number of keys that equal t u
    and no earlier entry) satisfy `Bits`, `NumKeys` and the identity of `Mid` at every al; `hU`,
    `hV` satisfy `Rows`.

Limits:
Positions j with W ≤ j < 2^w: the bits there are only asked to be bits. Their products enter nothing
of `Mid` or, for 1 ≤ W, of `Rows`. Of this file's statements only `Spec.relT_iff` and `Spec.tab_end`
reach them.
This file says nothing on the grand products, zerochecks and sumchecks themselves; nothing on
oracles, masks, codes.

The identity and its counts are Alg/Lookup.lean's (there with public padding, here without). The
protocol is the field's multiset check with multiplicities in bits and square-and-multiply, in the
form of the protocol of this protocol's technical report, which follows the texts named in
lean/CREDITS.md.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.GpAlg
import Alg.Lookup
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Lkp
open Finset

variable {E : Type} [Field E]

def InTable (n T : ℕ) (key t : ℕ → E) : Prop := ∀ b < 2 ^ n, ∃ u < 2 ^ T, key b = t u

def Bits (T w : ℕ) (M : ℕ → ℕ → E) : Prop := ∀ u < 2 ^ T, ∀ j < 2 ^ w, M u j * (M u j - 1) = 0

def NumKeys (n T W : ℕ) (M : ℕ → ℕ → E) : Prop :=
  ∑ u ∈ range (2 ^ T), ∑ j ∈ range W, (2 : E) ^ j * M u j = ((2 ^ n : ℕ) : E)

def keyProd (n : ℕ) (key : ℕ → E) (al : E) : E := ∏ b ∈ range (2 ^ n), (al - key b)

def tabProd (T : ℕ) (t : ℕ → E) (M : ℕ → ℕ → E) (al : E) (j : ℕ) : E :=
  ∏ u ∈ range (2 ^ T), (1 + M u j * (al - 1 - t u))

/-- The relation after the challenge. -/
def Mid (n T w W : ℕ) (key t : ℕ → E) (M : ℕ → ℕ → E) (al : E) : Prop :=
  Bits T w M ∧ NumKeys n T W M ∧ keyProd n key al = ∏ j ∈ range W, tabProd T t M al j ^ 2 ^ j

/-- The rows on the sent products. -/
structure Rows (W : ℕ) (PK : E) (PT U V : ℕ → E) : Prop where
  top : U (W - 1) = PT (W - 1)
  sq  : ∀ j < W - 1, V j = U (j + 1) ^ 2
  mul : ∀ j < W - 1, U j = V j * PT j
  eq  : PK = U 0

open Classical in
/-- The number that the first W positions of the bits of u write (a position counts if its entry is
1). -/
def multOf (W : ℕ) (M : ℕ → ℕ → E) (u : ℕ) : ℕ :=
  Alg.Lookup.mult W (fun u j => decide (M u j = 1)) u

/-- The factors of the keys' grand product, and of the table's, with the index (u|j) = u 2^w + j. -/
def facK (key : ℕ → E) (al : E) : ℕ → E := fun b => al - key b
def facT (w : ℕ) (t : ℕ → E) (M : ℕ → ℕ → E) (al : E) : ℕ → E := fun X =>
  1 + M (X / 2 ^ w) (X % 2 ^ w) * (al - 1 - t (X / 2 ^ w))

open Classical in
/-- The honest multiplicity of u: the number of keys that equal t u and no earlier entry of the
table. -/
def hmult (n : ℕ) (key t : ℕ → E) (u : ℕ) : ℕ :=
  (univ.filter fun b : Fin (2 ^ n) => key b = t u ∧ ∀ u' < u, key b ≠ t u').card

/-- The honest bits. -/
def hbit (n W : ℕ) (key t : ℕ → E) (u j : ℕ) : E :=
  if j < W ∧ (hmult n key t u).testBit j = true then 1 else 0

/-- The honest powers and squares. -/
def hU (W : ℕ) (PT : ℕ → E) (j : ℕ) : E := Alg.Lookup.chainFrom PT (W - 1 - j) j
def hV (W : ℕ) (PT : ℕ → E) (j : ℕ) : E := hU W PT (j + 1) ^ 2

end Cb.Lkp

namespace Cb.Spec
open Finset Prob Cb.Lkp

/-- The bad values of the challenge. -/
def cnt_badAl_le : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (n T w W : ℕ)
      (key t : ℕ → E) (M : ℕ → ℕ → E),
    W ≤ 2 ^ w → 2 ^ n < 2 ^ W → 2 ^ T * (2 ^ W - 1) < p → ¬ InTable n T key t →
    cnt (fun al : E => Mid n T w W key t M al) ≤ 2 ^ n - 1

def planes : Prop :=
  ∀ (E : Type) [Field E] (T w W : ℕ) (t : ℕ → E) (M : ℕ → ℕ → E) (al : E), W ≤ 2 ^ w → Bits T w M →
    ∏ j ∈ range W, tabProd T t M al j ^ 2 ^ j = ∏ u ∈ range (2 ^ T), (al - t u) ^ multOf W M u

/-- Error 0: under the hypotheses below, true products and the rows give the relation after the
challenge. -/
def mid_of_rows : Prop :=
  ∀ (E : Type) [Field E] (n T w W : ℕ) (key t : ℕ → E) (M : ℕ → ℕ → E) (al PK : E) (PT U V : ℕ → E),
    1 ≤ W → Bits T w M → NumKeys n T W M → keyProd n key al = PK →
    (∀ j < W, tabProd T t M al j = PT j) → Rows W PK PT U V → Mid n T w W key t M al

def relK_iff : Prop :=
  ∀ (E : Type) [Field E] (n : ℕ) (key : ℕ → E) (al PK : E),
    Gp.Rel 0 n (facK key al) (fun _ => PK) ↔ keyProd n key al = PK

def relT_iff : Prop :=
  ∀ (E : Type) [Field E] (T w : ℕ) (t : ℕ → E) (M : ℕ → ℕ → E) (al : E) (PT : ℕ → E),
    Gp.Rel w T (facT w t M al) PT ↔ ∀ j < 2 ^ w, tabProd T t M al j = PT j

/-- States: the end claim of the keys' grand product is a claim on the extension of the keys. -/
def key_end : Prop :=
  ∀ (E : Type) [Field E] (n : ℕ) (key z : ℕ → E) (al h : E),
    Blocks.ext n (facK key al) z = h ↔ Blocks.ext n key z = al - h

/-- States: the end claim of the table's grand product, less the constant 1, is a sum with a public
coefficient and the bits. -/
def tab_end : Prop :=
  ∀ (E : Type) [Field E] (T w : ℕ) (t : ℕ → E) (M : ℕ → ℕ → E) (z : ℕ → E) (al h : E),
    Blocks.ext (T + w) (facT w t M al) z = h ↔
    Blocks.ext (T + w) (fun X => (al - 1 - t (X / 2 ^ w)) * M (X / 2 ^ w) (X % 2 ^ w)) z = h - 1

def honest_bits : Prop :=
  ∀ (E : Type) [Field E] (n T w W : ℕ) (key t : ℕ → E), Bits T w (hbit n W key t)

def honest_numKeys : Prop :=
  ∀ (E : Type) [Field E] (n T W : ℕ) (key t : ℕ → E),
    2 ^ n < 2 ^ W → InTable n T key t → NumKeys n T W (hbit n W key t)

def honest_ident : Prop :=
  ∀ (E : Type) [Field E] (n T W : ℕ) (key t : ℕ → E), 2 ^ n < 2 ^ W → InTable n T key t →
    ∀ al, keyProd n key al = ∏ j ∈ range W, tabProd T t (hbit n W key t) al j ^ 2 ^ j

def honest_rows : Prop :=
  ∀ (E : Type) [Field E] (W : ℕ) (PT : ℕ → E),
    1 ≤ W → Rows W (∏ j ∈ range W, PT j ^ 2 ^ j) PT (hU W PT) (hV W PT)

end Cb.Spec
