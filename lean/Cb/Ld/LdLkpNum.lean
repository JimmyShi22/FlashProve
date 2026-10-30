-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpNum.lean: numbers and corners of a cube, lowest bit first; the levels of a forest of
product trees as tables on cubes.
This file is about indexing: it translates between vectors indexed by the numbers below 2^k and
tables on the Boolean cube in k variables, for the product trees of a lookup argument. No protocol
occurs in it.

Definitions and statements (the statements in `Cb.Spec`). Proofs: Cb/Ld/LdLkpNumProofs.lean.

Why: the mathematics of the lookup (Cb/Gen/LkpAlg.lean, Blocks/LookupRel.lean, Blocks/Ext.lean)
speaks of vectors indexed by numbers. The blocks of Cb/Ld/LdPsc.lean and Cb/Ld/LdLine.lean speak of
tables on cubes, with points that are functions on the variables, and the newest variable is the
last.
The order of bits. `numLE x` = ∑_i x_i 2^i: coordinate i is bit i, the first coordinate is the
lowest bit. So a further last coordinate is a further top bit (`Spec.ldLkpNum_snoc`). `Alg.num` of
Alg/Mle.lean, and with it `Blocks.ext`, list the top bit first: numLE x = Alg.num (x read backwards)
(`Spec.ldLkpNum_rev`).
The levels. A forest of 2^g trees with 2^n leaves each; the leaf j of the tree X₀ is the factor
A (j 2^g + X₀) (`Blocks.lvl`). `cubeLvl g n A l`: level l as a table on the cube in g + l variables;
the first g coordinates name the tree. It is defined for all l: above the leaves (l ≥ n) the lower
half of level l + 1 is level l and the upper half is 1; for that the factors are cut off (`cutOne`:
1 from 2^(n+g) on).

Main names:
  `Spec.ldLkpNum_step`: for all l: an entry of level l is the product of the two entries of level
    l + 1 above it (last coordinate 0 and 1). No hypothesis on l.
  `Spec.ldLkpNum_lvl`: for l ≤ n it is `Blocks.lvl` at the number of the corner;
    `Spec.ldLkpNum_top`: level n holds the factors; `Spec.ldLkpNum_root`: level 0 holds the products
    of the trees.
  `Spec.ldLkpNum_rootK`, `Spec.ldLkpNum_rootT`: for the factors of the lookup: the one product over
    the keys (g = 0); the product over the table at the bit position that the corner numbers
    (g = w).
  `Spec.ldLkpNum_topK`, `Spec.ldLkpNum_topT`: the leaves: λ - key; 1 + bit (λ - 1 - entry), the
    corner's low w bits being the bit position.
  `Spec.ldLkpNum_lt`: numLE x < 2^k; `Spec.ldLkpNum_inj`: `numLE` is injective on the corners of a
    cube.
  `Spec.ldLkpNum_sum`, `Spec.ldLkpNum_prod`: sums and products over the cube are those over the
    numbers below 2^k.
  `Spec.ldLkpNum_ext`: the multilinear extension of the table x ↦ a (numLE x): `Blocks.ext`
    (Blocks/Ext.lean) at the point read backwards.

Terms: lean/GLOSSARY.md.
-/
import Alg.Mle
import Blocks.LookupRel
import Blocks.Ext
import Cb.Gen.LkpAlg

set_option autoImplicit false

namespace Cb.LdLkp
open Finset

/-- The number of a corner, lowest bit first. -/
def numLE {k : ℕ} (x : Fin k → Bool) : ℕ := ∑ i : Fin k, if x i then 2 ^ (i : ℕ) else 0

variable {E : Type}

/-- the factors, cut off: 1 from N on -/
def cutOne [One E] (N : ℕ) (A : ℕ → E) : ℕ → E := fun i => if i < N then A i else 1

/-- Level l of a forest, as a table on the cube in g + l variables. -/
def cubeLvl [CommMonoid E] (g n : ℕ) (A : ℕ → E) (l : ℕ) (x : Fin (g + l) → Bool) : E :=
  Blocks.lvl g n (cutOne (2 ^ (n + g)) A) l (numLE x)

end Cb.LdLkp

namespace Cb.Spec
open Finset Cb.LdLkp Cb.Lkp

def ldLkpNum_snoc : Prop :=
  ∀ (k : ℕ) (x : Fin k → Bool) (b : Bool),
    numLE (Fin.snoc x b : Fin (k + 1) → Bool) = numLE x + if b then 2 ^ k else 0
def ldLkpNum_lt : Prop := ∀ (k : ℕ) (x : Fin k → Bool), numLE x < 2 ^ k
def ldLkpNum_rev : Prop := ∀ (k : ℕ) (x : Fin k → Bool), numLE x = Alg.num fun i => x i.rev
def ldLkpNum_inj : Prop := ∀ k : ℕ, Function.Injective (numLE : (Fin k → Bool) → ℕ)
def ldLkpNum_sum : Prop :=
  ∀ (N : Type) [AddCommMonoid N] (k : ℕ) (f : ℕ → N),
    ∑ x : Fin k → Bool, f (numLE x) = ∑ c ∈ range (2 ^ k), f c
def ldLkpNum_prod : Prop :=
  ∀ (N : Type) [CommMonoid N] (k : ℕ) (f : ℕ → N),
    ∏ x : Fin k → Bool, f (numLE x) = ∏ c ∈ range (2 ^ k), f c

/-- An entry of a level is the product of the two entries above it, at every level. -/
def ldLkpNum_step : Prop :=
  ∀ (E : Type) [CommMonoid E] (g n : ℕ) (A : ℕ → E) (l : ℕ) (x : Fin (g + l) → Bool),
    cubeLvl g n A l x =
      cubeLvl g n A (l + 1) (Fin.snoc x false : Fin (g + l + 1) → Bool) *
        cubeLvl g n A (l + 1) (Fin.snoc x true : Fin (g + l + 1) → Bool)

def ldLkpNum_lvl : Prop :=
  ∀ (E : Type) [CommMonoid E] (g n : ℕ) (A : ℕ → E) (l : ℕ) (x : Fin (g + l) → Bool),
    l ≤ n → cubeLvl g n A l x = Blocks.lvl g n A l (numLE x)
def ldLkpNum_top : Prop :=
  ∀ (E : Type) [CommMonoid E] (g n : ℕ) (A : ℕ → E) (x : Fin (g + n) → Bool),
    cubeLvl g n A n x = A (numLE x)
def ldLkpNum_root : Prop :=
  ∀ (E : Type) [CommMonoid E] (g n : ℕ) (A : ℕ → E) (θ : Fin (g + 0) → Bool),
    cubeLvl g n A 0 θ = ∏ j ∈ range (2 ^ n), A (j * 2 ^ g + numLE θ)

/-- The products in the lookup's identity (this statement and the next). -/
def ldLkpNum_rootK : Prop :=
  ∀ (E : Type) [Field E] (v : ℕ) (key : ℕ → E) (al : E) (θ : Fin (0 + 0) → Bool),
    cubeLvl 0 v (facK key al) 0 θ = keyProd v key al
def ldLkpNum_rootT : Prop :=
  ∀ (E : Type) [Field E] (w d : ℕ) (t : ℕ → E) (M : ℕ → ℕ → E) (al : E) (θ : Fin (w + 0) → Bool),
    cubeLvl w d (facT w t M al) 0 θ = tabProd d t M al (numLE θ)
def ldLkpNum_topK : Prop :=
  ∀ (E : Type) [Field E] (v : ℕ) (key : ℕ → E) (al : E) (x : Fin (0 + v) → Bool),
    cubeLvl 0 v (facK key al) v x = al - key (numLE x)
def ldLkpNum_topT : Prop :=
  ∀ (E : Type) [Field E] (w d : ℕ) (t : ℕ → E) (M : ℕ → ℕ → E) (al : E) (x : Fin (w + d) → Bool),
    cubeLvl w d (facT w t M al) d x =
      1 + M (numLE x / 2 ^ w) (numLE x % 2 ^ w) * (al - 1 - t (numLE x / 2 ^ w))

/-- The extension of a table that is given by numbers: `Blocks.ext` at the point read backwards. -/
def ldLkpNum_ext : Prop :=
  ∀ (E : Type) [Field E] (k : ℕ) (a : ℕ → E) (z : Fin k → E),
    Alg.mle (fun x : Fin k → Bool => a (numLE x)) z =
      Blocks.ext k a (Blocks.nat fun i : Fin k => z i.rev)

end Cb.Spec
