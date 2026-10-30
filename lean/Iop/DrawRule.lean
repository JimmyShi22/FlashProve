-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/DrawRule.lean: challenge samplers of the standard form: a predicate that says from which basic
samplers, and by which rules only, a sampler is built; and the sampler of the coefficients of a
range proof. (Words of this library: lean/GLOSSARY.md.)

The condition `BS.Good` on a sampler (Iop/Draw.lean) says how far from uniform its values are; it
does not say which function of the blocks the sampler is: a sampler that returns the negative of the
sampled element satisfies the same condition. `BS.Rule bE sl s` says it:
s is built from
    unit      no block, the one value
    el        the sampler bE of E itself
    pos       a position among n = 2^L: the low L bits of the block (`Iop.BS.pos`; one block as long
              as 0 < L and L + sl < lam)
    coefs     a table of coefficients: for each column two blocks, the first for the signs, the
              second for the supports; bit u of each belongs to combination u (`BS.coefs`). (One
              coefficient, as two bits: its value is 0 if the support bit is 0; otherwise +1 or -1
              by the sign bit: `Prob.Coef`, `Prob.Coef.val`, Prob/Window.lean; a combination of the
              columns of a matrix: `Cb.Rng.combF`, Cb/Gen/RngAlg.lean.)
  by
    prod      a pair: the blocks of the left part, then those of the right part
    vec       a vector on Fin n: coordinate i reads the blocks i · b, .., i · b + b − 1
    fnE, piE  a family on an enumerated index type: the coordinates in the order of the enumeration
  And by nothing else: no map after sampling but the re-indexings inside `coefs`, `fnE`, `piE`, no
  number modulo something that is no power of two, no bit that costs a block (but a position among 2
  does pass, and so does `coefs` at n = 1), no numbering of the set of challenges (all four: but for
  what `el` lets in: bE is any sampler of any E).
    `Shape.Draws.Ruled`    every round of a list of rounds has such a sampler
    `Pow2`, `DrawRuled`    the samplers that the class `DrawOf` finds (Iop/DrawOf.lean) are of the
                           standard form, if the numbers of positions are powers of two. (`Bool` has
                           no instance: the class spends a block on a bit.)

Notation: `lam : ℕ`: the bits of a block (`Dig lam`, Iop/Wire.lean); `E : Type`, `bE : BS lam E`,
`sl : ℕ`: in `DrawOf bE sl C` (Iop/DrawOf.lean), the sampler bE of E and the slack sl of positions;
combination, column, support bit, sign bit: see the docstrings of `BS.coefs` and `BS.coefEquiv`
below.
Limits: the predicate does not say which enumerations the index types have (data of the caller), nor
that bE is the right sampler of E.
-/
import Iop.DrawOf

namespace Iop
open Prob
open scoped ENNReal

namespace BS
variable {lam : ℕ}

/-- from the two strings of bits of each column to the table of coefficients: bit u of the second
string is the support bit, bit u of the first the sign bit of combination u -/
def coefEquiv (n : ℕ) (ι : Type) :
    (ι → (Fin n → Bool) × (Fin n → Bool)) ≃ (Fin n → ι → Bool × Bool) where
  toFun := fun f u c => ((f c).2 u, (f c).1 u)
  invFun := fun g c => (fun u => (g u c).2, fun u => (g u c).1)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The coefficients of a range proof (combination u < n, column c; support bit, sign bit): for each
column two blocks, signs then supports; bit u of each belongs to combination u; the other bits are
thrown away. -/
def coefs (n : ℕ) (h : n ≤ lam) (ι : Type) [FinEnum ι] : BS lam (Fin n → ι → Bool × Bool) :=
  (fnE (ι := ι) ((bits n h).prod (bits n h))).map (coefEquiv n ι)

theorem coefs_good (n : ℕ) (h : n ≤ lam) (ι : Type) [FinEnum ι] {κ : ℝ≥0∞} (hκ : 1 ≤ κ) :
    (coefs n h ι).Good (κ ^ (coefs n h ι).b) := by
  refine map_good _ (fnE_good ?_)
  have := prod_good (bits_good n h) (bits_good n h)
  rw [one_mul] at this
  exact this.mono (one_le_pow₀ hκ)

/-- s is of the standard form: built by these rules, and by nothing else. -/
inductive Rule {E : Type} (bE : BS lam E) (sl : ℕ) : {C : Type} → BS lam C → Prop
  | unit : Rule bE sl BS.unit
  | el : Rule bE sl bE
  | pos (n L : ℕ) (h : 0 < n) (hn : n = 2 ^ L) : Rule bE sl (BS.pos lam sl n h)
  | coefs (n : ℕ) (h : n ≤ lam) (ι : Type) [FinEnum ι] : Rule bE sl (BS.coefs n h ι)
  | prod {C D : Type} {s : BS lam C} {t : BS lam D} : Rule bE sl s → Rule bE sl t → Rule bE sl (s.prod t)
  | vec {C : Type} {s : BS lam C} (n : ℕ) : Rule bE sl s → Rule bE sl (s.vec n)
  | fnE {ι C : Type} [FinEnum ι] {s : BS lam C} : Rule bE sl s → Rule bE sl (BS.fnE (ι := ι) s)
  | piE {ι : Type} [FinEnum ι] {C : ι → Type} {s : ∀ i, BS lam (C i)} : (∀ i, Rule bE sl (s i)) → Rule bE sl (BS.piE s)

end BS

/-- every round has a sampler of the standard form -/
def Shape.Draws.Ruled {lam : ℕ} {E : Type} (bE : BS lam E) (sl : ℕ) :
    (s : Shape) → s.Draws lam → Prop
  | [], _ => True
  | _ :: s, (d, ds) => BS.Rule bE sl d ∧ Shape.Draws.Ruled bE sl s ds

theorem Shape.Draws.ruled_app {lam : ℕ} {E : Type} {bE : BS lam E} {sl : ℕ} :
    ∀ {s t : Shape} (a : s.Draws lam) (b : t.Draws lam), Shape.Draws.Ruled bE sl s a →
      Shape.Draws.Ruled bE sl t b → Shape.Draws.Ruled bE sl (s ++ t) (Shape.Draws.app a b)
  | [], _, _, _, _, hb => hb
  | _ :: _, _, (_, as), b, ha, hb => ⟨ha.1, Shape.Draws.ruled_app as b ha.2 hb⟩

theorem Shape.Draws.ruled_rep {lam : ℕ} {E : Type} {bE : BS lam E} {sl : ℕ} (r : Round)
    (h : BS lam r.Chal) (hg : BS.Rule bE sl h) :
    ∀ (n : ℕ) {t : Shape} (d : t.Draws lam), Shape.Draws.Ruled bE sl t d →
      Shape.Draws.Ruled bE sl (List.replicate n r ++ t) (Shape.Draws.rep r h n d)
  | 0, _, _, hd => hd
  | n + 1, _, d, hd => ⟨hg, Shape.Draws.ruled_rep r h hg n d hd⟩

/-- n is a power of two -/
class Pow2 (n : ℕ) : Prop where
  ex : ∃ L, n = 2 ^ L

/-- The sampler that the class `DrawOf` finds is of the standard form. -/
class DrawRuled {lam : ℕ} {E : Type} (bE : BS lam E) (sl : ℕ) (C : Type) [d : DrawOf bE sl C] :
    Prop where
  rule : BS.Rule bE sl d.bs

namespace DrawRuled
variable {lam : ℕ} {E : Type} (bE : BS lam E) (sl : ℕ)

instance unit : DrawRuled bE sl Unit := ⟨.unit⟩
instance (priority := high) self : DrawRuled bE sl E := ⟨.el⟩
instance fin (n : ℕ) [Nonempty (Fin n)] [p : Pow2 n] : DrawRuled bE sl (Fin n) :=
  ⟨by obtain ⟨L, hL⟩ := p.ex; exact .pos n L _ hL⟩
instance prod {C D : Type} [DrawOf bE sl C] [DrawOf bE sl D]
    [a : DrawRuled bE sl C] [b : DrawRuled bE sl D] : DrawRuled bE sl (C × D) :=
  ⟨.prod a.rule b.rule⟩
instance pi {ι : Type} [FinEnum ι] {C : ι → Type}
    [∀ i, DrawOf bE sl (C i)] [a : ∀ i, DrawRuled bE sl (C i)] : DrawRuled bE sl (∀ i, C i) :=
  ⟨.piE fun i => (a i).rule⟩
instance (priority := high) fn {ι C : Type} [FinEnum ι] [DrawOf bE sl C] [a : DrawRuled bE sl C] :
    DrawRuled bE sl (ι → C) := ⟨.fnE a.rule⟩
instance (priority := high + 1) vec (n : ℕ) {C : Type} [DrawOf bE sl C] [a : DrawRuled bE sl C] :
    DrawRuled bE sl (Fin n → C) := ⟨.vec n a.rule⟩

end DrawRuled

end Iop
