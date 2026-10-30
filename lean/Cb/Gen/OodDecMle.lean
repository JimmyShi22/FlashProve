-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecMle.lean: an out-of-domain sample whose answers are values of the message's multilinear
extension at random points. It is the sample at multilinear points, an instance of the sample maps
of Cb/Gen/OodDec.lean.

Definitions and statements; the proofs are in Cb/Gen/OodDecMleProofs.lean.

The entries J of a message are placed on the vertices of a cube with the variables μ by an injection
pl (a message whose length is not a power of two is padded with zeros: `placed`). A seed is a list
of s points of E^μ, drawn independently; the i-th answer is the value at the i-th point of the
multilinear extension of the placed message. For a table of interleaved rows with view = `whole`
this is one value of the message of the whole table (rows and places together) for each point, not
one value for each row.

Main names, the definitions:
  `Sample.mle`: the sample map: `Sample.pow` of the equality kernel (`Evader.eqPt`, `Evader.comap`
    of Cb/Gen/BatEvader.lean). The kernel is eq(z, b) = ∏_v (z_v if b_v = 1, else 1 - z_v)
    (`Alg.eqk`); the multilinear extension of u is ∑_b eq(z, b) u[b] (`Alg.mle`).
  `placed`, `plBoth`: see their docstrings.

Main names, the statements. m = |μ| is the number of variables. All but `ood_val_mle`,
`ood_frac_mle` and `ood_val_rows` assume that the placement is injective.
  `ood_val_mle`, `ood_placed_at`: see the docstrings of `ood_val_mle` and `placed`.
  `ood_ok_mle`: the property of a sample map (`Sample.OK`), with err (`Sample.err`) =
    (m |E|^(m-1))^s, by the Schwartz-Zippel count for multilinear extensions
    (`Alg.count_mle_zero_le`, through `Cb.ok_eqPt`, `Cb.ok_comap`).
  `ood_frac_mle`: err as a fraction: the fraction is at most (m / |E|)^s.
  `ood_cnt_mle`: the counting lemma (`ood_cnt_clash`, Cb/Gen/OodDec.lean) at multilinear points, for
    a table with at most L tables of messages within the radius: the lists of s points at which some
    answers get the value "several" number at most (L choose 2) (m |E|^(m-1))^s; as a fraction of
    all lists of points: at most (L choose 2) (m / |E|)^s. Note the form: the power is on m / |E|
    alone; the number of pairs enters once.
  `ood_cnt_mle_plain`, `ood_cnt_mle_plain_pow`: the first of these bounds without decoder and sample
    map, for a reader who wants the mathematics alone: the points (lists of s points) at which two
    tables of messages within the radius with different views have the same value(s) of the
    multilinear extension.
  `ood_val_rows`: the answer at the point (x | z) is the answer at z of the row
    ∑_a eq(x, plR a) M_a. So a claim on the answer is a claim on the combination of the rows by the
    equality kernel at x.

Limits: for (L choose 2) m^s ≥ |E|^s the count says nothing. Nothing on hiding. No pad under the
sample (a sample row with further coefficients on fresh random coordinates is another instance of
`Cb.Ood.Sample`, not built here).
That the sample may be a multilinear point on the message of the whole interleaved word follows
advice (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.OodDec
import Alg.Mle

set_option autoImplicit false

namespace Cb.Ood
open Prob Blocks Alg

/-- The sample at s independent multilinear points. -/
@[reducible] def Sample.mle (E μ J : Type) [Field E] [Fintype E] [Fintype μ] [DecidableEq μ]
    (pl : J → μ → Bool) (s : ℕ) : Sample E J :=
  Sample.pow ((Evader.eqPt E μ).comap pl) s

/-- The message on the cube: for an injective pl, the entry u j at the vertex pl j, 0 at the other
vertices. -/
def placed {E μ J : Type} [Field E] [Fintype μ] [Fintype J] (pl : J → μ → Bool) (u : J → E) :
    (μ → Bool) → E :=
  fun b => ∑ j, if pl j = b then u j else 0

/-- Rows on one cube, places on another: the entry (row a, place i) is at the vertex (plR a | plP i)
of the cube with the variables μR ⊕ μP. -/
def plBoth {R κ μR μP : Type} (plR : R → μR → Bool) (plP : κ → μP → Bool) :
    R × κ → μR ⊕ μP → Bool :=
  fun n => Sum.elim (plR n.1) (plP n.2)

end Cb.Ood

namespace Cb.Spec
open Prob Blocks Alg Cb.Ood

/-- The answers are the values of the multilinear extension of the placed message. -/
def ood_val_mle : Prop :=
  ∀ (E μ J : Type) [Field E] [Fintype E] [Fintype μ] [DecidableEq μ] [Fintype J] (pl : J → μ → Bool)
      (s : ℕ) (ρ : Fin s → μ → E) (u : J → E) (i : Fin s),
    (Sample.mle E μ J pl s).val ρ u i = Alg.mle (placed pl u) (ρ i)

def ood_placed_at : Prop :=
  ∀ (E μ J : Type) [Field E] [Fintype μ] [Fintype J] (pl : J → μ → Bool) (u : J → E),
    Function.Injective pl →
    (∀ j, placed pl u (pl j) = u j) ∧ ∀ b, (∀ j, pl j ≠ b) → placed pl u b = 0

def ood_ok_mle : Prop :=
  ∀ (E μ J : Type) [Field E] [Fintype E] [Fintype μ] [DecidableEq μ] [Fintype J]
      (pl : J → μ → Bool) (s : ℕ),
    Function.Injective pl → (Sample.mle E μ J pl s).OK

/-- The number of the sample map, as it is and as a fraction of the seeds. -/
def ood_frac_mle : Prop :=
  ∀ (E μ J : Type) [Field E] [Fintype E] [Fintype μ] [DecidableEq μ] (pl : J → μ → Bool) (s : ℕ),
    (Sample.mle E μ J pl s).err = (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1)) ^ s ∧
    (Sample.mle E μ J pl s).err * Fintype.card E ^ s ≤
      Fintype.card μ ^ s * Fintype.card (Fin s → μ → E)

/-- The counting lemma at multilinear points. -/
def ood_cnt_mle : Prop :=
  ∀ (E ι κ R μ J : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq μ]
      [Fintype J] (G : Matrix ι κ E) (e : ℕ) (view : (R → κ → E) → J → E) (pl : J → μ → Bool)
      (s : ℕ) (f : R → ι → E) (L : ℕ),
    Function.Injective pl → ListLE (DecodesTo G e f) L →
    cnt (fun ρ : Fin s → μ → E => ∃ y, decS G e view (Sample.mle E μ J pl s) f ρ y = .several) ≤
      L.choose 2 * (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1)) ^ s ∧
    cnt (fun ρ : Fin s → μ → E => ∃ y, decS G e view (Sample.mle E μ J pl s) f ρ y = .several) *
        Fintype.card E ^ s ≤
      L.choose 2 * Fintype.card μ ^ s * Fintype.card (Fin s → μ → E)

/-- The counting lemma at one multilinear point, in plain words: no decoder, no sample map. Under
the hypotheses below, it bounds the number of the points z at which two tables of messages within
the radius, with different views, have the same value of the multilinear extension. -/
def ood_cnt_mle_plain : Prop :=
  ∀ (E ι κ R μ J : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq μ]
      [Fintype J] (G : Matrix ι κ E) (e : ℕ) (view : (R → κ → E) → J → E) (pl : J → μ → Bool)
      (f : R → ι → E) (L : ℕ),
    Function.Injective pl → ListLE (DecodesTo G e f) L →
    cnt (fun z : μ → E =>
        ∃ M M',
          DecodesTo G e f M ∧ DecodesTo G e f M' ∧ view M ≠ view M' ∧
          Alg.mle (placed pl (view M)) z = Alg.mle (placed pl (view M')) z) ≤
      L.choose 2 * (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1))

/-- The same for s independent points: the two have the same value at all of them. -/
def ood_cnt_mle_plain_pow : Prop :=
  ∀ (E ι κ R μ J : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq μ]
      [Fintype J] (G : Matrix ι κ E) (e : ℕ) (view : (R → κ → E) → J → E) (pl : J → μ → Bool)
      (s : ℕ) (f : R → ι → E) (L : ℕ),
    Function.Injective pl → ListLE (DecodesTo G e f) L →
    cnt (fun z : Fin s → μ → E =>
        ∃ M M',
          DecodesTo G e f M ∧ DecodesTo G e f M' ∧ view M ≠ view M' ∧
          ∀ i, Alg.mle (placed pl (view M)) (z i) = Alg.mle (placed pl (view M')) (z i)) ≤
      L.choose 2 * (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1)) ^ s

/-- A sample of the whole table is a sample of one combined row. -/
def ood_val_rows : Prop :=
  ∀ (E R κ μR μP : Type) [Field E] [Fintype E] [Fintype R] [Fintype κ] [Fintype μR] [DecidableEq μR]
      [Fintype μP] [DecidableEq μP] (plR : R → μR → Bool) (plP : κ → μP → Bool) (s : ℕ)
      (ρ : Fin s → μR ⊕ μP → E) (M : R → κ → E) (i : Fin s),
    (Sample.mle E (μR ⊕ μP) (R × κ) (plBoth plR plP) s).val ρ (whole M) i =
      (Sample.mle E μP κ plP s).val
        (fun i v => ρ i (Sum.inr v)) (∑ a, eqk (fun v => ρ i (Sum.inl v)) (plR a) • M a) i

def ood_plBoth_inj : Prop :=
  ∀ (R κ μR μP : Type) (plR : R → μR → Bool) (plP : κ → μP → Bool),
    Function.Injective plR → Function.Injective plP → Function.Injective (plBoth plR plP)

end Cb.Spec
