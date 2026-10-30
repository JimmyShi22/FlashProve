-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/Gen/CodeListRSF.lean: the statement on codes (`Cb.BCHKS46F`), on
agreement of Reed-Solomon codes, in a narrower form: for the finite extensions of one base field F,
points in F. The three statements on codes of this file follow from this form already.

Definitions, statements (in `Cb.Spec`) and proofs.
Cb/Gen/CodeListRS.lean has the proposition BCHKS46: mutual correlated agreement of Reed-Solomon
codes below the Johnson radius, for two words (a line; no rows), for every finite field and any
distinct points of it, as its source states it (named above; it gives an outline of a proof). (The
source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.)

Why:
For a HYPOTHESIS the narrower form is the more cautious: the wide one also speaks of small
characteristics, and the source's outline treats separable factors only (by reading); no other
factor occurs when the characteristic exceeds (m + 1/2) / sqrt(k / n) (m: Cb.bchksM), which holds of
a field of characteristic 2^64 - 2^32 + 1 at every m of interest.

Main names:
  `BCHKS46F F`: the same statement, word for word, for every finite field K that is an algebra over
    F, and distinct points x in F (read in K). The same count (`Cb.bchksBound n k e`: it does not
    depend on the field). It says: for 0 < k, 0 < e with n k < (n - e)^2 (below the Johnson radius)
    and any two words u₀, u₁ over K on the n points, the number of exceptional z in K is at most the
    count. Here z is exceptional if there is a set A of at least n - e positions on which u₀ + z u₁
    agrees with a polynomial of degree at most k (`OnRS`, Cb/Gen/CodeListRS.lean), while u₀ and u₁
    do not both agree on A with such polynomials.
  `BCHKS46RowsF F`: the same for tables of any finite number of rows (agreement by columns), the
    same count.
  `Spec.bchks46F_of_wide`: BCHKS46 → BCHKS46F F, for every F. The wide form is the stronger.
  `Spec.rows_cost_nothingF`: BCHKS46F F → BCHKS46RowsF F. Our own lemma, proved, as
    Cb/Gen/CodeListRows.lean's: a table over K is one word over an extension of K, which is again
    an extension of F, on the same points.
  `Spec.rs_mcaAtF`, `Spec.rs_proxF`: BCHKS46F F → for `Code.RS.code` of dimension k + 1, 0 < k, on
    distinct points of F, tables over any finite E over F: agreement (and, proved without it,
    lists) at all radii e > 0 below the Johnson radius.
  `Spec.rs_group_proxF`: BCHKS46F F → families of such codes under an even reading (the statement
    of Cb/Gen/CodeRepRS.lean's `rs_group_prox` at this F, with its further hypotheses).

Notation: `Cb.bchksBound n k e`: the count, a real number (its formula: Cb/Gen/CodeListRS.lean);
`msg`, `r`, `e₀`, `mca₀`: natural numbers (`msg`, `r` in `Spec.rs_group_proxF`: one for each code),
arguments of `Code.RS.code` (Code/RS.lean).

Limits:
Not proved here, no axiom: BCHKS46F F stands as a hypothesis in the Lean text of each statement that
uses it.
This file does not say whether the statement holds, whether its source proves it, or that the count
is small against a field.
Terms: lean/GLOSSARY.md.
-/
/- Limits: `BCHKS46F` is an assumed statement: a definition of a proposition, which this file does
not prove. Nothing in this library checks that it says what its source shows. -/
import Cb.Gen.CodeListRows
import Cb.Gen.CodeRepRS

set_option autoImplicit false

namespace Cb
open Prob Blocks Polynomial

/-- **The statement on codes (`BCHKS46F`), for the finite extensions of F and points in F** (not
proved here, not an axiom). -/
def BCHKS46F (F : Type) [Field F] : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [Algebra F K] (n k e : ℕ) (x : Fin n → F),
    Function.Injective x → 0 < k → 0 < e → n * k < (n - e) ^ 2 →
    ∀ u₀ u₁ : Fin n → K,
      (cnt (fun z : K =>
          ∃ A : Finset (Fin n),
            n ≤ A.card + e ∧
            OnRS (fun j => algebraMap F K (x j)) k (fun j => u₀ j + z * u₁ j) A ∧
            ¬ (OnRS (fun j => algebraMap F K (x j)) k u₀ A ∧
              OnRS (fun j => algebraMap F K (x j)) k u₁ A)) : ℝ) ≤ bchksBound n k e

/-- The same for tables. -/
def BCHKS46RowsF (F : Type) [Field F] : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [Algebra F K] (n k e : ℕ) (x : Fin n → F),
    Function.Injective x → 0 < k → 0 < e → n * k < (n - e) ^ 2 →
    ∀ (R : Type) [Finite R] (u₀ u₁ : R → Fin n → K),
      (cnt (fun z : K =>
          ∃ A : Finset (Fin n),
            n ≤ A.card + e ∧
            (∀ a, OnRS (fun j => algebraMap F K (x j)) k (fun j => u₀ a j + z * u₁ a j) A) ∧
            ¬ ((∀ a, OnRS (fun j => algebraMap F K (x j)) k (u₀ a) A) ∧
              ∀ a, OnRS (fun j => algebraMap F K (x j)) k (u₁ a) A)) : ℝ) ≤ bchksBound n k e

namespace Spec
section
variable (F : Type) [Field F]

/-- The wide form is the stronger. -/
def bchks46F_of_wide : Prop := BCHKS46 → BCHKS46F F

/-- Rows cost nothing: `BCHKS46F F` gives `BCHKS46RowsF F`. -/
def rows_cost_nothingF : Prop := BCHKS46F F → BCHKS46RowsF F

def rs_mcaAtF : Prop :=
  BCHKS46F F →
  ∀ (E : Type) [Field E] [Finite E] [Algebra F E] (n k msg r e₀ mca₀ : ℕ) (x : Fin n → F),
    Function.Injective x →
    ∀ e : ℕ, 0 < k → 0 < e → n * k < (n - e) ^ 2 →
      ∀ (R : Type) [Finite R],
        (Code.RS.code x (k + 1) msg r e₀ mca₀).MCAat E R e ⌊bchksBound n k e⌋₊

/-- From `BCHKS46F F`: bounds on list and agreement (`Enc.Prox`, Cb/Gen/CodeList.lean) as functions
of the radius, for all radii e > 0 below the Johnson radius. (not all hypotheses are named here: see
the statement below) -/
def rs_proxF : Prop :=
  BCHKS46F F →
  ∀ (E : Type) [Field E] [Finite E] [Algebra F E] (n k msg r e₀ mca₀ : ℕ) (x : Fin n → F),
    Function.Injective x → 0 < k →
    (Code.RS.code x (k + 1) msg r e₀ mca₀).Prox E (fun e => 0 < e ∧ n * k < (n - e) ^ 2)
      (fun e _ => listMax n (n - k) e) (fun e _ => ⌊bchksBound n k e⌋₊)

/-- Families under an even reading (`Reading.Even`, Cb/Gen/CodeRep.lean): `Reading.Prox` (the same
file), from `BCHKS46F F`, under the hypotheses below, at the radii that the statement names. -/
def rs_group_proxF : Prop :=
  BCHKS46F F →
  ∀ (E : Type) [Field E] [Finite E] [Algebra F E] (A : Type) [Fintype A]
      (n k msg r : A → ℕ) (x : ∀ a, Fin (n a) → F),
    (∀ a, Function.Injective (x a)) → (∀ a, 0 < k a) → (∀ a, k a < n a) →
    ∀ T : Reading (fun a => Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0), T.Even →
      ∀ D : ℕ, (∀ a, D ≤ T.mult a * (n a - k a)) →
        ∀ (R : A → Type) [∀ a, Finite (R a)], T.Prox E R
          (fun e => InJohnson (Fintype.card T.P) D e ∧ ∀ a, T.mult a ≤ e)
          (fun e => listMax (Fintype.card T.P) D e)
          (fun e => ∑ a, ⌊bchksBound (n a) (k a) (e / T.mult a)⌋₊)

end
end Spec

open CodeListRows CodeListRS CodeRep

section
variable (F : Type) [Field F]

-- Limit: the statement has the premise `Cb.BCHKS46`, a hypothesis; this file does not prove it.
theorem bchks46F_of_wide : Spec.bchks46F_of_wide F := fun H K _ _ _ n k e x hx hk he hJ u₀ u₁ =>
  H K n k e (fun j => algebraMap F K (x j)) ((algebraMap F K).injective.comp hx) hk he hJ u₀ u₁

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem rows_cost_nothingF : Spec.rows_cost_nothingF F := by
  intro H E _ _ _ n k e x hx hk he hJ R _ u₀ u₁
  rcases isEmpty_or_nonempty R with hR | hR
  · rw [cnt_false fun z ⟨A, _, _, h⟩ => h ⟨fun a => isEmptyElim a, fun a => isEmptyElim a⟩]
    exact le_trans (Nat.cast_le.mpr (Nat.zero_le _)) (H E n k e x hx hk he hJ 0 0)
  · cases nonempty_fintype R
    obtain ⟨p, hp⟩ := CharP.exists E
    haveI : Fact p.Prime := ⟨CharP.char_is_prime E p⟩
    haveI : NeZero (Fintype.card R) := ⟨Fintype.card_ne_zero⟩
    let K := FiniteField.Extension E p (Fintype.card R)
    letI : Algebra F K := ((algebraMap E K).comp (algebraMap F E)).toAlgebra
    let b : Module.Basis R E K :=
      (Module.finBasisOfFinrankEq E K (FiniteField.finrank_extension E p (Fintype.card R))).reindex
        (Fintype.equivFin R).symm
    have h := H K n k e x hx hk he hJ (pack b u₀) (pack b u₁)
    refine le_trans
      (Nat.cast_le.mpr (cnt_le_cnt_of_injective (algebraMap E K) (algebraMap E K).injective ?_)) h
    rintro θ ⟨A, hA, h1, h2⟩
    refine ⟨A, hA, ?_,
      fun h3 =>
        h2 ⟨(rows_iff (fun j => algebraMap F E (x j)) k b u₀ A).mpr h3.1,
            (rows_iff (fun j => algebraMap F E (x j)) k b u₁ A).mpr h3.2⟩⟩
    have h4 :=
      (rows_iff (fun j => algebraMap F E (x j)) k b (fun a j => u₀ a j + θ * u₁ a j) A).mp h1
    have e1 : pack b (fun a j => u₀ a j + θ * u₁ a j) =
        fun j => pack b u₀ j + algebraMap E K θ * pack b u₁ j :=
      funext fun j => pack_line b u₀ u₁ θ j
    rwa [e1] at h4

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem rs_mcaAtF : Spec.rs_mcaAtF F := by
  intro H E _ _ _ n k msg r e₀ mca₀ x hx e hk he hJ R _ f₀ f₁
  have h := rows_cost_nothingF F H E n k e x hx hk he hJ R f₀ f₁
  refine Nat.le_floor
    (le_trans (Nat.cast_le.mpr (le_of_eq (cnt_congr fun θ => exists_congr fun S => ?_))) h)
  rw [CodeListRS.onCode_iff, CodeListRS.onCode_iff, CodeListRS.onCode_iff]
  exact Iff.rfl

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem rs_proxF : Spec.rs_proxF F := by
  intro H E _ _ _ n k msg r e₀ mca₀ x hx hk
  refine ⟨fun e he R _ f => ?_,
    fun e he R _ => rs_mcaAtF F H E n k msg r e₀ mca₀ x hx e hk he.1 he.2 R⟩
  have hkn := lt_of_radius he.2
  have h := johnson_enc F E (Code.RS.code x (k + 1) msg r e₀ mca₀) e (Code.RS.code_dist hx hkn)
    (by
      show InJohnson n (n - (k + 1) + 1) e
      rw [dist_eq hkn]
      exact inJohnson_of_radius he.2) R f
  have h' : cnt (fun M => DecodesTo ((Code.RS.code x (k + 1) msg r e₀ mca₀).GE E) e f M) ≤
      listMax n (n - (k + 1) + 1) e := h
  rwa [dist_eq hkn] at h'

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem rs_group_proxF : Spec.rs_group_proxF F := by
  intro H E _ _ _ A _ n k msg r x hx hk hkn T hT D hD R _
  have hd : ∀ a, HasDist (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).G
      (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).d :=
    fun a => Code.RS.code_dist (hx a) (hkn a)
  have hD' : ∀ a, D ≤ T.mult a * (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).d := fun a => by
    show D ≤ T.mult a * (n a - (k a + 1) + 1)
    rw [dist_eq (hkn a)]
    exact hD a
  have hP := prox_johnson_of_comps F E A _ T hT hd D hD' R _ _ _ fun a =>
    rs_proxF F H E (n a) (k a) (msg a) (r a) 0 0 (x a) (hx a) (hk a)
  have hok : ∀ e, (InJohnson (Fintype.card T.P) D e ∧ ∀ a, T.mult a ≤ e) →
      InJohnson (Fintype.card T.P) D e ∧
      ∀ a, 0 < e / T.mult a ∧ n a * k a < (n a - e / T.mult a) ^ 2 := by
    intro e he
    refine ⟨he.1, fun a => ⟨Nat.div_pos (he.2 a) (hT a).1, ?_⟩⟩
    have hc : Fintype.card T.P = T.mult a * n a := even_card F A _ T hT a
    have h1 := he.1
    rw [hc] at h1
    have h2 := inJohnson_comp (n a) (n a - k a) (T.mult a) D e (hD a) h1
    unfold InJohnson at h2
    rwa [Nat.sub_sub_self (hkn a).le] at h2
  exact ⟨fun e he => hP.list e (hok e he), fun e he => hP.mca e (hok e he)⟩

end
end Cb
