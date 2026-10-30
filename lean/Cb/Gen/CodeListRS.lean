-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeListRS.lean: Reed-Solomon codes below the Johnson radius: the new code interface, under
one assumed statement (Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at
STOC 2026; the theorem is not in the proceedings, which state the plain form (their Theorem 1.5)),
taken as a named hypothesis.

Definitions and statements (the latter in `Cb.Spec`); the proofs are in
Cb/Gen/CodeListRSProofs.lean and Cb/Gen/CodeListRows.lean.

The hypothesis. "BCHKS46" restates Theorem 4.6 ("List correlated agreement, up to Johnson bound"),
at its parameter M = 1 (lines u0 + z u1), of
   E. Ben-Sasson, D. Carmon, U. Haböck, S. Kopparty, S. Saraf, "On Proximity Gaps for Reed-Solomon
   Codes", Cryptology ePrint Archive 2025/2055.
The text that was read for this file is the same paper's issue as ECCC Technical Report TR25-169,
dated November 7, 2025.
What the theorem says there, at M = 1: for the Reed-Solomon code of the polynomials of degree at
most k on any n distinct points of any finite field, with rho = k / n (so 1 - rho is the relative
distance;
the dimension is k + 1), any radius gamma with 0 < gamma < 1 - sqrt(rho), and any two words u0, u1,
the number of z in the field for which there is a set A of at least (1 - gamma) n points on which
u0 + z u1 agrees with a codeword while u0 and u1 do not both, is at most
   (2 (m + 1/2)^5 + 3 (m + 1/2) gamma rho) / (3 rho^(3/2)) n + (m + 1/2) / sqrt(rho),
   with m = max (ceil (sqrt(rho) / (1 - sqrt(rho) - gamma)), 3).
The paper says that this notion is the one that others call strong, or mutual, correlated
agreement; it is, set by set, the notion of Code.Enc.MCA (Code/Iface.lean) for ONE row.
Here gamma = e / n for a natural number e > 0; "gamma < 1 - sqrt(rho)" is written n k < (n - e)^2;
rho^(3/2) is written rho sqrt(rho). So `BCHKS46` asks for no more than the theorem says. How far the
source carries: see Limits.

The second named proposition. "BCHKS46Rows": the same with tables of any finite number of rows in
the place of words (agreement by columns), with the same count. The paper does not state it.
`Spec.rows_cost_nothing` says that it follows from `BCHKS46`, because the theorem holds over every
finite field with a count that does not depend on the field: a table of r rows is one word over an
extension of degree r. That is proved in Cb/Gen/CodeListRows.lean, so in the end, of the two named
propositions only `BCHKS46` is left as a hypothesis (`Spec.rs_listProps`, `Spec.rs_prox`).

Main names:
  `Spec.rs_prox_of_rows`, `Spec.rs_listProps_of_rows`: the interface of Cb/Gen/CodeList.lean
    (`Code.Enc.Prox`, `Code.Enc.ListProps`) from `BCHKS46Rows`; `Spec.rs_prox`,
    `Spec.rs_listProps`: the same from `BCHKS46`. What they conclude, with its further hypotheses,
    is `RsProx` and `RsListProps`.

Limits: how far the source carries. As printed, the proof of Theorem 4.6 is an outline of one
paragraph, which says how an earlier section's analysis is to be generalised. The paper credits a
proof of the property, up to the Johnson bound, to a note that it cites as a personal communication;
the count in the theorem is the paper's own ("We state the result with the improved bounds"), and
the outline is all that it gives for that count. The makers of this library have checked no full
proof of it.
`BCHKS46` is a definition of a proposition, not an axiom: this file does not prove it, and every
statement that uses it has it as a hypothesis in its own text.
This file says nothing on circle codes or other subcodes. It says nothing on combinations of more
than two tables (M > 1 in the theorem; powers or other generators). It says nothing at the radius
0; `Cb.prox_third` covers it where 0 < d, and every radius e with 3 e < d (its premise:
`HasDist C.G C.d`). It says nothing on numerals: whether the count is small against a given field
is not looked at.
Terms: lean/GLOSSARY.md.
-/
/- Limits: `BCHKS46` is an assumed statement: a definition of a proposition, which this file does
not prove. Nothing in this library checks that it says what its source shows. -/
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Defs
import Code.RS
import Cb.Gen.CodeList
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob Blocks Polynomial

/-- On the set A of positions the word u agrees with a polynomial of degree at most k, evaluated at
the points x. -/
def OnRS {K : Type} [Field K] {n : ℕ} (x : Fin n → K) (k : ℕ) (u : Fin n → K) (A : Finset (Fin n)) :
    Prop :=
  ∃ p : K[X], p.degree < ((k + 1 : ℕ) : WithBot ℕ) ∧ ∀ j ∈ A, u j = p.eval (x j)

/-- The number m of the theorem, at rho = k / n and gamma = e / n. -/
def bchksM (n k e : ℕ) : ℝ :=
  max ((⌈Real.sqrt ((k : ℝ) / n) / (1 - Real.sqrt ((k : ℝ) / n) - (e : ℝ) / n)⌉ : ℤ) : ℝ) 3

/-- The count of the theorem, at rho = k / n and gamma = e / n. -/
def bchksBound (n k e : ℕ) : ℝ :=
  (2 * (bchksM n k e + 1 / 2) ^ 5 + 3 * (bchksM n k e + 1 / 2) * ((e : ℝ) / n) * ((k : ℝ) / n)) /
      (3 * (((k : ℝ) / n) * Real.sqrt ((k : ℝ) / n))) * n +
    (bchksM n k e + 1 / 2) / Real.sqrt ((k : ℝ) / n)

/-- **The statement on codes, as a proposition** (its source: see the header; not proved here, not
an axiom). -/
def BCHKS46 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n k e : ℕ) (x : Fin n → K), Function.Injective x → 0 < k →
    0 < e → n * k < (n - e) ^ 2 →
    ∀ u₀ u₁ : Fin n → K,
      (cnt (fun z : K =>
          ∃ A : Finset (Fin n),
            n ≤ A.card + e ∧
            OnRS x k (fun j => u₀ j + z * u₁ j) A ∧
            ¬ (OnRS x k u₀ A ∧ OnRS x k u₁ A)) : ℝ) ≤ bchksBound n k e

/-- The same for tables: rows indexed by any finite R, agreement on a common set of positions, the
same count. -/
def BCHKS46Rows : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n k e : ℕ) (x : Fin n → K), Function.Injective x → 0 < k →
    0 < e → n * k < (n - e) ^ 2 →
    ∀ (R : Type) [Finite R] (u₀ u₁ : R → Fin n → K),
      (cnt (fun z : K =>
          ∃ A : Finset (Fin n),
            n ≤ A.card + e ∧
            (∀ a, OnRS x k (fun j => u₀ a j + z * u₁ a j) A) ∧
            ¬ ((∀ a, OnRS x k (u₀ a) A) ∧ ∀ a, OnRS x k (u₁ a) A)) : ℝ) ≤ bchksBound n k e

namespace Spec

def bchks46_of_rows : Prop := BCHKS46Rows → BCHKS46

/-- Rows cost nothing for Reed-Solomon codes: `BCHKS46` gives `BCHKS46Rows`. -/
def rows_cost_nothing : Prop := BCHKS46 → BCHKS46Rows

/-- Mutual correlated agreement (`Code.Enc.MCAat` with the count rounded down) of `Code.RS.code`
(dimension k + 1 with 0 < k, distinct points in F, tables over E) at a radius e > 0 below the
Johnson radius, from `BCHKS46Rows`. -/
def rs_mcaAt_of_rows : Prop :=
  BCHKS46Rows →
  ∀ (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E]
      (n k msg r e₀ mca₀ : ℕ) (x : Fin n → F),
    Function.Injective x →
    ∀ e : ℕ, 0 < k → 0 < e → n * k < (n - e) ^ 2 →
      ∀ (R : Type) [Finite R],
        (Code.RS.code x (k + 1) msg r e₀ mca₀).MCAat E R e ⌊bchksBound n k e⌋₊

/-- What `rs_prox_of_rows` and `rs_prox` below conclude, for distinct points and 0 < k: list and
agreement as functions of the radius, for all radii e > 0 below the Johnson radius.

Not proved outright in this library: proved only from the statement on codes `Cb.BCHKS46` or its
equivalent form with rows, neither of which this file proves.

-/
def RsProx : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E]
      (n k msg r e₀ mca₀ : ℕ) (x : Fin n → F),
    Function.Injective x → 0 < k →
    (Code.RS.code x (k + 1) msg r e₀ mca₀).Prox E (fun e => 0 < e ∧ n * k < (n - e) ^ 2)
      (fun e _ => listMax n (n - k) e) (fun e _ => ⌊bchksBound n k e⌋₊)

/-- What `rs_listProps_of_rows` and `rs_listProps` below conclude: the record `Code.Enc.ListProps`
of Cb/Gen/CodeList.lean for a Reed-Solomon code with distinct non-zero points, msg + r ≤ k + 1 and
0 < k, at a radius e > 0 below the Johnson radius.

Not proved outright in this library: proved only from the statement on codes `Cb.BCHKS46` or its
equivalent form with rows, neither of which this file proves.

-/
def RsListProps : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Finite E] [Algebra F E]
      (n k msg r e : ℕ) (x : Fin n → F),
    Function.Injective x → (∀ j, x j ≠ 0) → msg + r ≤ k + 1 → 0 < k → 0 < e → n * k < (n - e) ^ 2 →
    (Code.RS.code x (k + 1) msg r e ⌊bchksBound n k e⌋₊).ListProps E (listMax n (n - k) e)

def rs_prox_of_rows : Prop := BCHKS46Rows → RsProx
def rs_listProps_of_rows : Prop := BCHKS46Rows → RsListProps

/-- In the end: of the two named propositions one is left as a hypothesis, the statement on codes.
(not all hypotheses are named here: see `RsProx`, `RsListProps`) -/
def rs_prox : Prop := BCHKS46 → RsProx
def rs_listProps : Prop := BCHKS46 → RsListProps

end Spec
end Cb
