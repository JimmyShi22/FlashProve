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
SO READ THE LEAN TEXT, NOT THE WORDS BELOW, TO SEE
WHAT IS A HYPOTHESIS HERE: neither "the statement on codes" nor "the fact on agreement" in these
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
Cb/Gen/CodeListRS.lean.) Cb/Gen/CodeListRSAt.lean: the statement on codes (`Cb.BCHKS46At`), on
agreement of Reed-Solomon codes, cut down to one field: over E alone, points in the base field F.
The three statements on codes of Cb/Gen/CodeListRSF.lean, at this E, follow from this form already,
because the count for tables is the count for two words ("rows cost nothing"), and this is proved
without an extension field.

Definitions and statements (the latter in `Cb.Spec`); the proofs are in
Cb/Gen/CodeListRSAtProofs.lean.
Cb/Gen/CodeListRSF.lean has `BCHKS46F F`: mutual correlated agreement of Reed-Solomon codes below
the Johnson radius, for two words, for every finite field K that is an algebra over F, points in F.
In that file's proofs the other fields K are used in one step only: a table of rows is packed into
one word over an extension. Cb/Ld/LdRelRowsEAbs.lean states a lemma of linear algebra over E itself
that takes that step's place (`Spec.rows_free_abs`).

Main names:
  `BCHKS46At F E`: the body of `BCHKS46F F` at K := E, word for word. It runs over all lengths n,
    degree bounds k > 0, radii e > 0 with n k < (n - e)^2, distinct points x in F (read in E), two
    words over E; the same event; the same count (`Cb.bchksBound n k e`). For these (u₀, u₁: the two
    words) it says: the number of exceptional z in E is at most the count. Here z is exceptional if
    there is a set A of at least n - e positions on which u₀ + z u₁ agrees with a polynomial of
    degree at most k (`OnRS`, Cb/Gen/CodeListRS.lean), while u₀ and u₁ do not both agree on A with
    such polynomials.
    By reading, this is the technical report's own restatement of the assumed theorem: over E
    alone, points in the base field. ON THE LETTER: the report's radius is a real number; here
    it is e / n with e ≥ 1: the report's other radii follow (the event depends on the integer
    part alone, the count is monotone), and at e = 0 nothing needs assuming: so this form asks a
    shade less and loses nothing
  `Spec.bchks46At_of_F`: BCHKS46F F → BCHKS46At F E. The form at one field is the weaker
    hypothesis: whatever follows from it follows from `BCHKS46F F`, and so from `BCHKS46`.
  `Spec.rows_cost_nothingAt`: BCHKS46At F E → BCHKS46RowsAt F E. No extension field.
  `Spec.rsAt_mca`, `Spec.rsAt_prox`, `Spec.rsAt_group_prox`: the statements `rs_mcaAtF`,
    `rs_proxF`, `rs_group_proxF` of Cb/Gen/CodeListRSF.lean, at this E, from BCHKS46At F E.

Limits:
Not proved here, no axiom: BCHKS46At F E stands as a hypothesis in the Lean text of each statement
that uses it, or in a `variable` line before it. It is a case of the theorem named above, whose
source gives an outline of a proof. (The source of the statement on codes: the head of
Cb/Gen/CodeListRS.lean.)
This file does not say whether the statement holds, or whether its source proves it.
`BCHKS46At F E` still speaks of all lengths, degree bounds and radii over E: one false instance
would empty what rests on it. This file does not say that the count is small against the field.
Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
/- Limits: `BCHKS46At` is a statement on codes: a definition of a proposition. This library proves
it in Cb/Bridge (bchks46At), from files adapted from ArkLib and Mathlib
(ThirdParty/; lean/LIMITS.md, L15); the theorems
that take it keep it as a hypothesis. Nothing in this library checks that it says what its source
shows. -/
import Cb.Gen.CodeListRSF
import Cb.Ld.LdRelRowsEAbs

set_option autoImplicit false

namespace Cb
open Prob Blocks Polynomial

/-- **The statement on codes (`BCHKS46At`), over E alone, points in F** (not proved here (Cb/Bridge/
proves it); not an axiom). -/
def BCHKS46At (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E] : Prop :=
  ∀ (n k e : ℕ) (x : Fin n → F), Function.Injective x → 0 < k → 0 < e → n * k < (n - e) ^ 2 →
    ∀ u₀ u₁ : Fin n → E,
      (cnt (fun z : E => ∃ A : Finset (Fin n), n ≤ A.card + e ∧
        OnRS (fun j => algebraMap F E (x j)) k (fun j => u₀ j + z * u₁ j) A ∧ ¬ (OnRS (fun j => algebraMap F E (x j)) k u₀ A ∧ OnRS (fun j => algebraMap F E (x j)) k u₁ A)) : ℝ) ≤ bchksBound n k e

/-- The same for tables. -/
def BCHKS46RowsAt (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E] : Prop :=
  ∀ (n k e : ℕ) (x : Fin n → F), Function.Injective x → 0 < k → 0 < e → n * k < (n - e) ^ 2 →
    ∀ (R : Type) [Finite R] (u₀ u₁ : R → Fin n → E),
      (cnt (fun z : E =>
          ∃ A : Finset (Fin n),
            n ≤ A.card + e ∧
            (∀ a, OnRS (fun j => algebraMap F E (x j)) k (fun j => u₀ a j + z * u₁ a j) A) ∧
            ¬ ((∀ a, OnRS (fun j => algebraMap F E (x j)) k (u₀ a) A) ∧
              ∀ a, OnRS (fun j => algebraMap F E (x j)) k (u₁ a) A)) : ℝ) ≤ bchksBound n k e

namespace Spec
section
variable (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E]

/-- The form at one field is the weaker hypothesis. -/
def bchks46At_of_F : Prop := BCHKS46F F → BCHKS46At F E

/-- Rows cost nothing: no extension field: `BCHKS46At F E` gives `BCHKS46RowsAt F E`. -/
def rows_cost_nothingAt : Prop := BCHKS46At F E → BCHKS46RowsAt F E

def rsAt_mca : Prop :=
  BCHKS46At F E → ∀ (n k msg r e₀ mca₀ : ℕ) (x : Fin n → F), Function.Injective x →
    ∀ e : ℕ, 0 < k → 0 < e → n * k < (n - e) ^ 2 → ∀ (R : Type) [Finite R],
      (Code.RS.code x (k + 1) msg r e₀ mca₀).MCAat E R e ⌊bchksBound n k e⌋₊

/-- From `BCHKS46At F E`, for distinct points and 0 < k, for the Reed-Solomon code of dimension
k + 1 on these points: bounds on list and agreement (`Code.Enc.Prox`, Cb/Gen/CodeList.lean) as
functions of the radius, for all radii e > 0 below the Johnson radius. -/
def rsAt_prox : Prop :=
  BCHKS46At F E →
  ∀ (n k msg r e₀ mca₀ : ℕ) (x : Fin n → F), Function.Injective x → 0 < k →
    (Code.RS.code x (k + 1) msg r e₀ mca₀).Prox E (fun e => 0 < e ∧ n * k < (n - e) ^ 2)
      (fun e _ => listMax n (n - k) e) (fun e _ => ⌊bchksBound n k e⌋₊)

/-- Families under an even reading (`Reading.Even`, Cb/Gen/CodeRep.lean): `Reading.Prox` (the same
file), from `BCHKS46At F E`, at the radii that the statement names. (not all hypotheses are named
here: see the statement below) -/
def rsAt_group_prox : Prop :=
  BCHKS46At F E →
  ∀ (A : Type) [Fintype A] (n k msg r : A → ℕ) (x : ∀ a, Fin (n a) → F),
    (∀ a, Function.Injective (x a)) → (∀ a, 0 < k a) → (∀ a, k a < n a) →
    ∀ T : Reading (fun a => Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0), T.Even →
      ∀ D : ℕ, (∀ a, D ≤ T.mult a * (n a - k a)) →
        ∀ (R : A → Type) [∀ a, Finite (R a)], T.Prox E R
          (fun e => InJohnson (Fintype.card T.P) D e ∧ ∀ a, T.mult a ≤ e)
          (fun e => listMax (Fintype.card T.P) D e)
          (fun e => ∑ a, ⌊bchksBound (n a) (k a) (e / T.mult a)⌋₊)

end
end Spec
end Cb
