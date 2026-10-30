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
Cb/Gen/CodeListRS.lean.) Cb/Ld/LdRelRowsEAbs.lean: rows cost nothing, in its bare form: linear
algebra over a finite field;
no code, no extension field.

`Spec.rows_free_abs` is the core of a reduction for mutual correlated agreement, from tables of
interleaved rows to two words: "rows cost nothing", that is, where the lemma is applied, the count
of exceptional values for tables of rows is no more than the count for two words.
Two statements (`Cb.Spec.rows_avoid`, `Cb.Spec.rows_free_abs`); the proofs are in
Cb/Ld/LdRelRowsEAbsProofs.lean. Nothing assumed beyond the hypotheses of the statements and whatever
the arguments hold as proofs.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: mutual correlated agreement on lines is asked of tables of rows under one code.
The library has "the count for tables is the count for two words" for Reed-Solomon codes, by
packing a table of r rows into one word over an extension field of degree r
(Cb/Gen/CodeListRows.lean, Cb/Gen/CodeListRSF.lean): for that step alone the statement on codes
(`Cb.BCHKS46F`, Cb/Gen/CodeListRSF.lean) speaks of all finite extensions.
A write-up of ours (lean/CREDITS.md) has the step by a lemma on every linear code, which
needs no extension. Here is that lemma's core, restated in our own words: the lemma, and the family
of subspaces in its proof, follow that report (lean/CREDITS.md), which sets the lemma beside (Jo26),
of whose announced statement it is a case.

Main names:
  `Spec.rows_avoid`: E a finite field, R a finite set. For at most |E| proper subspaces V θ of E^R
    (one for each θ in a set B of elements of E) there is a vector w in none of them. The count: a
    proper subspace has at most |E|^(|R| - 1) elements, and all subspaces share 0. Without that the
    union bound gives |E| · |E|^(|R| - 1) = |E|^|R|, which is not enough when B is all of E. (How it
    serves `Spec.rows_free_abs`: the head of Cb/Ld/LdRelRowsEAbsProofs.lean.)
  `Spec.rows_free_abs`: M a vector space over E ("long words"); 𝒮 any type ("sets of positions"), ok
    a property of its members ("large"); W S a subspace of M for each S ("agrees on S with a
    codeword"); g₀, g₁ : R → M two tables. There is one vector w of coefficients such that every θ
    that is exceptional for the tables (for some large S all rows of g₀ + θ g₁ lie in W S, but not
    all rows of g₀ and g₁ do) is exceptional for the two words ∑ w i • g₀ i, ∑ w i • g₁ i, with a
    large S again: each side has its own `∃ S`, so the statement does not say that it is the same
    set (the proof fixes one set for each θ).

Limits: this file says nothing on any code, radius, distance or count. These come in where the lemma
is applied (Cb/Gen/CodeListRSAtProofs.lean: Reed-Solomon codes). It says nothing on infinite fields.
There the statement is easier for a finite 𝒮 and not needed.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
"The report": this protocol's technical report (lean/CREDITS.md).
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness

set_option autoImplicit false

namespace Cb
namespace Spec

/-- States: at most |E| proper subspaces of E^R do not cover E^R. -/
def rows_avoid : Prop :=
  ∀ (E R : Type) [Field E] [Fintype E] [Fintype R] (B : Finset E) (V : E → Submodule E (R → E)),
    (∀ θ ∈ B, V θ ≠ ⊤) → ∃ w : R → E, ∀ θ ∈ B, w ∉ V θ

/-- Rows cost nothing. States: there is one vector w of coefficients such that every θ that is
exceptional for the tables g₀, g₁ is exceptional for the two words ∑ w i • g₀ i, ∑ w i • g₁ i. -/
def rows_free_abs : Prop :=
  ∀ (E R M 𝒮 : Type) [Field E] [Finite E] [Fintype R] [AddCommGroup M] [Module E M] (ok : 𝒮 → Prop)
      (W : 𝒮 → Submodule E M) (g₀ g₁ : R → M),
    ∃ w : R → E, ∀ θ : E,
      (∃ S, ok S ∧ (∀ i, g₀ i + θ • g₁ i ∈ W S) ∧ ¬ ((∀ i, g₀ i ∈ W S) ∧ ∀ i, g₁ i ∈ W S)) →
      ∃ S,
        ok S ∧ (∑ i, w i • g₀ i) + θ • (∑ i, w i • g₁ i) ∈ W S ∧
        ¬ ((∑ i, w i • g₀ i) ∈ W S ∧ (∑ i, w i • g₁ i) ∈ W S)

end Spec
end Cb
