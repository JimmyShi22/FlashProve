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
Cb/Gen/CodeListRS.lean.) Cb/Ld/LdFoldEqCode.lean: the encoded index under a code with encoder: the
abstract numbers of Cb/Ld/LdFoldEq.lean (agreement error for the fold's coefficients, list size,
collisions of a record) from the code interface of Cb/Gen/CodeList.lean.

Definitions and statements (`Cb.Spec`); the proofs are in Cb/Ld/LdFoldEqCodeProofs.lean.
Here the generator is that of a code C₀ of Code/Iface.lean, read over E.
`Enc.Prox E ok L bad` (Cb/Gen/CodeList.lean) says that L bounds the list size and bad the count for
agreement, as functions of the radius and the number of rows, at the radii with ok; here it is a
premise. Below, "the distance" is `C₀.d`, and each statement that names it has the premise
`HasDist C₀.G C₀.d`.

Main names:
  `LdIx.ofEnc E C₀ hp pl v Z eM rank`: the index, X below: rows on the cube of v variables under
    `C₀.GE E`; full messages of length k; "pl" names the places of the message (pads included) among
    the first "msg" coordinates.
  1. Agreement (`X.MCAeq e' bad`, Cb/Ld/LdFoldEq.lean: every table has at most "bad" exceptional
    points γ, of the |E|^v).
    `Spec.ldFc_mcaFor_iff`: `Enc.MCAat` (Cb/Gen/CodeList.lean) is `Code.MCAFor` for the range of the
    generator.
    `Spec.ldFc_mca_prox`: from `Enc.Prox`, at a radius e' with ok: see its doc comment.
    `Spec.ldFc_mca_third`: nothing assumed beyond the hypotheses of its statement, for 3 e' below
    the distance:
    X.MCAeq e' (v (e' + 1) |E|^(v-1)).
    For distinct points x, 0 < k (full messages of length k + 1) and 0 < e':
    Spec.ldFc_mca_bchks: for a Reed-Solomon code below the Johnson radius, under the named
    hypothesis BCHKS46 (stated in the paper cited in the head of Cb/Gen/CodeListRS.lean, with an
    outline of a proof; that head says how far the source carries):
    X.MCAeq e' (v ⌊count of the theorem⌋ |E|^(v-1)).
  2. The list: a bound on the number of tables of full messages within e' columns of a table.
    `Spec.ldFc_list_prox` (from `Enc.Prox`, at a radius e' with ok: L at e' and the number of rows);
    `Spec.ldFc_list_johnson` (e' below the Johnson radius for the distance, `InJohnson`,
    Cb/Gen/JohnsonList.lean: `listMax C₀.n C₀.d e'`); `Spec.ldFc_list_unique` (2 e' below the
    distance: 1).
  3. Words over the small field. `Spec.ldFc_overF`. (Beyond unique decoding: for every member of the
    list.)
  4. Under the hypotheses of the statements, the record binds. `Spec.ldFc_binds`: for the index X,
    let the table have its symbols in F, eM below the distance, at most L tables of full messages
    within eM columns, and let the sample map of a row be a zero-evader on the vectors whose pad
    part lies in F (`Sample.OKOn (PadInF F)`). Then at most (L choose 2) err seeds have a collision,
    and twice that number is at most L² err.
    `Spec.ldFc_binds_pad`: under the hypotheses of its statement, for the row with a pad
    (`Sample.pad`, its set B of factors not empty) the property holds, so nothing is left to ask of
    the sample map but three injectivities.
  5. The bad points of the fold (`X.Bad f rec e'`, Cb/Ld/LdFoldEq.lean): their number, for e' ≤ eM,
    eM below the distance, and no collision at the record's seed (`X.Coll`, the same file: two
    tables of full messages within eM columns of f with different message parts and the same answers
    at the seed):
    `Spec.ldFc_cnt_third`: for 3 e' below the distance: at most v (e' + 1) |E|^(v-1) + v |E|^(v-1).
    `Spec.ldFc_cnt_johnson`: for e' below the Johnson radius for the distance and `X.MCAeq e' bad`,
    a premise: at most bad + `listMax C₀.n C₀.d e'` · v |E|^(v-1).

Notation: `Z`: a `Sample E J`: the sample map of one row; `eM`: a natural number: the radius of
decoding, in columns; `rank`: a function from tables of full messages to ℕ; `X.Rec`: a type: a
record: a seed, and the answers of every row (all four: `LdIx`, Cb/Ld/LdFoldEq.lean).

Limits: no proximity gap beyond a third of the distance is proved here or in
Cb/Ld/LdFoldEqCodeProofs.lean; BCHKS46 is a hypothesis in the
text of the one statement that uses it. A bound that reaches |E|^v, or the number of seeds, says
nothing. This file says nothing on hiding, on protocols. It says nothing on numerals.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdFoldEq
import Cb.Gen.CodeListRS

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

/-- The encoded index under a code with encoder, read over E. -/
def LdIx.ofEnc {F : Type} [Field F] (E : Type) [Field E] [Algebra F E] (C₀ : Code.Enc F)
    (hp : C₀.msg ≤ C₀.k) {J : Type} (pl : J → Fin C₀.msg) (v : ℕ) (Z : Sample E J) (eM : ℕ)
    (rank : ((Fin v → Bool) → Fin C₀.k → E) → ℕ) :
    LdIx E (Fin C₀.n) (Fin C₀.k) J :=
  ⟨v, C₀.GE E, fun j => Fin.castLE hp (pl j), Z, eM, rank⟩

namespace Spec
section
variable (F E : Type) [Field F] [Field E] [Fintype E] [Algebra F E]

def ldFc_mcaFor_iff : Prop :=
  ∀ (C₀ : Code.Enc F) (R : Type) [Finite R] (e bad : ℕ),
    C₀.MCAat E R e bad ↔ Code.MCAFor (LinearMap.range (C₀.GE E).mulVecLin) e R bad

/-- The agreement error for the fold's coefficients, from the code's functions of radius and rows,
at a radius with ok. (not all hypotheses are named here: see the statement below) -/
def ldFc_mca_prox : Prop :=
  ∀ (C₀ : Code.Enc F) (hp : C₀.msg ≤ C₀.k) (J : Type) [Fintype J] (pl : J → Fin C₀.msg) (v : ℕ)
      (Z : Sample E J) (eM : ℕ) (rank : ((Fin v → Bool) → Fin C₀.k → E) → ℕ) (ok : ℕ → Prop)
      (L bad : ℕ → ℕ → ℕ) (e' : ℕ),
    C₀.Prox E ok L bad → ok e' →
    (LdIx.ofEnc E C₀ hp pl v Z eM rank).MCAeq
      e' ((∑ j ∈ Finset.range v, bad e' (2 ^ j)) * Fintype.card E ^ (v - 1))

/-- Nothing assumed beyond the hypotheses below, up to a third of the distance.
(not all hypotheses are named here: see the statement below) -/
def ldFc_mca_third : Prop :=
  ∀ (C₀ : Code.Enc F) (hp : C₀.msg ≤ C₀.k) (J : Type) [Fintype J] (pl : J → Fin C₀.msg) (v : ℕ)
      (Z : Sample E J) (eM : ℕ) (rank : ((Fin v → Bool) → Fin C₀.k → E) → ℕ) (e' : ℕ),
    HasDist C₀.G C₀.d → 3 * e' < C₀.d →
    (LdIx.ofEnc E C₀ hp pl v Z eM rank).MCAeq e' (v * (e' + 1) * Fintype.card E ^ (v - 1))

/-- Reed-Solomon codes below the Johnson radius, under the statement on codes.
(not all hypotheses are named here: see the statement below) -/
def ldFc_mca_bchks : Prop :=
  BCHKS46 →
  ∀ (n k msg r e₀ mca₀ : ℕ) (x : Fin n → F), Function.Injective x → 0 < k →
    ∀ (hp : msg ≤ k + 1) (J : Type) [Fintype J] (pl : J → Fin msg) (v : ℕ) (Z : Sample E J) (eM : ℕ)
        (rank : ((Fin v → Bool) → Fin (k + 1) → E) → ℕ) (e' : ℕ),
      0 < e' → n * k < (n - e') ^ 2 →
      (LdIx.ofEnc E (Code.RS.code x (k + 1) msg r e₀ mca₀) hp pl v Z eM rank).MCAeq
        e' (v * ⌊bchksBound n k e'⌋₊ * Fintype.card E ^ (v - 1))

def ldFc_list_prox : Prop :=
  ∀ (C₀ : Code.Enc F) (ok : ℕ → Prop) (L bad : ℕ → ℕ → ℕ) (e' : ℕ), C₀.Prox E ok L bad → ok e' →
    ∀ (R : Type) [Finite R] (f : R → Fin C₀.n → E),
      ListLE (DecodesTo (C₀.GE E) e' f) (L e' (Nat.card R))

def ldFc_list_johnson : Prop :=
  ∀ (C₀ : Code.Enc F) (e' : ℕ), HasDist C₀.G C₀.d → InJohnson C₀.n C₀.d e' →
    ∀ (R : Type) (f : R → Fin C₀.n → E), ListLE (DecodesTo (C₀.GE E) e' f) (listMax C₀.n C₀.d e')

def ldFc_list_unique : Prop :=
  ∀ (C₀ : Code.Enc F) (e' : ℕ), HasDist C₀.G C₀.d → 2 * e' < C₀.d →
    ∀ (R : Type) (f : R → Fin C₀.n → E), ListLE (DecodesTo (C₀.GE E) e' f) 1

/-- For e below the distance, every member of the list of a table over F is over F. -/
def ldFc_overF : Prop :=
  ∀ (C₀ : Code.Enc F) (e : ℕ), HasDist C₀.G C₀.d → e < C₀.d →
    ∀ (R : Type) (f₀ : R → Fin C₀.n → F) (M : R → Fin C₀.k → E),
      DecodesTo (C₀.GE E) e (fun a => Code.liftWord E (f₀ a)) M →
      ∃ M₀ : R → Fin C₀.k → F, DecodesTo C₀.G e f₀ M₀ ∧ M = fun a => Code.liftWord E (M₀ a)

/-- Under the hypotheses of its statement, the record binds. -/
def ldFc_binds : Prop :=
  ∀ (C₀ : Code.Enc F) (hp : C₀.msg ≤ C₀.k) (J₀ P : Type) [Fintype J₀] [Fintype P]
      (pl : J₀ ⊕ P → Fin C₀.msg) (v : ℕ) (Z : Sample E (J₀ ⊕ P)) (eM : ℕ)
      (rank : ((Fin v → Bool) → Fin C₀.k → E) → ℕ) (L : ℕ) (f₀ : (Fin v → Bool) → Fin C₀.n → F),
    HasDist C₀.G C₀.d → eM < C₀.d → Z.OKOn (PadInF F) →
    ListLE (DecodesTo (C₀.GE E) eM fun a => Code.liftWord E (f₀ a)) L →
    cnt ((LdIx.ofEnc E C₀ hp pl v Z eM rank).Coll fun a => Code.liftWord E (f₀ a)) ≤
      L.choose 2 * Z.err ∧
    2 * cnt ((LdIx.ofEnc E C₀ hp pl v Z eM rank).Coll fun a => Code.liftWord E (f₀ a)) ≤
      L ^ 2 * Z.err

/-- The same for the row with a pad, under the hypotheses of its statement. -/
def ldFc_binds_pad : Prop :=
  ∀ (C₀ : Code.Enc F) (hp : C₀.msg ≤ C₀.k) (μ J₀ P B : Type) [Fintype μ] [DecidableEq μ]
      [Fintype B] [Nonempty B] [Fintype J₀] [Fintype P] (pl : J₀ ⊕ P → Fin C₀.msg) (v : ℕ)
      (plc : J₀ → μ → Bool) (w : P → E) (b : B → E) (eM : ℕ)
      (rank : ((Fin v → Bool) → Fin C₀.k → E) → ℕ) (L : ℕ) (f₀ : (Fin v → Bool) → Fin C₀.n → F),
    HasDist C₀.G C₀.d → eM < C₀.d → Function.Injective plc → Function.Injective b →
    Function.Injective (padVal (F := F) w) →
    ListLE (DecodesTo (C₀.GE E) eM fun a => Code.liftWord E (f₀ a)) L →
    cnt ((LdIx.ofEnc E C₀ hp pl v (Sample.pad E μ J₀ P B plc w b) eM rank).Coll fun a =>
          Code.liftWord E (f₀ a)) ≤
      L.choose 2 * (Sample.pad E μ J₀ P B plc w b).err ∧
    2 * cnt ((LdIx.ofEnc E C₀ hp pl v (Sample.pad E μ J₀ P B plc w b) eM rank).Coll
            fun a => Code.liftWord E (f₀ a)) ≤
      L ^ 2 * (Sample.pad E μ J₀ P B plc w b).err

/-- The bad points of the fold, nothing assumed beyond the hypotheses below: 3 e' below the
distance, e' ≤ eM below the distance, no collision at the record's seed.
(not all hypotheses are named here: see the statement below) -/
def ldFc_cnt_third : Prop :=
  ∀ (C₀ : Code.Enc F) (hp : C₀.msg ≤ C₀.k) (J : Type) [Fintype J] (pl : J → Fin C₀.msg) (v : ℕ)
      (Z : Sample E J) (eM : ℕ) (rank : ((Fin v → Bool) → Fin C₀.k → E) → ℕ) (e' : ℕ)
      (f : (Fin v → Bool) → Fin C₀.n → E) (rec : (LdIx.ofEnc E C₀ hp pl v Z eM rank).Rec),
    HasDist C₀.G C₀.d → eM < C₀.d → e' ≤ eM → 3 * e' < C₀.d →
    ¬ (LdIx.ofEnc E C₀ hp pl v Z eM rank).Coll f rec.1 →
    cnt ((LdIx.ofEnc E C₀ hp pl v Z eM rank).Bad f rec e') ≤
      v * (e' + 1) * Fintype.card E ^ (v - 1) + 1 * (v * Fintype.card E ^ (v - 1))

/-- The bad points of the fold below the Johnson radius: the list is proved, the agreement count is
a parameter; under the hypotheses of its statement. -/
def ldFc_cnt_johnson : Prop :=
  ∀ (C₀ : Code.Enc F) (hp : C₀.msg ≤ C₀.k) (J : Type) [Fintype J] (pl : J → Fin C₀.msg) (v : ℕ)
      (Z : Sample E J) (eM : ℕ) (rank : ((Fin v → Bool) → Fin C₀.k → E) → ℕ) (e' bad : ℕ)
      (f : (Fin v → Bool) → Fin C₀.n → E) (rec : (LdIx.ofEnc E C₀ hp pl v Z eM rank).Rec),
    HasDist C₀.G C₀.d → eM < C₀.d → e' ≤ eM → InJohnson C₀.n C₀.d e' →
    (LdIx.ofEnc E C₀ hp pl v Z eM rank).MCAeq e' bad →
    ¬ (LdIx.ofEnc E C₀ hp pl v Z eM rank).Coll f rec.1 →
    cnt ((LdIx.ofEnc E C₀ hp pl v Z eM rank).Bad f rec e') ≤
      bad + listMax C₀.n C₀.d e' * (v * Fintype.card E ^ (v - 1))

end
end Spec
end Cb
