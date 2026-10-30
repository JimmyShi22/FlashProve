-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3Base.lean: a small Reed-Solomon code with proved bounds on
list decoding and on mutual correlated agreement at the radius 3, not within half of its distance 5,
as a test instance.


The toys' code of eight points, dimension 4, distance 5, read
at the radius 3: not within half of its distance, below its Johnson radius; there the count of the
statement on codes for agreement is a true count, with nothing assumed.

Definitions, one statement (`Cb.GlJ3.Spec.gl_j3_base`) and proofs. A guard against empty theorems;
no parameter of a protocol.
The code is `C84` of Cb/GlVal/GlToyBase4.lean (the subgroup of order 8; polynomials of degree at
most 3; one message symbol and three symbols of randomness, which fill the dimension 4; distance 5;
it hides 3 positions), with any rows R, read as it stands over E: `toyLd84 R`. Conventions of the
toys of the namespace `Cb.GlJ3`, said of the toys' own oracle messages and groups,
not of what a statement takes as a parameter: every online oracle message, and the group of a
closing where a file has one, is read at the radius 3: not within half of the distance, below the
Johnson radius; every bound on lists is `LJ3` = listMax 8 5 3, the proved Johnson bound; every count
for agreement is `bJ3`, the count of the statement on codes at (8, 3, 3), which at this size is a
true count for every code with the laws, without the statement on codes, by a count of sets of
positions ("Why it is a true count" below: read it before quoting); the pad's coefficient of a
sample is drawn among all values other than 0. This is not said of the offline side (configuration,
index, lookup tables, weights-formedness).

Main names: `eJ3`: the radius: 3. 3 · 3 is
    not below 5, nor is 2 · 3; 8 · 3 = 24 < 25 = (8 - 3)^2: below the Johnson radius (`inJ3`), and
    the condition of the statement on codes on (length, degree, radius) = (8, 3, 3).
  `bJ3`: the count of the statement on codes at (8, 3, 3), rounded down (`bchksBound`,
    Cb/Gen/CodeListRS.lean). Not evaluated here; at least 93 (`le_bJ3`).
  `mcaJ3`, `rowsJ3`: every code at the eight positions with the laws has at most `bJ3` exceptional
    values at the radius 3, as it stands (`MCAat`) and whatever the number of further rows
    (`MCArows`, Cb/Ld/LdRelRows.lean): proved, nothing assumed.
  `glJ3 R`: `GlJ (toyLd84 R) 5 3 3 bJ3` (Cb/Gl/GlLdJ.lean): what the records over this field ask of
    a code, at the count of the statement on codes.
  `Spec.gl_j3_base`: all of these and `listJ3` together, but for `le_bJ3`.

Why it is a true count with nothing assumed (by a reading). Every code with the laws has at most one
exceptional value on a line for each set of long positions that omits at most e of them
(`ld_mca_sets`, Cb/Ld/LdRelAny.lean; generic, proved). At eight positions and e = 3 there are 1 + 8
+ 28 + 56 = 93 such sets (`cnt_setsJ3`), and the count of the statement on codes is at least that
(`le_bJ3`).
Why this matters. (This is said of a toy request and of a guard's object; the files of both are not
in this library, which builds no value of `GPack`: `GPack.ofJohn`, Cb/Ld/LdGroupJohnPack.lean, is
applied nowhere.) The toy request's term is built through a bundle that carries data and facts,
agreement among the facts (`GPack`, Cb/Ld/LdGroupPack.lean). With a count that is true with nothing
assumed, the guard's object is one fixed term that depends on no proof of the statement on codes
(`BCHKS46F F`, Cb/Gen/CodeListRSF.lean).

Limits:
What this is worth, in plain words. It lets a guard show that the other hypotheses of a theorem
under the statement on codes can be met together at a radius beyond a third, with the counts that
that theorem's records ask. It says nothing for the statement on codes: at this size agreement holds
by a count of sets, so the guard does not reach a place where the statement on codes is needed.
What these toys do not show: a value of `GlJ` (Cb/Gl/GlLdJ.lean) at a radius other than 3. `GlJ`
does not ask a radius within half the distance.
This file does not say the value of `bJ3`, or that it is below the number of elements of E. It says
nothing on real parameters.
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyBase4
import Cb.Gl.GlLdJProofs
import Cb.Ld.LdRelJohnsonProofs
import Cb.Ld.LdRelAny
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Code Prob Blocks Iop Hiop Cb.Gl

/-- The radius. -/
abbrev eJ3 : ℕ := 3

/-- The bound on lists: the Johnson bound at eight positions, distance 5, radius 3. -/
abbrev LJ3 : ℕ := listMax (Fintype.card P84) 5 eJ3

/-- The count of the statement on codes at length 8, degree 3, radius 3, rounded down. -/
def bJ3 : ℕ := ⌊Cb.bchksBound (2 ^ 3) 3 3⌋₊

namespace Spec

def gl_j3_base : Prop :=
  ¬ 3 * eJ3 < 5 ∧ ¬ 2 * eJ3 < 5 ∧ eJ3 < 5 ∧
    InJohnson (Fintype.card P84) 5 eJ3 ∧ bJ3 = ⌊Cb.bchksBound (2 ^ 3) 3 3⌋₊ ∧
  (∀ D : LdCode E P84, D.Laws → D.MCAat eJ3 bJ3 ∧ D.MCArows eJ3 bJ3) ∧
  (∀ (R : Type) [Fintype R] [DecidableEq R], GlJ (toyLd84 R) 5 3 eJ3 bJ3) ∧
  ∀ D : LdCode E P84, D.Laws → D.Dist 5 → D.ListAt eJ3 LJ3

end Spec

theorem inJ3 : InJohnson (Fintype.card P84) 5 eJ3 := by
  rw [card84]
  show 8 * (8 - 5) < (8 - 3) ^ 2
  norm_num

/-- The sets of eight positions that omit at most three: there are 93. -/
theorem cnt_setsJ3 : cnt (fun S : Finset (Fin 8) => Fintype.card (Fin 8) ≤ S.card + 3) = 93 := by
  rw [cnt_eq_card_filter]
  decide

/-- A crude bound from below for the form of the count of the statement on codes. -/
theorem count_geJ3 (M s n g r : ℝ) (hM : 3 ≤ M) (hs0 : 0 < s) (hs1 : s ≤ 1) (hr0 : 0 < r)
    (hr1 : r ≤ 1) (hn : 1 ≤ n) (hg : 0 ≤ g) :
    ((93 : ℕ) : ℝ) ≤
      (2 * (M + 1 / 2) ^ 5 + 3 * (M + 1 / 2) * g * r) / (3 * (r * s)) * n + (M + 1 / 2) / s := by
  have e93 : ((93 : ℕ) : ℝ) = 93 := by norm_num
  rw [e93]
  have hA : (7 / 2 : ℝ) ≤ M + 1 / 2 := by linarith
  have hA0 : 0 ≤ M + 1 / 2 := by linarith
  have h5 : (7 / 2 : ℝ) ^ 5 ≤ (M + 1 / 2) ^ 5 := pow_le_pow_left₀ (by norm_num) hA 5
  have h7 : (7 / 2 : ℝ) ^ 5 = 16807 / 32 := by norm_num
  have hrs0 : 0 < r * s := mul_pos hr0 hs0
  have hrs1 : r * s ≤ 1 := mul_le_one₀ hr1 hs0.le hs1
  have hD0 : 0 < 3 * (r * s) := by linarith
  have hx : 0 ≤ 3 * (M + 1 / 2) * g * r :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0) hg) hr0.le
  have hq : (93 : ℝ) ≤ (2 * (M + 1 / 2) ^ 5 + 3 * (M + 1 / 2) * g * r) / (3 * (r * s)) := by
    rw [le_div_iff₀ hD0]
    linarith
  have h1 : (93 : ℝ) ≤ (2 * (M + 1 / 2) ^ 5 + 3 * (M + 1 / 2) * g * r) / (3 * (r * s)) * n :=
    le_trans hq (le_mul_of_one_le_right (le_trans (by norm_num) hq) hn)
  have h2 : 0 ≤ (M + 1 / 2) / s := div_nonneg hA0 hs0.le
  linarith

/-- The count of the statement on codes is at least the number of these sets: it is at least 93. -/
theorem le_bJ3 : 93 ≤ bJ3 := by
  refine Nat.le_floor ?_
  unfold Cb.bchksBound
  exact count_geJ3 _ _ _ _ _ (le_max_right _ _) (Real.sqrt_pos.2 (by norm_num))
    (Real.sqrt_le_one.2 (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by positivity)

/-- Every code at the eight positions with the laws: agreement at the radius 3, at the count of the
statement on codes: nothing assumed. -/
theorem mcaJ3 (D : LdCode E P84) (hL : D.Laws) : D.MCAat eJ3 bJ3 :=
  ld_mca_mono E _ _ eJ3 _ bJ3 (le_trans (le_of_eq cnt_setsJ3) le_bJ3)
    (ld_mca_sets E P84 D hL eJ3)

theorem rowsJ3 (D : LdCode E P84) (hL : D.Laws) : D.MCArows eJ3 bJ3 := fun R _ _ =>
  mcaJ3 (D.il R) (ld_laws_il E P84 D R hL)

/-- The toys' code with rows R is of the closure of Cb/Gl/GlLdJ.lean, at the count of the statement
on codes. -/
theorem glJ3 (R : Type) [Fintype R] [DecidableEq R] : GlJ (toyLd84 R) 5 3 eJ3 bJ3 :=
  .base (glJ_one 3 3 1 3 3 R  (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num))
theorem glJ30 (R : Type) [Fintype R] [DecidableEq R] : GlJ (toyLd84 R) 5 0 eJ3 bJ3 :=
  glJ_mono P84 _ 5 3 eJ3 bJ3 0 (glJ3 R) (Nat.zero_le _)
theorem glJ31 (R : Type) [Fintype R] [DecidableEq R] : GlJ (toyLd84 R) 5 1 eJ3 bJ3 :=
  glJ_mono P84 _ 5 3 eJ3 bJ3 1 (glJ3 R) (by norm_num)

/-- Every code at the eight positions with the laws and the distance 5: lists by the Johnson
bound. -/
theorem listJ3 (D : LdCode E P84) (hL : D.Laws) (hD : D.Dist 5) : D.ListAt eJ3 LJ3 :=
  ld_list_johnson E P84 D 5 eJ3 hL hD inJ3

theorem gl_j3_base : Spec.gl_j3_base :=
  ⟨by decide, by decide, by decide, inJ3, rfl, fun D hL => ⟨mcaJ3 D hL, rowsJ3 D hL⟩,
    fun R _ _ => glJ3 R, listJ3⟩

end Cb.GlJ3
