-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`IsGlCpJ` (Cb/Gl/GlCopy.lean) does not ask a radius within half the distance.
Cb/Gl/GlCopyJ.lean: agreement of copied rows below the Johnson radius, whatever the number of rows,
with the long codes' counts plus one list, from agreement of the families of plain Reed-Solomon
codes, taken as a premise.

Statements and proofs. Nothing from the literature is named in this file. The count `Cb.bchksBound`
(Cb/Gen/CodeListRS.lean) stands in `Spec.glCpJ_one`.
For a ≤ b ≤ 32 a copied code is a short plain Reed-Solomon code whose codewords are written out
2^(b - a) times as one long word (`rsCp a b k msg r`, Cb/Gl/GlCopy.lean). Agreement is mutual
correlated agreement on lines (`LdCode.MCAat e bad`, Cb/Ld/LdRel.lean). Whatever the number of rows:
the same of `C.il R` for every finite R (`LdCode.MCArows`, Cb/Ld/LdRelRows.lean). Below the Johnson
radius is `InJohnson`, and `listMax` is the bound on the list there (Cb/Gen/JohnsonList.lean).
The statement on codes (Cb/Gen/CodeListRS.lean; its two forms: Cb/Gen/CodeListRSF.lean and
Cb/Gen/CodeListRSAt.lean) asserts such agreement of two words for the Reed-Solomon code of degree
at most k > 0 on n distinct points, at every radius e > 0 with n k < (n - e)^2, with the count
`Cb.bchksBound n k e`.
(The source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.)

Main names:
  `Spec.glCp_rows_of`: if every family of plain Reed-Solomon codes whose message and randomness fill
    the dimension (`IsGlJ`, Cb/Gl/GlLdJ.lean) has agreement of rows below the Johnson radius with
    its count (what `Cb.Gl.glJ_rows0` and `Cb.Gl.glAt_rows0` prove under the statement on codes in
    its two forms), then so has every family of copied codes (`IsGlCpJ`, Cb/Gl/GlCopy.lean).
  `Spec.glCpJ_one`: the predicate `IsGlCpJ` is not empty: for a ≤ b ≤ 32, 0 < k < 2^a,
    msg + r ≤ k + 1: one copied code read as it stands (`Reading.one`, Cb/Gen/CodeRep.lean), any
    rows, any radius e ≥ 1.

Why: the way, which, by reading, is the write-up's: the copied family is a subcode of the
family of the long codes (`Cb.Gl.glCp_sub`); a subcode has at most the whole code's count plus the
list of two rows of the whole code (`Cb.ld_sub_rows`, under its hypotheses); below the Johnson
radius that list is at most listMax |P| d e, whatever the rows.
A little better than the write-up's route, by reading: for a family of several copied codes
one
`listMax` is added for the whole family (the lemma on subcodes at the complex of the long codes),
where the write-up's route (each code, then complexes) adds one list for each member.
Why a premise and no named hypothesis: this file is imported by the proofs on the closure `GlJ`
(`glJ_rows`, Cb/Gl/GlLdJProofs.lean; `glAt_rows`, Cb/Gl/GlLdJAt.lean), which use it for the
constructor `copy`, each under its own form of the statement on codes.

Notation:
  `p`, `F`: the prime, and the integers modulo it (Cb/Gl/GlField.lean);
  `E`: the challenge field (Cb/Gl/GlField.lean);
  `C`: a code read under a transformation (`LdCode E P`, Cb/Ld/LdRel.lean); `P`: its long positions;
  `d`, `t`, `e`, `bad`: numbers, the arguments of `IsGlJ C d t e bad` (Cb/Gl/GlLdJ.lean) and
    `IsGlCpJ C d t e bad` (Cb/Gl/GlCopy.lean); d and e stand as distance and radius in
    `InJohnson n d e`, bad as the count in `C.MCArows e bad`;
  `InJohnson n d e` (n positions): n * (n - d) < (n - e) ^ 2 (Cb/Gen/JohnsonList.lean);
  `listMax n d e`: n * (d - e) / ((n - e) ^ 2 - n * (n - d)), rounded down
    (Cb/Gen/JohnsonList.lean).

Limits: this file does not say that the term `listMax` is needed, or that the counts are small: the
long code's count is the assumed statement's at the long length: by reading, the write-up
puts the price at up to 9 bits.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gl.GlLdJ
import Cb.Gl.GlCopyProofs
import Cb.Ld.LdRelRowsProofs
import Cb.Ld.LdRelJohnsonProofs

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks

namespace Spec

/-- Agreement of copied rows, from agreement of the families of plain codes. -/
def glCp_rows_of : Prop :=
  (∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ),
    IsGlJ C d t e bad → InJohnson (Fintype.card P) d e → C.MCArows e bad) →
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ),
    IsGlCpJ C d t e bad → InJohnson (Fintype.card P) d e → C.MCArows e bad

/-- One copied code, read as it stands. -/
def glCpJ_one : Prop :=
  ∀ (a b k msg r e : ℕ) (R : Type) [Fintype R] [DecidableEq R], a ≤ b → b ≤ 32 → 0 < k → k < 2 ^ a →
    msg + r ≤ k + 1 → 1 ≤ e →
    IsGlCpJ ((Reading.one (rsCp a b k msg r)).ld E fun _ => R) (2 ^ b - 2 ^ (b - a) * k) r e
      (⌊Cb.bchksBound (2 ^ b) (2 ^ (b - a) * k) e⌋₊ +
        listMax (Fintype.card (Fin (2 ^ b))) (2 ^ b - 2 ^ (b - a) * k) e)

end Spec

theorem cp_john_lt {n d e : ℕ} (h : InJohnson n d e) : e < d := by
  by_contra hn
  have h1 : n - e ≤ n - d := Nat.sub_le_sub_left (Nat.le_of_not_lt hn) n
  have h2 : (n - e) ^ 2 ≤ n * (n - d) := by
    rw [pow_two]
    exact Nat.mul_le_mul (Nat.sub_le n e) h1
  exact absurd h (not_lt.2 h2)

theorem glCp_rows_of : Spec.glCp_rows_of := by
  intro h0 P _ C d t e bad h hJ
  obtain ⟨A, iA, dA, a, b, k, msg, r, pos, mult, R, fR, dR, rfl, hab, hb, hk0, hk,
      hp, hE, hd, ht, hm, hbd⟩ := h
  have hW : IsGlJ
      ((⟨P, pos, mult⟩ : Reading
          (grp b (fun i => 2 ^ (b i - a i) * k i)
            (fun i => 2 ^ (b i - a i) * k i + 1) fun _ => 0)).ld
        E R)
      d 0 e (∑ i, ⌊Cb.bchksBound (2 ^ b i) (2 ^ (b i - a i) * k i) (e / mult i)⌋₊) :=
    ⟨A, iA, dA, b, fun i => 2 ^ (b i - a i) * k i, fun i => 2 ^ (b i - a i) * k i + 1, fun _ => 0,
      pos, mult, R, fR, dR, rfl, hb, fun i => Nat.mul_pos (pow_pos (by norm_num) _) (hk0 i),
      fun i => cp_lt (hab i) (hk i), fun _ => rfl, hE, hd, fun _ => le_rfl, hm, le_rfl⟩
  have gW := glC_code P _ d 0
    (.base ⟨A, iA, dA, b, fun i => 2 ^ (b i - a i) * k i, fun i => 2 ^ (b i - a i) * k i + 1,
        fun _ => 0, pos, mult, R, fR, dR, rfl, hb, fun i => cp_lt (hab i) (hk i), fun _ => le_rfl,
        hE, hd, fun _ => le_rfl⟩)
  have gS := glCp_code P _ d t
    ⟨A, iA, dA, a, b, k, msg, r, pos, mult, R, fR, dR, rfl, hab, hb, hk, hp, hE, hd, ht⟩
  exact ld_rows_mono E P _ _ _ _ hbd
    (ld_sub_rows E P _ _ _ d e _ _ (glCp_sub A a b k msg r P pos mult R) gW.1 gS.1 gW.2.2.2.1
      (cp_john_lt hJ) (h0 P _ d 0 e _ hW hJ) fun R' _ _ =>
        ld_list_johnson E P _ d e (ld_laws_il E P _ Bool (ld_laws_il E P _ R' gW.1))
          (ld_dist_il E P _ Bool d (ld_dist_il E P _ R' d gW.2.2.2.1)) hJ)

theorem glCpJ_one : Spec.glCpJ_one := fun a b k msg r e R fR dR hab hb hk0 hk hp he  =>
  ⟨Unit, inferInstance, inferInstance, fun _ => a, fun _ => b, fun _ => k, fun _ => msg, fun _ => r,
    fun _ x => x, fun _ => 1, fun _ => R, fun _ => fR, fun _ => dR, rfl, fun _ => hab, fun _ => hb,
    fun _ => hk0, fun _ => hk, fun _ => hp,
    one_even F (rsCp a b k msg r),
    fun _ => by rw [Nat.one_mul], fun _ => le_rfl, fun _ => he,  by
      simp only [Finset.univ_unique, Finset.sum_singleton, Nat.div_one]
      exact le_rfl⟩

end Cb.Gl
