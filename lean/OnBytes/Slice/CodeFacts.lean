-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CodeFacts.lean: the code of an entry file is a Reed-Solomon code of the library.

A code (a, l, r) of the format has 2^a positions. Its generator matrix `genOf` gives coefficient
number k of a word's polynomial the weight z^k at the position with the point z. The library has
Reed-Solomon codes at any family of points (Code/RS.lean). This file takes the library's code at the
format's points, shows that its generator matrix over the extension field is `genOf`, and carries
three facts of the library to every table format whose generator matrix is `genOf`.

Throughout, k = r + l is the number of coefficients and d = 2^a - k + 1. The conditions are a ≤ 32,
under which the 2^a points are different (OnBytes/Slice/Points.lean), and k ≤ 2^a.

Main definition: `rsCode`, the library's code at the format's points.
Main theorems.
 `genOf_eq_GE`    `genOf` is the generator matrix of `rsCode`, read over the extension field.
 `eq_ofEnc`       a table format with the generator matrix `genOf` is the library's table format
                  under `rsCode`. So what Cb/Ld/LdFoldEqCode.lean states of that table format under
                  any code can be used for it.
 `hasDist_genOf`  distance: the word of a polynomial other than 0 is not 0 at d positions or more.
 `mcaEq_third`    for 3 e < d, every table of 2^v rows has at most v (e + 1) |E|^(v - 1) exceptional
                  points among the |E|^v points of the fold. A point is exceptional if there is a
                  set of positions, leaving out at most e, on which the rows' sum with the point's
                  weights is equal to a code word, and on which one of the rows is equal to none.
 `list_unique`    for 2 e < d, at most one table of polynomials is within e columns of a table.

Not claimed. Nothing at a radius of a third of the distance or more for `mcaEq_third`, or of half
the distance or more for `list_unique`. Nothing on how many positions of a word are hidden. Nothing
on protocols. That the format's points are those of the programs is not a matter of this file.
-/
import Cb.Ld.LdFoldEqCodeProofs
import OnBytes.Slice.LinkAt
import OnBytes.Slice.Points

set_option autoImplicit false

namespace OnBytes.Slice
open Cb

/-- The library's Reed-Solomon code at the format's points, over the base field: 2^a positions
and r + l coefficients. All coefficients count as the message here, because a table format names
the places of its message itself. The three further parameters of `Code.RS.code` are read by no
statement of this file and are 0. -/
def rsCode (C : Fmt.M1.Code) : Code.Enc GF :=
  Code.RS.code (ptOf C.a) (C.r + C.l) (C.r + C.l) 0 0 0

/-- The format's generator matrix is that of the library's code, read over the extension field.
Both have the image of z^k at the position with the point z and the coefficient number k. -/
theorem genOf_eq_GE (C : Fmt.M1.Code) : genOf C = (rsCode C).GE GE := by
  funext x k
  rfl

/-- The library's code at the format's points has the distance 2^a - (r + l) + 1 over the base
field, since the points are different. -/
theorem hasDist_rsCode (C : Fmt.M1.Code) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) :
    Blocks.HasDist (rsCode C).G (2 ^ C.a - (C.r + C.l) + 1) :=
  Code.RS.code_dist (ptOf_inj C.a ha) hk

/-- Distance. Over the extension field, the word of a polynomial other than 0 with r + l
coefficients is not 0 at 2^a - (r + l) + 1 positions or more. -/
theorem hasDist_genOf (C : Fmt.M1.Code) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) :
    Blocks.HasDist (genOf C) (2 ^ C.a - (C.r + C.l) + 1) := by
  have h : Blocks.HasDist ((rsCode C).GE GE) (2 ^ C.a - (C.r + C.l) + 1) :=
    Blocks.HasDist.map (E := GE) (hasDist_rsCode C ha hk)
  rwa [← genOf_eq_GE] at h

/-- A table format with the format's generator matrix is the library's table format under its
Reed-Solomon code, with the same number of row variables, places, sample map, radius and order. -/
theorem eq_ofEnc (C : Fmt.M1.Code) {J : Type}
    (X : LdIx GE (Fin (2 ^ C.a)) (Fin (C.r + C.l)) J) (hG : X.G = genOf C) :
    X = LdIx.ofEnc GE (rsCode C) (Nat.le_refl (C.r + C.l)) X.pl X.v X.Z X.eM X.rank := by
  obtain ⟨v, G, pl, Z, eM, rank⟩ := X
  have hG' : G = (rsCode C).GE GE := hG.trans (genOf_eq_GE C)
  subst hG'
  rfl

/-- Agreement, up to a third of the distance. For 3 e < 2^a - (r + l) + 1 every table has at
most v (e + 1) |E|^(v - 1) exceptional points of the fold. -/
theorem mcaEq_third (C : Fmt.M1.Code) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) {J : Type}
    [Fintype J] (X : LdIx GE (Fin (2 ^ C.a)) (Fin (C.r + C.l)) J) (hG : X.G = genOf C) (e : ℕ)
    (h3 : 3 * e < 2 ^ C.a - (C.r + C.l) + 1) :
    X.MCAeq e (X.v * (e + 1) * Fintype.card GE ^ (X.v - 1)) := by
  have h := ldFc_mca_third GF GE (rsCode C) (Nat.le_refl (C.r + C.l)) J X.pl X.v X.Z X.eM X.rank e
    (hasDist_rsCode C ha hk) h3
  rwa [← eq_ofEnc C X hG] at h

/-- Unique decoding for tables with any set R of rows: for 2 e < 2^a - (r + l) + 1 at most one table
of polynomials has its words within e columns of the table f. -/
theorem list_unique_genOf (C : Fmt.M1.Code) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) (e : ℕ)
    (h2 : 2 * e < 2 ^ C.a - (C.r + C.l) + 1) (R : Type) (f : R → Fin (2 ^ C.a) → GE) :
    Ood.ListLE (Blocks.DecodesTo (genOf C) e f) 1 := by
  rw [genOf_eq_GE]
  exact ldFc_list_unique GF GE (rsCode C) e (hasDist_rsCode C ha hk) h2 R f

/-- The list, up to half the distance. For 2 e < 2^a - (r + l) + 1 at most one table of
polynomials has its words within e columns of a table of the format X. -/
theorem list_unique (C : Fmt.M1.Code) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) {J : Type}
    (X : LdIx GE (Fin (2 ^ C.a)) (Fin (C.r + C.l)) J) (hG : X.G = genOf C) (e : ℕ)
    (h2 : 2 * e < 2 ^ C.a - (C.r + C.l) + 1) (f : X.Row → Fin (2 ^ C.a) → GE) :
    Ood.ListLE (Blocks.DecodesTo X.G e f) 1 := by
  rw [hG]
  exact list_unique_genOf C ha hk e h2 X.Row f

end OnBytes.Slice

#print axioms OnBytes.Slice.genOf_eq_GE
#print axioms OnBytes.Slice.eq_ofEnc
#print axioms OnBytes.Slice.hasDist_genOf
#print axioms OnBytes.Slice.mcaEq_third
#print axioms OnBytes.Slice.list_unique
