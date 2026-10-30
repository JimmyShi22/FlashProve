-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/LineRdOf.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the lookup's join: what the forms of the
keys read at a layer (LineRd, LineRdM, LineReturn.lean), tensor by tensor under the verifier's
names, from the laws for all arrays at once (TensorsThere.lean), at the sizes that the shape itself
gives (the library's dimOf). One definition of a hypothesis; statements and proofs.

  `PlanRd v`         the layout's plain facts, the switches, and the six families' entries.
  `rd_af`, `rd_qa`, `rd_ad`, `rd_ar`   an array of one of the four matrices.
  **`lineRdM_of`**     LineRdM at each layer with routed experts.
  **`lineRd_of`**      LineRd at each layer, the stream and the rows of digits being there.

Not shown here. That the hypotheses PlanRd hold together at any plan: no example is shown here.
UNDER THE LIBRARY's ELEVEN SWITCHES ALONE, at profile 4. THE RESIDUAL STREAM's THREE TABLES AND THE
ROWS OF DIGITS STAY HYPOTHESES OF lineRd_of (hs0, hs1, hs2, hrow). Public data alone: whether a
form IS THERE, nothing on what it is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.TensorsThere
import Johnson.Road.K4.C.LineReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env)
open Inst.Model.FFSeg (Arr)

/-- **The layout's plain facts, the switches, and the six families' entries.** This defines a
hypothesis; the definition claims nothing. -/
structure PlanRd (v : Env) : Prop where
  L : Laid v.y
  L2 : Laid2 v.y
  S : Switches v.y.h
  p4 : v.y.h.p4 = true
  la : v.y.h.la = v.y.ls + v.y.h.lt
  long : ∀ p ∈ [("af" ++ "@" ++ "Z", 0), ("qa" ++ "@" ++ "Z", 3), ("xbI" ++ "@" ++ "Z", 4),
      ("xbO" ++ "@" ++ "Z", 5)], ∃ tb, v.tabAt p.1 = some tb ∧
    Reach v tb (partsM v.y p.2 * (colsM v.y p.2 * (rowsM v.y p.2 / 2 ^ v.y.h.la)))
  short : ∀ p ∈ [("ad" ++ "@" ++ "zt", 1), ("ar" ++ "@" ++ "zt", 2)], ∃ tb,
    v.tabAt p.1 = some tb ∧
      Reach v tb (partsM v.y p.2 * (colsM v.y p.2 * (rowsM v.y p.2 / v.y.T)))

variable {v : Env}

/-- An array of the matrix af. -/
theorem rd_af (B : PlanRd v) (X : Arr) (hX : listed X = true) (hm : matNo X = 0) {i : ℕ}
    (hi : i < X.cnt (dimOf v.y.h)) :
    Long v (arrName X) i (X.width (dimOf v.y.h) / v.y.S2) :=
  long_of_arr B.L B.L2 B.S (sized_dimOf _) B.p4 B.la X (Or.inl hX) (Or.inl hm)
    (by rw [hm]; exact B.long ("af" ++ "@" ++ "Z", 0) (by simp)) hi

/-- An array of the matrix qa. -/
theorem rd_qa (B : PlanRd v) (X : Arr) (hX : listed X = true) (hm : matNo X = 3) {i : ℕ}
    (hi : i < X.cnt (dimOf v.y.h)) :
    Long v (arrName X) i (X.width (dimOf v.y.h) / v.y.S2) :=
  long_of_arr B.L B.L2 B.S (sized_dimOf _) B.p4 B.la X (Or.inl hX) (Or.inr hm)
    (by rw [hm]; exact B.long ("qa" ++ "@" ++ "Z", 3) (by simp)) hi

/-- An array of the matrix ad. -/
theorem rd_ad (B : PlanRd v) (X : Arr) (hX : listed X = true) (hm : matNo X = 1) {i : ℕ}
    (hi : i < X.cnt (dimOf v.y.h)) : Short v (arrName X) "zt" i (X.width (dimOf v.y.h)) :=
  short_of_arr B.L B.L2 B.S (sized_dimOf _) B.p4 X (Or.inl hX)
    (by rw [hm]; exact B.short ("ad" ++ "@" ++ "zt", 1) (by simp)) hi

/-- An array of the matrix ar. -/
theorem rd_ar (B : PlanRd v) (X : Arr) (hX : listed X = true) (hm : matNo X = 2) {i : ℕ}
    (hi : i < X.cnt (dimOf v.y.h)) : Short v (arrName X) "zt" i (X.width (dimOf v.y.h)) :=
  short_of_arr B.L B.L2 B.S (sized_dimOf _) B.p4 X (Or.inl hX)
    (by rw [hm]; exact B.short ("ar" ++ "@" ++ "zt", 2) (by simp)) hi

/-- **WHAT THE FAMILIES OF THE LAYERS WITH ROUTED EXPERTS READ IS THERE**, at each such layer.
CONDITIONAL: on B. -/
theorem lineRdM_of (B : PlanRd v) {lamM : ℕ} (h : lamM < v.y.LamM) : LineRdM v lamM := by
  have hi : lamM < 2 ^ v.y.h.ll / 2 := by
    rw [← B.L.LamM]
    exact h
  exact {
    xr := rd_ad B .xr rfl rfl hi
    lr := rd_ar B .lr rfl rfl hi
    rl := rd_ar B .rl rfl rfl hi
    sel := rd_ar B .sel rfl rfl hi
    ly := rd_ar B .ly rfl rfl hi
    l3 := rd_ar B .l3 rfl rfl hi
    sc := rd_ar B .sc rfl rfl hi }

/-- **WHAT THE FAMILIES OF ALL LAYERS READ IS THERE**, at each layer, the stream's three tables and
the rows of digits being there. CONDITIONAL: on B, hs0, hs1, hs2 and hrow. -/
theorem lineRd_of (B : PlanRd v) {lam : ℕ} (h : lam < v.y.Lam) (hs0 : Strm v (2 * lam))
    (hs1 : Strm v (2 * lam + 1)) (hs2 : Strm v (2 * lam + 2))
    (hrow : ∃ b trow, v.tabAt "ar@zt" = some b ∧ v.y.T_ "row" = some trow ∧
      ∀ x, x < v.y.NN * ledNR v.y.h.xl →
        (v.U3at b (trow.OFF + (v.y.NN * lam + x / ledNR v.y.h.xl) * ledNR v.y.h.xl +
          x % ledNR v.y.h.xl)).isSome = true) : LineRd v lam := by
  have hi : lam < 2 ^ v.y.h.ll := by
    rw [← B.L.Lam]
    exact h
  have hS2 : 0 < v.y.S2 := by
    rw [B.L.S2]
    exact Nat.two_pow_pos _
  have ekx : v.y.nqk / v.y.S2 - v.y.dq / v.y.S2 = v.y.h.Gk * v.y.h.dh / v.y.S2 := by
    obtain ⟨k, hk⟩ := B.L.bdq
    rw [B.L.nqk, B.L.dq, hk, Nat.mul_add_div hS2, Nat.mul_div_cancel_left _ hS2]
    exact Nat.add_sub_cancel_left _ _
  exact {
    u := rd_af B .up rfl rfl hi
    g0 := rd_af B .g0 rfl rfl hi
    gh := rd_af B .gh rfl rfl hi
    gc := rd_af B .gc rfl rfl hi
    s := rd_af B .sl rfl rfl hi
    ru := rd_af B .ru rfl rfl hi
    rg := rd_af B .rg rfl rfl hi
    aw := rd_af B .aw rfl rfl hi
    mw := rd_af B .mw rfl rfl hi
    ra := rd_af B .ra rfl rfl hi
    rm := rd_af B .rm rfl rfl hi
    ro := rd_af B .ro rfl rfl hi
    rd := rd_af B .rd rfl rfl hi
    qkw := by
      rw [B.L.nqk]
      exact rd_af B .qkw rfl rfl hi
    rqk := by
      rw [B.L.nqk]
      exact rd_af B .rqk rfl rfl hi
    q := by
      rw [B.L.dq]
      exact rd_qa B .q rfl rfl hi
    kx := by
      rw [ekx]
      exact rd_qa B .kx rfl rfl hi
    vw := by
      rw [B.L.dkv]
      exact rd_af B .vw rfl rfl hi
    rv := by
      rw [B.L.dkv]
      exact rd_af B .rv rfl rfl hi
    vv := by
      rw [B.L.dkv]
      exact rd_qa B .v rfl rfl hi
    s0 := hs0
    s1 := hs1
    s2 := hs2
    a := rd_ad B .a rfl rfl hi
    m := rd_ad B .m rfl rfl hi
    row := hrow
    fe := by
      have := B.L.ffe
      omega
    dq := by
      rw [B.L.nqk, B.L.dq]
      exact Nat.le_add_right _ _ }

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.rd_af
#print axioms OnBytes.Road.K4.C.rd_qa
#print axioms OnBytes.Road.K4.C.rd_ad
#print axioms OnBytes.Road.K4.C.rd_ar
#print axioms OnBytes.Road.K4.C.lineRdM_of
#print axioms OnBytes.Road.K4.C.lineRd_of
