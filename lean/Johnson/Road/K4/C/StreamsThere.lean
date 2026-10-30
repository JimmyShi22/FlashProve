-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StreamsThere.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the lookup's join: the two hypotheses that
lineRd_of (LineRdOf.lean) leaves: the tables of the residual stream after each write of the group
(Strm, StreamReturn.lean), and the rows of digits of the norms. With them: what the forms of the
keys read at a layer is there. Statements and proofs.

  `tensorAt_inv`   what tensorAt has found.
  `xb_there`       a block of a matrix of the stream.
  **`strm_of`**      Strm after each write.
  **`rowDigits_of`**       the rows of digits.
  **`lineRd_plan`**  LineRd at each layer.

Not shown here. That the hypotheses PlanRd hold together at any plan: no example is shown here.
UNDER THE LIBRARY's ELEVEN SWITCHES ALONE, at profile 4. Public data alone: whether a form IS
THERE, nothing on what it is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.LineRdOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Ten)
open Inst.Model.FFSeg (Arr Cell)

variable {v : Env}

/-- What tensorAt has found: the tensor under its name, and its matrix's family at the point. -/
theorem tensorAt_inv {X Z : String} {t : Ten} {tb : ℕ} (h : v.tensorAt X Z = some (t, tb)) :
    v.y.T_ X = some t ∧ v.tabAt (Env.mname t.mat ++ "@" ++ Z) = some tb := by
  unfold Env.tensorAt at h
  obtain ⟨t', h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tb', h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨h1, h2⟩

/-- A block of a matrix of the residual stream is there. mat: 4 for the stream that comes in, 5 for
the one that goes out. -/
theorem xb_there (B : PlanRd v) {mat : ℕ} (hm : mat ∈ [0, 3, 4, 5])
    (hcap : v.y.h.xl * v.y.h.d ≤ partsM v.y mat * colsM v.y mat * fcM v.y mat) {tb : ℕ}
    (R : Reach v tb (partsM v.y mat * (colsM v.y mat * (rowsM v.y mat / 2 ^ v.y.h.la))))
    {xh : ℕ} (hx : xh < v.y.h.d / v.y.S2) : (v.xbA tb xh).isSome = true := by
  have hS2 : 0 < v.y.S2 := by
    rw [B.L.S2]
    exact Nat.two_pow_pos _
  have hfc := fc_blocks B.L B.L2 B.la hm
  refine xbA_some R fun l hl => ?_
  rw [B.L.xb] at hl ⊢
  have hl' : l < v.y.h.xl := hl
  have e0 : tenCell (⟨0, v.y.h.xl, 1, v.y.h.d⟩ : TenAt) l 0 0 = l * v.y.h.d := by
    show 0 + (l * 1 + 0) * v.y.h.d + 0 = l * v.y.h.d
    rw [Nat.zero_add, Nat.add_zero, Nat.add_zero, Nat.mul_one]
  rw [e0]
  have hxw : xh * v.y.S2 < v.y.h.d := by
    have h1 := (Nat.le_div_iff_mul_le hS2).mp (Nat.succ_le_of_lt hx)
    rw [Nat.succ_mul] at h1
    omega
  have hle : (l + 1) * v.y.h.d ≤ v.y.h.xl * v.y.h.d :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hl')
  rw [Nat.succ_mul] at hle
  have e1 : (l * v.y.h.d + xh * v.y.S2) / v.y.S2 = l * v.y.h.d / v.y.S2 + xh :=
    Nat.add_mul_div_right _ _ hS2
  rw [← e1]
  apply Nat.div_lt_of_lt_mul
  calc l * v.y.h.d + xh * v.y.S2 < v.y.h.xl * v.y.h.d := by omega
    _ ≤ partsM v.y mat * colsM v.y mat * fcM v.y mat := hcap
    _ = v.y.S2 * (partsM v.y mat * (colsM v.y mat * (rowsM v.y mat / 2 ^ v.y.h.la))) := by
      rw [hfc]
      ring

/-- **THE TABLE OF THE RESIDUAL STREAM AFTER EACH WRITE OF THE GROUP IS FOUND, AND ITS BLOCKS ARE
THERE.** CONDITIONAL: on B. -/
theorem strm_of (B : PlanRd v) {sg : ℕ} (h : sg ≤ v.y.NW * v.y.Lam) : Strm v sg := by
  obtain ⟨txs, hT, hmat, -⟩ := ten_of B.L B.S .xs (Or.inl rfl)
  have hT' : v.y.T_ "xs" = some txs := hT
  have hmat' : txs.mat = 0 := hmat
  by_cases h0 : sg = 0
  · subst h0
    obtain ⟨tb, htb, R⟩ := B.long ("xbI" ++ "@" ++ "Z", 4) (by simp)
    exact ⟨tb, txs, htb, hT', fun xh hx => xb_there B (by simp) (cap_stream B.L2) R hx⟩
  · by_cases h1 : sg = v.y.NW * v.y.Lam
    · obtain ⟨tb, htb, R⟩ := B.long ("xbO" ++ "@" ++ "Z", 5) (by simp)
      have c0 : (sg == 0) = false := by simpa using h0
      have c1 : (sg == v.y.NW * v.y.Lam) = true := by simpa using h1
      refine ⟨tb, txs, ?_, hT', fun xh hx => ?_⟩
      · rw [c0, c1]
        exact htb
      · rw [c0, c1]
        exact xb_there B (by simp) (cap_out B.L2) R hx
    · have c0 : (sg == 0) = false := by simpa using h0
      have c1 : (sg == v.y.NW * v.y.Lam) = false := by simpa using h1
      have hi : sg - 1 < 2 * 2 ^ v.y.h.ll - 1 := by
        have e := B.L.NW
        have e' := B.L.Lam
        rw [e, e'] at h h1
        omega
      obtain ⟨t, tb, ht, H⟩ := rd_af B .xs rfl rfl (i := sg - 1) hi
      obtain ⟨a1, a2⟩ := tensorAt_inv ht
      have et : t = txs := Option.some.inj (a1.symm.trans hT')
      subst et
      refine ⟨tb, t, ?_, hT', fun xh hx => ?_⟩
      · rw [c0, c1]
        rw [hmat'] at a2
        exact a2
      · rw [c0, c1]
        exact H xh hx

/-- **THE ROWS OF DIGITS OF A LAYER's TWO NORMS ARE THERE.** CONDITIONAL: on B. -/
theorem rowDigits_of (B : PlanRd v) {lam : ℕ} (h : lam < v.y.Lam) :
    ∃ b trow, v.tabAt "ar@zt" = some b ∧ v.y.T_ "row" = some trow ∧
      ∀ x, x < v.y.NN * ledNR v.y.h.xl →
        (v.U3at b (trow.OFF + (v.y.NN * lam + x / ledNR v.y.h.xl) * ledNR v.y.h.xl +
          x % ledNR v.y.h.xl)).isSome = true := by
  obtain ⟨trow, hT, -, -, -, hJ, -⟩ := ten_of B.L B.S .D (Or.inl rfl)
  obtain ⟨b, hb, R⟩ := B.short ("ar" ++ "@" ++ "zt", 2) (by simp)
  have hNR : ledNR v.y.h.xl = 99 := by
    rw [B.S.xl]
    rfl
  have hJ' : trow.J = 99 := hJ
  have hi : lam < 2 ^ v.y.h.ll := by
    rw [← B.L.Lam]
    exact h
  refine ⟨b, trow, hb, hT, fun x hx => ?_⟩
  rw [hNR, B.L.NN] at hx ⊢
  have e : trow.OFF + (2 * lam + x / 99) * 99 + x % 99 =
      tenCell trow.place 0 (2 * lam + x / 99) (x % 99) := by
    show _ = trow.OFF + (0 * trow.cnt + (2 * lam + x / 99)) * trow.J + x % 99
    rw [hJ', Nat.zero_mul, Nat.zero_add]
  rw [e, (place_eq_feat B.L B.S (sized_dimOf _) .D (Or.inl rfl) hT 0 _ _).1]
  have hv : (⟨.D, 0, 2 * lam + x / 99, x % 99, 0⟩ : Cell).Valid (dimOf v.y.h) := by
    refine ⟨Nat.zero_lt_one, ?_, Nat.mod_lt _ (by decide),
      Inst.Model.FFSeg.IndexFacts.T_pos _⟩
    show 2 * lam + x / 99 < 2 * 2 ^ v.y.h.ll
    omega
  obtain ⟨-, hlt⟩ := valid_inMat B.L2 B.S (sized_dimOf _) B.p4 hv
  rw [Nat.mul_assoc] at hlt
  exact R _ hlt

/-- **WHAT THE FAMILIES OF ALL LAYERS READ IS THERE**, at each layer of the group. CONDITIONAL: on
B. -/
theorem lineRd_plan (B : PlanRd v) {lam : ℕ} (h : lam < v.y.Lam) : LineRd v lam := by
  have e := B.L.NW
  exact lineRd_of B h (strm_of B (by rw [e]; omega)) (strm_of B (by rw [e]; omega))
    (strm_of B (by rw [e]; omega)) (rowDigits_of B h)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.rowDigits_of
#print axioms OnBytes.Road.K4.C.lineRd_plan
#print axioms OnBytes.Road.K4.C.tensorAt_inv
#print axioms OnBytes.Road.K4.C.xb_there
#print axioms OnBytes.Road.K4.C.strm_of
