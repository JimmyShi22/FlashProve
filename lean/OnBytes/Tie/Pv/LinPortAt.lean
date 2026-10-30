-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/LinPortAt.lean: the shared point and the locations of the test on a stored table, at
the library's own numbers: the planner's rounds cover them, for a table whose distances are given
by integers.

OnBytes/Tie/Pv/LinPort.lean shows that "LIN point" and "LOC" cover the library's error counts under
premises on what the planner's count, list size and agreement enclose. For a table whose distances
are given by integers, with m as printed, the laws of OnBytes/Params/LibraryJohnson.lean and
OnBytes/Params/MorePrices.lean pay these premises at a radius e. Definitions and statements with
their proofs.
Main names:
  `linM T x`: the integer of the distance at which the table is read.
  `linProx_johnson`: that distance is the planner's `johnson` at the table's code and `linM`.
  `ptCount T e q`: (v * B + L * v) * q ^ (v - 1), for B the integer part of the library's assumed
    bound `Cb.bchksBound` and L its `Cb.listMax`, at the table's code and the radius e.
  `pt_covered_at`, `pt_tied_at`: "LIN point", with a closeness term, covers the library's count of
    the point at εf := `ptCount`, for a radius e ≤ (1 - a) * n, where a is the agreement of the
    distance and n the length of the table's code.
  `loc_covered_at`, `loc_tied_at`: "LOC", at a table that is read near, covers (n - e - 1) ^ t of
    n ^ t for every radius e that is at least the planner's `upperRadius` of the distance.
Limits: those of OnBytes/Tie/Pv/LinPort.lean, but for the premises that are paid here. That the
library's block is knowledge sound at εf := `ptCount` (`LdLinP.FoldErr`) is not shown here. One
radius serves both statements only if it is at least `upperRadius` and at most (1 - a) * n; no
radius is evaluated here.

-/
import OnBytes.Tie.Pv.LinPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lin
open OnBytes OnBytes.Params Iop Cb

/-- The integer of the distance at which the table is read. -/
def linM (T : TableSize) (x : LinSize) : ℕ :=
  if x.oneTime then T.distances.mOnce else T.distances.mLater

/-- The distance at which the table is read, for a table with integers and m as printed. -/
theorem linProx_johnson {s : Setting} {T : TableSize} (x : LinSize) (hM : T.distances.mOnce ≠ 0)
    (hp : s.printed = true) : linProx s T x = johnson (wordOf T.code) (linM T x) true := by
  obtain ⟨a1, a0⟩ := tableAnalysis_fromM (s := s) hM
  rw [hp] at a1 a0
  unfold linProx linM
  by_cases h : x.oneTime = true
  · rw [if_pos h, if_pos h, a1]
  · rw [if_neg h, if_neg h, a0]

/-- The count of points that are bad for the fold, at the library's numbers. -/
noncomputable def ptCount (T : TableSize) (e q : ℕ) : ℕ :=
  (T.v * ⌊Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e⌋₊ +
    Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e * T.v) * q ^ (T.v - 1)

section
variable {s : Setting} {T : TableSize} {x : LinSize} {e : ℕ}

/-- "LIN point" at the library's numbers. -/
theorem pt_covered_at (hM : T.distances.mOnce ≠ 0)
    (hp : s.printed = true) (gc : (linProx s T x).count.bad = false)
    (hk : 0 < (wordOf T.code).k)
    (he : (e : ℝ) ≤ (1 - (wordOf T.code).agreeAt (linM T x) true) * ((wordOf T.code).n : ℝ))
    (hi : 1 ≤ x.instances) (hq : 0 < s.cardE)
    (g : (Bound.ofNat x.instances * fieldError s (T.v + x.kLo) +
      tableFoldError s T (linProx s T x)).bad = false) :
    Covered s .once
      (ptCount T e s.cardE * s.cardE ^ x.kLo + (T.v + x.kLo) * s.cardE ^ (T.v + x.kLo - 1),
        s.cardE ^ (T.v + x.kLo)) (linPoint s T x) := by
  have ej := linProx_johnson (s := s) (T := T) x hM hp
  have gc' : (johnson (wordOf T.code) (linM T x) true).count.bad = false := ej ▸ gc
  have hx : EnclR (linProx s T x).count
      (countAt (wordOf T.code).n (wordOf T.code).rho
        (1 - (wordOf T.code).agreeAt (linM T x) true) (linM T x)) := by
    rw [ej]
    exact enclR_johnson_count _ _ _
  have hB : ((⌊Cb.bchksBound (wordOf T.code).n (wordOf T.code).k e⌋₊ : ℕ) : ℝ) ≤
      countAt (wordOf T.code).n (wordOf T.code).rho
        (1 - (wordOf T.code).agreeAt (linM T x) true) (linM T x) :=
    (Nat.floor_le (bchksBound_nonneg _ _ _)).trans
      (bchksBound_le_countAt (johnson_count_good gc').1 hk le_rfl he)
  have hL : Cb.listMax (wordOf T.code).n ((wordOf T.code).n - (wordOf T.code).k) e ≤
      (linProx s T x).list := by
    rw [ej]
    exact listMax_le_list gc' hk he
  exact pt_covered hx hB hL hi hq le_rfl g

/-- "LOC" at a table that is read near, from the upper radius on. -/
theorem loc_covered_at (hM : T.distances.mOnce ≠ 0)
    (hp : s.printed = true)
    (p : ((linProx s T x).delta * Bound.ofNat (wordOf T.code).n).bad = false)
    (u : upperRadius (linProx s T x).delta (wordOf T.code).n ≤ e)
    (g : (Bound.pow (linAgree s T x) (linColumns s .once T x)).bad = false) :
    Covered s .once
      (((wordOf T.code).n - e - 1) ^ linColumns s .once T x,
        (wordOf T.code).n ^ linColumns s .once T x) (linLoc s .once T x) := by
  have ej := linProx_johnson (s := s) (T := T) x hM hp
  have ha : EnclR (linAgree s T x) ((wordOf T.code).agreeAt (linM T x) true) := by
    unfold linAgree
    rw [ej]
    exact enclR_johnson_agree _ _ _
  have hd : EnclR (linProx s T x).delta (1 - (wordOf T.code).agreeAt (linM T x) true) := by
    rw [ej]
    exact enclR_johnson_delta _ _ _
  have hpos : 0 < (wordOf T.code).n := by
    unfold Word.n
    positivity
  exact loc_covered ha hpos (agree_of_upperRadius hd p u (agreeAt_nonneg _ _ _)) g

end

section Blocks
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (P : LdLinP E ι κ J Y) {s : Setting} {T : TableSize} {x : LinSize}

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- The block's shared point, at εf := `ptCount`. -/
theorem pt_tied_at {e : ℕ} (hM : T.distances.mOnce ≠ 0)
    (hp : s.printed = true) (gc : (linProx s T x).count.bad = false)
    (hk : 0 < (wordOf T.code).k)
    (he : (e : ℝ) ≤ (1 - (wordOf T.code).agreeAt (linM T x) true) * ((wordOf T.code).n : ℝ))
    (hi : 1 ≤ x.instances) (hq : Fintype.card E = s.cardE) (hv : P.D.X.v = T.v)
    (hkl : P.D.klo = x.kLo)
    (g : (Bound.ofNat x.instances * fieldError s (T.v + x.kLo) +
      tableFoldError s T (linProx s T x)).bad = false) :
    Covered s .once (P.errPt (ptCount T e s.cardE), Fintype.card P.D.Pt) (linPoint s T x) := by
  have h0 : 0 < s.cardE := hq ▸ Fintype.card_pos
  have hc : Fintype.card P.D.Pt = s.cardE ^ (T.v + x.kLo) := by
    show Fintype.card ((Fin P.D.X.v → E) × (Fin P.D.klo → E)) = _
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      hq, hv, hkl, pow_add]
  unfold LdLinP.errPt
  rw [hc, hq, hv, hkl]
  exact pt_covered_at hM hp gc hk he hi h0 g

omit [Field E] [Fintype E] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- The block's locations. -/
theorem loc_tied_at (hM : T.distances.mOnce ≠ 0)
    (hp : s.printed = true) (hι : Fintype.card ι = (wordOf T.code).n)
    (ht : P.t = linColumns s .once T x)
    (p : ((linProx s T x).delta * Bound.ofNat (wordOf T.code).n).bad = false)
    (u : upperRadius (linProx s T x).delta (wordOf T.code).n ≤ P.e')
    (g : (Bound.pow (linAgree s T x) (linColumns s .once T x)).bad = false) :
    Covered s .once (P.errLoc, Fintype.card (Fin P.t → ι)) (linLoc s .once T x) := by
  unfold LdLinP.errLoc
  rw [Fintype.card_fun, Fintype.card_fin, ht, hι]
  exact loc_covered_at hM hp p u g

end Blocks

end Cb.Pv.Lin

#print axioms Cb.Pv.Lin.linProx_johnson
#print axioms Cb.Pv.Lin.pt_tied_at
#print axioms Cb.Pv.Lin.loc_tied_at
