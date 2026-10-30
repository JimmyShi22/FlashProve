-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/LinPort.lean: the test on a stored table has three rounds beside its sendings: the
library's error counts of these three against the rounds that the planner adds for them.

The three rounds of the library's test `LdLinP` (Cb/Ld/LdLin.lean) are the shared point, the
locations and the point zeta; Cb/Pv/Lin.lean has their errors and numbers of values. The planner's
routine `planLinShared` (OnBytes/Params/Planner.lean) adds "LIN point", "LOC" and "LIN zeta", with
two sendings between them (`linSharedList`, OnBytes/Params/PlanListsChains.lean). Definitions and
statements with their proofs.
Main names:
  `linProx`, `linAgree`: the distance at which the table is read; the agreement of the locations:
    in the planner's own words.
  `linPoint`, `linLoc`, `linZeta`, `linSharedList_eq`: the three rounds by name; the planner's list
    is these three with the two sendings between them.
  `zeta_fits`, `zeta_tied`: "LIN zeta" fits l * q ^ (l - 1) of q ^ l: the bound is that ratio; so of
    the block's `errZeta`.
  `loc_covered`, `loc_tied`: "LOC" covers (n - e - 1) ^ t of n ^ t, if n - e - 1 is at most what the
    agreement encloses, times n; so of the block's `errLoc`.
  `pt_num`, `pt_covered`, `pt_tied`: "LIN point" covers
    εf * q ^ k + (v + k) * q ^ (v + k - 1) of q ^ (v + k), if εf is at most
    (v * B + L * v) * q ^ (v - 1), for a whole number B at most what the count of the table's
    distance encloses and L at most its list size; so of the block's `errPt εf`.
Limits: for the point and the locations an inequality is shown, for zeta an equality. The clause on
εf is a premise, and it bounds εf from above. The library's block is knowledge sound if at most εf
points are bad for the fold (`LdLinP.FoldErr`), which bounds εf from below. That both hold of one εf
is not shown here. The scope is `.once`.
That a price is not marked bad is a hypothesis. That the field and the code of a block have as many
elements and positions as the setting and the table say are hypotheses.
Bytes and roots are not compared.

-/
import OnBytes.Tie.Pv.PortKit
import OnBytes.Params.PlanListsChains
import OnBytes.Params.LinkPrices
import Cb.Pv.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lin
open OnBytes OnBytes.Params Iop Cb

/-! ### the planner's rounds by name -/

/-- The distance at which the table is read. -/
def linProx (s : Setting) (T : TableSize) (x : LinSize) : Proximity :=
  if x.oneTime then (tableAnalysis s T).once else (tableAnalysis s T).later

/-- The agreement of the locations. -/
def linAgree (s : Setting) (T : TableSize) (x : LinSize) : Bound :=
  (linProx s T x).agree

/-- "LIN point". -/
def linPoint (s : Setting) (T : TableSize) (x : LinSize) : RoundSpec :=
  .said "LIN point" .closeness
    (Bound.ofNat x.instances * fieldError s (T.v + x.kLo) + tableFoldError s T (linProx s T x))
    { drawE := T.v + x.kLo, rests := (linProx s T x).source,
      priced := .callersWord } 0 0 0

/-- "LOC". -/
def linLoc (s : Setting) (c : Scope) (T : TableSize) (x : LinSize) : RoundSpec :=
  .said "LOC" .query (Bound.pow (linAgree s T x) (linColumns s c T x))
    { poss := linColumns s c T x, logN := T.code.logN, priced := .callersWord } 0 0 0

/-- "LIN zeta". -/
def linZeta (s : Setting) (x : LinSize) : RoundSpec :=
  .said "LIN zeta" .field (fieldError s x.rowsLog) { drawE := x.rowsLog, priced := .roundItself }
    0 0 0

/-- The planner's list is the three rounds with the two sendings between them. -/
theorem linSharedList_eq (s : Setting) (c : Scope) (T : TableSize) (x : LinSize) :
    linSharedList s c T x =
      linPoint s T x :: sendSeed s [x.u] x.rootsU ::
      .silent "SEND answer" (24 * (s.samples * 1)) (s.samples * 1) ::
      linLoc s c T x :: sendSeed s (x.omega :: x.besideOmega) x.rootsOmega ::
      .silent "SEND answer" (24 * (s.samples * (x.besideOmega.length + 1)))
        (s.samples * (x.besideOmega.length + 1)) :: [linZeta s x] := rfl

/-! ### numbers -/

theorem pred_pow (m q : ℕ) : m * q ^ (m - 1) * q = m * q ^ m := by
  cases m with
  | zero => simp
  | succ n => rw [Nat.add_sub_cancel, Nat.mul_assoc, ← pow_succ]

/-- The point's count, times q. -/
theorem pt_num {εf v k B L q : ℕ} (h : εf ≤ (v * B + L * v) * q ^ (v - 1)) :
    (εf * q ^ k + (v + k) * q ^ (v + k - 1)) * q ≤ (v * B + L * v + (v + k)) * q ^ (v + k) := by
  have h1 : εf * q ^ k * q ≤ (v * B + L * v) * q ^ (v + k) := by
    calc εf * q ^ k * q ≤ (v * B + L * v) * q ^ (v - 1) * q ^ k * q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
      _ = (B + L) * (v * q ^ (v - 1) * q) * q ^ k := by ring
      _ = (B + L) * (v * q ^ v) * q ^ k := by rw [pred_pow]
      _ = (v * B + L * v) * q ^ (v + k) := by
          rw [pow_add]
          ring
  calc (εf * q ^ k + (v + k) * q ^ (v + k - 1)) * q
      = εf * q ^ k * q + (v + k) * q ^ (v + k - 1) * q := by ring
    _ = εf * q ^ k * q + (v + k) * q ^ (v + k) := by rw [pred_pow]
    _ ≤ (v * B + L * v) * q ^ (v + k) + (v + k) * q ^ (v + k) := Nat.add_le_add_right h1 _
    _ = (v * B + L * v + (v + k)) * q ^ (v + k) := by ring

/-! ### zeta -/

/-- "LIN zeta": the bound is the ratio of the count to the number of values. -/
theorem zeta_fits (s : Setting) (x : LinSize) (hq : 0 < s.cardE) :
    Fits s.cardE (x.rowsLog * s.cardE ^ (x.rowsLog - 1), s.cardE ^ x.rowsLog) (linZeta s x) :=
  ⟨by simp [valuesOf, linZeta], x.rowsLog, s.cardE, hq, rfl, pred_pow _ _⟩

/-! ### the locations -/

/-- "LOC". -/
theorem loc_covered {s : Setting} {T : TableSize} {x : LinSize} {a : ℝ} {n e : ℕ}
    (ha : EnclR (linAgree s T x) a) (hn : 0 < n) (h : ((n - e - 1 : ℕ) : ℝ) ≤ a * (n : ℝ))
    (g : (Bound.pow (linAgree s T x) (linColumns s .once T x)).bad = false) :
    Covered s .once ((n - e - 1) ^ linColumns s .once T x, n ^ linColumns s .once T x)
      (linLoc s .once T x) := by
  unfold Covered linLoc
  rw [(round_once s _ _ _ _ _ _ _).1]
  refine le_trans (le_of_eq ?_) (positions_cover (linColumns s .once T x) ha hn h g)
  push_cast
  rw [div_pow]

/-! ### the point -/

/-- "LIN point". -/
theorem pt_covered {s : Setting} {T : TableSize} {x : LinSize}
    {cnt : ℝ} {B L εf : ℕ} (hx : EnclR (linProx s T x).count cnt) (hB : (B : ℝ) ≤ cnt)
    (hL : L ≤ (linProx s T x).list) (hi : 1 ≤ x.instances) (hq : 0 < s.cardE)
    (hε : εf ≤ (T.v * B + L * T.v) * s.cardE ^ (T.v - 1))
    (g : (Bound.ofNat x.instances * fieldError s (T.v + x.kLo) +
      tableFoldError s T (linProx s T x)).bad = false) :
    Covered s .once
      (εf * s.cardE ^ x.kLo + (T.v + x.kLo) * s.cardE ^ (T.v + x.kLo - 1),
        s.cardE ^ (T.v + x.kLo)) (linPoint s T x) := by
  unfold Covered linPoint
  rw [(round_once s _ _ _ _ _ _ _).1]
  obtain ⟨w, ew, lw⟩ := tableFold_covers s T (linProx s T x) hx hB
    (le_trans (Nat.cast_nonneg B) hB) hL
  refine le_trans ?_ (Bound.le_errorR (Bound.enclR_add (Bound.enclR_mul
    (Bound.enclR_ofNat x.instances) (enclR_fieldError s (T.v + x.kLo))) ew) g)
  have hQ : (0 : ℝ) < (s.cardE : ℝ) := by exact_mod_cast hq
  have hQm : (0 : ℝ) < ((s.cardE ^ (T.v + x.kLo) : ℕ) : ℝ) := by exact_mod_cast pow_pos hq _
  have h1 : ((εf * s.cardE ^ x.kLo + (T.v + x.kLo) * s.cardE ^ (T.v + x.kLo - 1) : ℕ) : ℝ) /
      ((s.cardE ^ (T.v + x.kLo) : ℕ) : ℝ) ≤
      ((T.v * B + L * T.v + (T.v + x.kLo) : ℕ) : ℝ) / (s.cardE : ℝ) := by
    rw [div_le_iff₀ hQm, div_mul_eq_mul_div, le_div_iff₀ hQ]
    exact_mod_cast pt_num hε
  have h2 : ((T.v + x.kLo : ℕ) : ℝ) / (s.cardE : ℝ) ≤
      (x.instances : ℝ) * (((T.v + x.kLo : ℕ) : ℝ) / (s.cardE : ℝ)) := by
    have hi' : (1 : ℝ) ≤ (x.instances : ℝ) := by exact_mod_cast hi
    exact le_mul_of_one_le_left (by positivity) hi'
  refine h1.trans ?_
  have h3 : ((T.v * B + L * T.v + (T.v + x.kLo) : ℕ) : ℝ) / (s.cardE : ℝ) =
      ((T.v : ℝ) * (B : ℝ) + (L : ℝ) * (T.v : ℝ)) / (s.cardE : ℝ) +
        ((T.v + x.kLo : ℕ) : ℝ) / (s.cardE : ℝ) := by
    push_cast
    ring
  rw [h3]
  linarith

/-! ### at the library's blocks -/

section Blocks
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (P : LdLinP E ι κ J Y)

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- The block's last round fits "LIN zeta". -/
theorem zeta_tied (s : Setting) (x : LinSize) (hq : Fintype.card E = s.cardE)
    (hl : P.D.l = x.rowsLog) :
    Fits s.cardE (P.errZeta, Fintype.card (Fin P.D.l → E)) (linZeta s x) := by
  have h0 : 0 < s.cardE := hq ▸ Fintype.card_pos
  unfold LdLinP.errZeta
  rw [Fintype.card_fun, Fintype.card_fin, hq, hl]
  exact zeta_fits s x h0

omit [Field E] [Fintype E] [Fintype κ] [Fintype J] [Fintype Y] in
/-- The block's locations are covered by "LOC". -/
theorem loc_tied {s : Setting} {T : TableSize} {x : LinSize} {a : ℝ}
    (ht : P.t = linColumns s .once T x) (ha : EnclR (linAgree s T x) a)
    (h : ((Fintype.card ι - P.e' - 1 : ℕ) : ℝ) ≤ a * (Fintype.card ι : ℝ))
    (g : (Bound.pow (linAgree s T x) (linColumns s .once T x)).bad = false) :
    Covered s .once (P.errLoc, Fintype.card (Fin P.t → ι)) (linLoc s .once T x) := by
  unfold LdLinP.errLoc
  rw [Fintype.card_fun, Fintype.card_fin, ht]
  exact loc_covered ha Fintype.card_pos h g

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- The block's shared point is covered by "LIN point". -/
theorem pt_tied {s : Setting} {T : TableSize} {x : LinSize} {cnt : ℝ}
    {B L εf : ℕ} (hq : Fintype.card E = s.cardE) (hv : P.D.X.v = T.v) (hk : P.D.klo = x.kLo)
    (hx : EnclR (linProx s T x).count cnt) (hB : (B : ℝ) ≤ cnt) (hL : L ≤ (linProx s T x).list)
    (hi : 1 ≤ x.instances) (hε : εf ≤ (T.v * B + L * T.v) * s.cardE ^ (T.v - 1))
    (g : (Bound.ofNat x.instances * fieldError s (T.v + x.kLo) +
      tableFoldError s T (linProx s T x)).bad = false) :
    Covered s .once (P.errPt εf, Fintype.card P.D.Pt) (linPoint s T x) := by
  have h0 : 0 < s.cardE := hq ▸ Fintype.card_pos
  have hc : Fintype.card P.D.Pt = s.cardE ^ (T.v + x.kLo) := by
    show Fintype.card ((Fin P.D.X.v → E) × (Fin P.D.klo → E)) = _
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      hq, hv, hk, pow_add]
  unfold LdLinP.errPt
  rw [hc, hq, hv, hk]
  exact pt_covered hx hB hL hi h0 hε g

end Blocks

end Cb.Pv.Lin

#print axioms Cb.Pv.Lin.linSharedList_eq
#print axioms Cb.Pv.Lin.zeta_tied
#print axioms Cb.Pv.Lin.loc_tied
#print axioms Cb.Pv.Lin.pt_tied
