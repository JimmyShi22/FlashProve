-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/MeanRd.lean: kind K5: the readers on "ah" are the library's own reads
of the cells (Inst/Model/Att/Sums.lean: rd2), for the written forms. These are twins of
readMaximum_rd2, readDenominator_rd2 and readIndexBit_rd2 (Johnson/Road/Rows/AttReadRow.lean), which
speak of a run of a routine in a context ("if the routine returns"). Here the written forms stand in
the run's place (Johnson/Desc/First/Att/Claims/Worth.lean where weighted_value and u3at_value
stood); the pure lemmas of Johnson/Road are used as they stand, and the proofs' pure parts follow
those proofs line for line.

Main names:
  `shVF_rd`, `overGF_rd`, `limbsF_rd2`, `readMaximumF_rd2`, `readDenominatorF_rd2`,
    `readIndexBitF_rd2`: ‹written form›.value ρ W = rd2 (L5.dimOf h.S) (pt ρ zg) (the table's token
    weights, read) (mxV, denV, ibV (cellsK h.S M) …).
  `score_start`: the twin of ScoreStartEnd (Johnson/Road/Rows/AttEnds58.lean): W.slot (sM6 + b) =
    rvM6 … (cellsK h.S M) b.
  `key_bits`: the twin of KeyAtIndexEndB: W.slot (sIb b k) = rvIBP ….
The setting is that of Johnson/Road/Rows/AttRead.lean: AttAt ρ W tl K3 M h lid cf fs: the reading
takes numerals to numbers; the shape is the planner's; the matrices fit; and every table of h.t.funs
is true of the matrices M in W. That last clause is a premise: it is what the smallness test is
meant to give; not shown in this file or in what it imports. TabAt: the table lies in the list with
these weights.
One premise more than in Johnson/Road/Rows: the indices read lie in the table. Those proofs take it
from the run's own test in u3at; the kind's u3at asks the same test, and
Johnson/Desc/First/Att/Claims/InRunAll.lean draws the premise out of the kind's runs' return.
At h := oldOf S gL i (Johnson/Desc/First/Att/Claims/Any.lean) the list h.t.funs is the kind's own
list, record for record.
Used of OnBytes, Johnson/Road and Inst: plain records, pure functions and lemmas on them alone; no
routine in a context and no theorem on a run: AttAt, TabAt, MatsFit, Holds, cellsK, mAt,
L5.featCell, L5.dimOf, rdW, pt, tab_read, eqTab_value, getD_extract, rowLimb_value, T_pos, dim_T,
shapedG_of_hid, pair_parts, rd2_pts, heads_pos; the library's rd2, mxV, denV, ibV, rvM6, rvIBP.
Not claimed: that a table is true.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEnds58Proofs
import Johnson.Desc.First.Att.Claims.Worth

set_option autoImplicit false

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (rd2 mxV denV ibV)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

theorem list_sum_range (n : ℕ) (f : ℕ → Kf) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ← ih, List.range_succ, List.map_append, List.sum_append]; simp

/-- **A number in nl limbs, read in a table on ah under the position weights psi.** -/
theorem shVF_rd (A : AttAt ρ W tl K3 M h lid cf fs) {t : ℕ} {psi : Array E}
    (Tb : TabAt tl h t h.S.cf.NAs h.S.T psi) {off nl J lam j : ℕ}
    (hin : ∀ l < nl, off + (l * h.S.Lam + lam) * J + j < (h.t.tabLen.lookup t).getD 0) :
    (Fo.shVF h K3 t off nl J lam j).value ρ W = ∑ l ∈ range nl, 256 ^ l *
      ∑ i ∈ range h.S.T, ρ.val (psi.getD i zeroE) *
        mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH (off + (l * h.S.Lam + lam) * J + j) i) := by
  have hT := T_pos A
  have hn : (tl.mats.getD h.S.cf.NAs {}).m / h.S.T = h.S.cf.wcH := by
    rw [A.mats.ahM, Nat.mul_div_cancel _ hT]
  have hm : h.S.cf.NAs < tl.NM := by rw [A.mats.nm]; omega
  rw [shVF_value, list_sum_range]
  refine sum_congr rfl fun l hl => ?_
  have hl' := mem_range.mp hl
  rw [rowLimb_value A.num hl']
  congr 1
  show rdW W h.iU3 K3 _ = _
  rw [tab_read A Tb hm (Nat.ne_of_gt hT) (hin l hl'), hn]
  rfl

/-- **The sum over the heads of keys and values.** -/
theorem overGF_rd (A : AttAt ρ W tl K3 M h lid cf fs) {zg : Array E} (hz : h.S.cf.lgk ≤ zg.size)
    (fv : ℕ → Aff) :
    (Fo.overGF h zg fv).value ρ W =
      ∑ g ∈ range (2 ^ h.S.cf.lgk), Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g * (fv g).value ρ W := by
  have hG := (shapedG_of_hid A.shape).G
  have hs : (zg.extract 0 h.S.cf.lgk).size = h.S.cf.lgk := by
    rw [Array.size_extract]
    omega
  rw [overGF_value, list_sum_range, hG]
  refine sum_congr rfl fun g hg => ?_
  have hg' : g < 2 ^ (zg.extract 0 h.S.cf.lgk).size := by rw [hs]; exact mem_range.mp hg
  rw [eqTab_value ρ _ g hg', hs]
  congr 1
  unfold Blocks.eqN
  refine prod_congr rfl fun k hk => ?_
  have hk' : k < h.S.cf.lgk := mem_range.mp hk
  have e : pt ρ (zg.extract 0 h.S.cf.lgk) (0 + k) = pt ρ zg (0 + k) := by
    unfold pt
    rw [Nat.zero_add, getD_extract zg hz (by omega), Nat.zero_add]
  rw [e]

/-- **A form on ah, summed over the heads, is the library's read of the array that its limbs spell.** -/
theorem limbsF_rd2 (A : AttAt ρ W tl K3 M h lid cf fs) {t : ℕ} {psi : Array E}
    (Tb : TabAt tl h t h.S.cf.NAs h.S.T psi) {zg : Array E} (hz : h.S.cf.lgk ≤ zg.size)
    {off nl J lam : ℕ} (jOf : ℕ → ℕ) (arr : ℕ → ℕ → Kf)
    (harr : ∀ g i, arr g i = ∑ l ∈ range nl, 256 ^ l *
      mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH (off + (l * h.S.Lam + lam) * J + jOf g) i))
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < nl,
      off + (l * h.S.Lam + lam) * J + jOf g < (h.t.tabLen.lookup t).getD 0) :
    (Fo.overGF h zg fun g => Fo.shVF h K3 t off nl J lam (jOf g)).value ρ W =
      rd2 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (psi.getD i zeroE)) arr := by
  rw [overGF_rd A hz]
  unfold rd2
  rw [dim_T A]
  refine sum_congr rfl fun g hg => ?_
  rw [shVF_rd A Tb (hin g (mem_range.mp hg))]
  simp only [harr, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun l _ => by
    show Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g * _ = Blocks.eqN h.S.cf.lgk 0 (pt ρ zg) g * _ * _
    ring

variable {t : ℕ} {psi zg : Array E} {lam a : ℕ}

/-- **The row maximum.** -/
theorem readMaximumF_rd2 (A : AttAt ρ W tl K3 M h lid cf fs) (Tb : TabAt tl h t h.S.cf.NAs h.S.T psi)
    (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA)
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, h.S.oMr + (l * h.S.Lam + lam) * h.S.cf.H + (g * h.S.HA + a) <
      (h.t.tabLen.lookup t).getD 0) :
    (Fo.readMaximumF h K3 t zg lam a).value ρ W =
      rd2 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (psi.getD i zeroE))
        (mxV (cellsK h.S M) (lam * h.S.HA + a)) := by
  have hb := pair_parts (lam := lam) ha
  refine limbsF_rd2 A Tb hz (fun g => g * h.S.HA + a) _ (fun g i => ?_) hin
  show ∑ k ∈ range 4, 256 ^ k * mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH
    (h.S.oMr + (k * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * h.S.cf.H +
      (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA)) i) = _
  rw [hb.1, hb.2]

/-- **The denominator.** -/
theorem readDenominatorF_rd2 (A : AttAt ρ W tl K3 M h lid cf fs)
    (Tb : TabAt tl h t h.S.cf.NAs h.S.T psi) (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA)
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, h.S.oZr + (l * h.S.Lam + lam) * h.S.cf.H + (g * h.S.HA + a) <
      (h.t.tabLen.lookup t).getD 0) :
    (Fo.readDenominatorF h K3 t zg lam a).value ρ W =
      rd2 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (psi.getD i zeroE))
        (denV (cellsK h.S M) (lam * h.S.HA + a)) := by
  have hb := pair_parts (lam := lam) ha
  refine limbsF_rd2 A Tb hz (fun g => g * h.S.HA + a) _ (fun g i => ?_) hin
  show ∑ k ∈ range 4, 256 ^ k * mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH
    (h.S.oZr + (k * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * h.S.cf.H +
      (g * h.S.HA + (lam * h.S.HA + a) % h.S.HA)) i) = _
  rw [hb.1, hb.2]

/-- **A bit of the index.** -/
theorem readIndexBitF_rd2 (A : AttAt ρ W tl K3 M h lid cf fs) (Tb : TabAt tl h t h.S.cf.NAs h.S.T psi)
    (hz : h.S.cf.lgk ≤ zg.size) (ha : a < h.S.HA) {k : ℕ}
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 1, h.S.oIb + (l * h.S.Lam + lam) * (h.S.cf.lt * h.S.cf.H) +
      (k * h.S.cf.H + g * h.S.HA + a) < (h.t.tabLen.lookup t).getD 0) :
    (Fo.readIndexBitF h K3 t zg lam a k).value ρ W =
      rd2 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val (psi.getD i zeroE))
        (ibV (cellsK h.S M) k (lam * h.S.HA + a)) := by
  have hb := pair_parts (lam := lam) ha
  refine limbsF_rd2 A Tb hz (fun g => k * h.S.cf.H + g * h.S.HA + a) _ (fun g i => ?_) hin
  show mAt M (L5.featCell h.S h.S.cf.NAs h.S.cf.wcH
    (h.S.oIb + (0 * h.S.Lam + (lam * h.S.HA + a) / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
      (k * h.S.cf.H + g * h.S.HA + (lam * h.S.HA + a) % h.S.HA)) i) = _
  rw [hb.1, hb.2, sum_range_one, pow_zero, one_mul]

/-! ### the twins of two statements of Johnson/Road/Rows on end values -/

open Inst.Model.AttSeg (Pub rvM6 rvIBP)

/-- **The twin of ScoreStartEnd**: the value sent for the row maximum of pair b is the library's rvM6. -/
theorem score_start (A : AttAt ρ W tl K3 M h lid cf fs) (htg : h.x.tg.size = h.S.cf.lgk)
    (hti : h.x.ti.size = h.S.cf.lt) {b : ℕ} (hb : b < h.S.NP) {p : Pub Kf}
    (hpg : ∀ j < h.S.cf.lgk, pt ρ h.x.tg j = p.tg j) (hpi : ∀ j < h.S.cf.lt, pt ρ h.x.ti j = p.ti j)
    (Tb : AhAt tl h h.t.hT (eqTab h.x.ti))
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, h.S.oMr + (l * h.S.Lam + b / h.S.HA) * h.S.cf.H +
      (g * h.S.HA + b % h.S.HA) < (h.t.tabLen.lookup h.t.hT).getD 0)
    (hval : W.slot (h.x.sM6 + b) =
      (Fo.readMaximumF h K3 h.t.hT h.x.tg (b / h.S.HA) (b % h.S.HA)).value ρ W) :
    W.slot (h.x.sM6 + b) = rvM6 (L5.dimOf h.S) p (cellsK h.S M) b := by
  have e := readMaximumF_rd2 A Tb (Nat.le_of_eq htg.symm) (Nat.mod_lt b (heads_pos hb)) hin
  rw [Nat.div_add_mod'] at e
  rw [hval, e]
  exact rd2_pts A hti hpg hpi _

/-- **The twin of KeyAtIndexEndB**: the end value for bit k of pair b in the key's sumcheck is the library's rvIBP. -/
theorem key_bits (A : AttAt ρ W tl K3 M h lid cf fs) (hr : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk)
    {b k : ℕ} (hb : b < h.S.NP) (Tb : AhAt tl h h.t.hPi (eqTab (h.x.pi h.S)))
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 1, h.S.oIb + (l * h.S.Lam + b / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
      (k * h.S.cf.H + g * h.S.HA + b % h.S.HA) < (h.t.tabLen.lookup h.t.hPi).getD 0)
    (hval : W.slot (h.x.sIb h.S b k) =
      (Fo.readIndexBitF h K3 h.t.hPi (h.x.pg h.S) (b / h.S.HA) (b % h.S.HA) k).value ρ W) :
    W.slot (h.x.sIb h.S b k) = rvIBP (L5.dimOf h.S) (cellsK h.S M) (pt ρ h.x.scd.r) b k := by
  have hlT := dim_lT A
  have s1 : (h.x.pg h.S).size = h.S.cf.lgk := by
    show (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s2 : (h.x.pi h.S).size = h.S.cf.lt := by
    show (h.x.scd.r.extract (h.S.cf.lt + h.S.cf.lgk) (2 * h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have e := readIndexBitF_rd2 A Tb (Nat.le_of_eq s1.symm) (Nat.mod_lt b (heads_pos hb)) hin
  rw [Nat.div_add_mod'] at e
  rw [hval, e]
  refine rd2_pts A s2 (fun j hj => ?_) (fun j hj => ?_) _
  · show pt ρ (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j =
      pt ρ h.x.scd.r ((L5.dimOf h.S).lT + j)
    rw [hlT]
    exact pt_extract ρ _ (by omega) (by omega)
  · show pt ρ (h.x.scd.r.extract (h.S.cf.lt + h.S.cf.lgk) (2 * h.S.cf.lt + h.S.cf.lgk)) j =
      pt ρ h.x.scd.r ((L5.dimOf h.S).lT + h.S.cf.lgk + j)
    rw [hlT]
    exact pt_extract ρ _ (by omega) (by omega)

end K5Law
