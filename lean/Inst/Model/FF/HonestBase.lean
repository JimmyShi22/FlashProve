-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/HonestBase.lean: the honest trace of a feed-forward segment, part 1: the values of
  the arrays and accumulators of Inst/Model/FF/Trace.lean on it.

  The honest trace is `hon` (Inst/Model/FF/Trace.lean): the cells of the value of every array, by
  the definitions of the integer program (Inst/Model/Program.lean), from a given stream x and given
  outputs o of attention. The main statement is `val_hon`: on the honest trace `val` gives every
  array, at every name, its honest value `hv`; it has no hypothesis.
    Part 1  `val_hon`; the stream, its cells, the ledger (`xS_hon`, `bS_hon`, `led_hon`)
    Part 2  layers with experts, routed units, shifts: the segment's and the program's agree if L0
            is even
    Part 3  the accumulators formed from the cells (`Aq`, .., `Ad`, Inst/Model/FF/Trace.lean) are
            the program's: the projections, the rotation, gate and up of a hidden unit (for the
            routed expert the sum over the experts collapses to the selected one), the down
            projection; gate, up and down: if L0 is even and there is at least one expert
  The sizes D are not fixed. Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean,
  Inst/Model/FF/Index.lean). A theorem marked "omit scl in" reads no scale.
-/
import Inst.Model.FF.Trace
import Inst.Model.Common.Router

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg.Hon

variable [scl : Scl]

open Finset

variable (D : Dim) (tb : Tables) (w : ℕ → LayerW) (L0 : ℕ) (x o : ℕ → ℕ → Vec)

local notation "H" => hon D tb w L0 x o
local notation "HV" => hv D tb w L0 x o
local notation "WR" => fun l => LW.ofInt ℤ (w l)

/-! ## Part 1. The values of the arrays -/

omit scl in
theorem nCell_pos (X : Arr) : 1 ≤ X.nCell := by cases X <;> decide

/-- On the honest trace, `val` gives every array its honest value. -/
theorem val_hon (X : Arr) (n j i : ℕ) : val H X n j i = HV X n j i := by
  have h := sum_cellW (nCell_pos X) (HV X n j i - X.off)
  unfold val
  simp only [hon, Int.cast_id]
  rw [h]
  ring

theorem xS_hon (s j i : ℕ) : xS D H s j i = x s i j := by
  unfold xS streamAt
  rw [val_hon]
  split_ifs with h0 h1
  · rw [h0]; rfl
  · rw [h1]; rfl
  · show x (s - 1 + 1) i j = _
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]

theorem bS_hon (s l j i : ℕ) : bS D H s l j i = cellW 5 (x s i j) l := by
  unfold bS streamAt
  split_ifs with h0 h1
  · rw [h0]
    show cellW 5 (x 0 i j - 0) l = _
    rw [sub_zero]
  · rw [h1]
    show cellW 5 (x (2 * D.nl) i j - 0) l = _
    rw [sub_zero]
  · show cellW 5 (x (s - 1 + 1) i j - 0) l = _
    rw [sub_zero, Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]

theorem led_hon (ν i : ℕ) :
    led H ν i = Ledger.hon (npOf D ν) D.d fun l j => cellW 5 (x ν i j) l := by
  funext n
  exact val_hon D tb w L0 x o .D ν n i

omit scl in
/-- the value that the five cells of a value represent -/
theorem xOf_cells (y : Vec) : Ledger.xOf (fun l j => cellW 5 (y j) l) = y := by
  funext j
  exact sum_cellW (by norm_num) _

/-! ## Part 2. Layers with experts, routed units, shifts -/

section Parity

variable {L0} (hL : L0 % 2 = 0)
include hL

omit scl in
theorem isExpL_iff (l : ℕ) : isExpL l = true ↔ hasExperts (L0 + l) := by
  unfold isExpL hasExperts
  rw [beq_iff_eq]
  omega

theorem routed_iff (l y : ℕ) : routed D l y = true ↔ FF.routed (D.Pl l) (L0 + l) y := by
  unfold routed FF.routed
  rw [Bool.and_eq_true, isExpL_iff hL, decide_eq_true_iff]
  rfl

theorem kG_eq (l y : ℕ) : kG D l y = FF.kG (D.Pl l) (L0 + l) y := by
  unfold kG FF.kG
  by_cases h : routed D l y = true
  · rw [if_pos h, if_pos ((routed_iff D hL l y).1 h)]
  · rw [if_neg h, if_neg fun h' => h ((routed_iff D hL l y).2 h')]

theorem kU_eq (l y : ℕ) : kU D l y = FF.kU (D.Pl l) (L0 + l) y := by
  unfold kU FF.kU
  by_cases h : routed D l y = true
  · rw [if_pos h, if_pos ((routed_iff D hL l y).1 h)]
  · rw [if_neg h, if_neg fun h' => h ((routed_iff D hL l y).2 h')]

end Parity

omit scl in
/-- an odd layer is the layer of its router instance -/
theorem odd_layer {l : ℕ} (h : isExpL l = true) :
    2 * (l / 2) + 1 = l ∧ 4 * (l / 2) + 3 = 2 * l + 1 := by
  unfold isExpL at h
  rw [beq_iff_eq] at h
  omega

/-! ## Part 3. The accumulators -/

theorem Aq_hon (l c i : ℕ) : Aq D H WR l c i = Att.Aq (D.Pl l) (w l) (x (2 * l)) i c := by
  unfold Aq Att.Aq dot
  exact sum_congr rfl fun j _ => by rw [val_hon]; simp only [LW.ofInt, Int.cast_id]; rfl

theorem Ak_hon (l c i : ℕ) : Ak D H WR l c i = Att.Ak (D.Pl l) (w l) (x (2 * l)) i c := by
  unfold Ak Att.Ak dot
  exact sum_congr rfl fun j _ => by rw [val_hon]; simp only [LW.ofInt, Int.cast_id]; rfl

theorem Av_hon (l c i : ℕ) : Av D H WR l c i = Att.Av (D.Pl l) (w l) (x (2 * l)) i c := by
  unfold Av Att.Av dot
  exact sum_congr rfl fun j _ => by rw [val_hon]; simp only [LW.ofInt, Int.cast_id]; rfl

theorem AY_hon (l c i : ℕ) : AY D H WR l c i = Att.AY (D.Pl l) (w l) (x (2 * l)) i c := by
  unfold AY Att.AY
  rw [Aq_hon, Ak_hon]
  rfl

theorem Y'_hon (l c i : ℕ) :
    Y' D H tb L0 WR l c i = Att.Y' (D.Pl l) tb (w l) (L0 + l) (x (2 * l)) i c := by
  unfold Y' Att.Y'
  simp only [AY_hon, Int.cast_id]
  rfl

theorem hh_hon (l j i : ℕ) : hh H l j i = FF.hh (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i j := by
  unfold hh
  rw [val_hon, val_hon]
  rfl

/-- On the honest trace, in a layer with experts and if there is at least one expert, the sum over
the experts, weighted with the selection, is the term of the selected expert -/
theorem sum_sel (hnx : 0 < D.nx) {l : ℕ} (he : isExpL l = true) (i : ℕ) (F : ℕ → ℤ) :
    ∑ e ∈ range D.nx, val H .sel (l / 2) e i * F e =
      F (FF.es (D.Pl l) (w l) (x (2 * l + 1)) i) := by
  obtain ⟨e1, e2⟩ := odd_layer he
  have hes : FF.es (D.Pl l) (w l) (x (2 * l + 1)) i < D.nx := by
    have := (Router.argTo_spec' (FF.lr (D.Pl l) (w l) (x (2 * l + 1)) i) ((D.Pl l).nexp - 1)).1
    unfold FF.es
    have h2 : D.nx = (D.Pl l).nexp := rfl
    omega
  refine Router.sum_indicator_mul hes (fun e _ => ?_) F
  rw [val_hon]
  show (if e = FF.es (D.Pl (2 * (l / 2) + 1)) (w (2 * (l / 2) + 1)) (x (4 * (l / 2) + 3)) i then
        (1 : ℤ)
      else 0) = _
  rw [e1, e2]

section Units

variable {L0} (hL : L0 % 2 = 0) (hnx : 0 < D.nx)
include hL hnx

theorem Ag_hon (l y i : ℕ) :
    Ag D H WR l y i =
      dot D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i y)
        (FF.wg (D.Pl l) (w l) (L0 + l) (x (2 * l + 1)) i y) := by
  unfold Ag dot FF.z FF.wg
  by_cases h : routed D l y = true
  · have hr := (routed_iff D hL l y).1 h
    have he : isExpL l = true := by unfold routed at h; exact (Bool.and_eq_true _ _ ▸ h).1
    obtain ⟨e1, e2⟩ := odd_layer he
    rw [if_pos h, sum_sel D tb w L0 x o hnx he]
    refine sum_congr rfl fun j _ => ?_
    rw [val_hon, if_pos hr, if_pos hr]
    simp only [LW.ofInt, Int.cast_id]
    show FF.xr (D.Pl (2 * (l / 2) + 1)) tb (w (2 * (l / 2) + 1)) (x (4 * (l / 2) + 3)) i j * _ = _
    rw [e1, e2]
    rfl
  · have hr : ¬ FF.routed (D.Pl l) (L0 + l) y := fun h' => h ((routed_iff D hL l y).2 h')
    rw [if_neg h]
    refine sum_congr rfl fun j _ => ?_
    rw [val_hon, if_neg hr, if_neg hr]
    simp only [LW.ofInt, Int.cast_id]
    rfl

theorem Au_hon (l y i : ℕ) :
    Au D H WR l y i =
      dot D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i y)
        (FF.wu (D.Pl l) (w l) (L0 + l) (x (2 * l + 1)) i y) := by
  unfold Au dot FF.z FF.wu
  by_cases h : routed D l y = true
  · have hr := (routed_iff D hL l y).1 h
    have he : isExpL l = true := by unfold routed at h; exact (Bool.and_eq_true _ _ ▸ h).1
    obtain ⟨e1, e2⟩ := odd_layer he
    rw [if_pos h, sum_sel D tb w L0 x o hnx he]
    refine sum_congr rfl fun j _ => ?_
    rw [val_hon, if_pos hr, if_pos hr]
    simp only [LW.ofInt, Int.cast_id]
    show FF.xr (D.Pl (2 * (l / 2) + 1)) tb (w (2 * (l / 2) + 1)) (x (4 * (l / 2) + 3)) i j * _ = _
    rw [e1, e2]
    rfl
  · have hr : ¬ FF.routed (D.Pl l) (L0 + l) y := fun h' => h ((routed_iff D hL l y).2 h')
    rw [if_neg h]
    refine sum_congr rfl fun j _ => ?_
    rw [val_hon, if_neg hr, if_neg hr]
    simp only [LW.ofInt, Int.cast_id]
    rfl

theorem Ad_hon (l c i : ℕ) :
    Ad D H WR l c i = FF.Ad (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i c := by
  unfold Ad FF.Ad FF.units
  by_cases he : isExpL l = true
  · have hx := (isExpL_iff hL l).1 he
    rw [if_pos he, if_pos hx, sum_sel D tb w L0 x o hnx he, Dim.Pl_fe,
      show 2 * D.P.fe = D.P.fe + D.P.fe from two_mul _, sum_range_add]
    congr 1
    · refine sum_congr rfl fun j hj => ?_
      have hr : ¬ FF.routed (D.Pl l) (L0 + l) j := fun h' => by
        have h1 : D.P.fe ≤ j := h'.2
        have h2 : j < D.P.fe := mem_range.1 hj
        omega
      rw [hh_hon, if_neg hr]
      simp only [LW.ofInt, Int.cast_id]
    · refine sum_congr rfl fun j _ => ?_
      have hr : FF.routed (D.Pl l) (L0 + l) (D.P.fe + j) := ⟨hx, Nat.le_add_right _ _⟩
      rw [hh_hon, if_pos hr, Nat.add_sub_cancel_left]
      simp only [LW.ofInt, Int.cast_id]
      rfl
  · have hx : ¬ hasExperts (L0 + l) := fun h' => he ((isExpL_iff hL l).2 h')
    rw [if_neg he, if_neg hx]
    refine sum_congr rfl fun j _ => ?_
    have hr : ¬ FF.routed (D.Pl l) (L0 + l) j := fun h' => hx h'.1
    rw [hh_hon, if_neg hr]
    simp only [LW.ofInt, Int.cast_id]

end Units

end Inst.Model.FFSeg.Hon
