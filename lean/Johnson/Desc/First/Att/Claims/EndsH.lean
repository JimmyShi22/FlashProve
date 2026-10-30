-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/EndsH.lean: kind K5: twins, for the written forms, of BitsEndA and
BitsEndB (Johnson/Road/Rows/AttEnds58.lean; proved in Johnson/Road/Rows/AttEnds58Proofs.lean, the
first of a run in a context): the end values of "the index's cells are bits" (the reader endsH of
Johnson/Desc/First/Att/Claims/Say58.lean). The pure parts of the proof follow that proof line for
line.

Main names:
  `bitsF_ext`: the weighted bits of pair b's index (bitsF) are worth the extension of the library's
    bitCube, with 4 bits that number a bit, at the sumcheck's own point.
  `bits_ends`: under what claim 8 says (Say8.ends): W.slot (scH.sEnd + 2 b) = that extension; W.slot
    (scH.sEnd + (2 b + 1)) = the same less 1.
What these reach, and what not: as the head of Johnson/Desc/First/Att/Claims/EndsQ.lean says.
Premise beyond those of Johnson/Road/Rows: the indices read lie in the table.
Used: as Johnson/Desc/First/Att/Claims/MeanRd.lean, and AhAt, L5.shape_of_hid, L5.shaped_of_hid,
lt_le_16, eqN_agree, bitCube_ext, Cb.Pv.Att.bitCube.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.MeanRd

set_option autoImplicit false

namespace K5Law
open Cb.Pv.Att
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Dim rd2 eqT sh ibV)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- **The weighted bits of pair b's index are the extension of the library's bitCube.** -/
theorem bitsF_ext (A : AttAt ρ W tl K3 M h lid cf fs) (hr : h.x.scH.r.size = h.S.nvH) {b : ℕ}
    (hb : b < h.S.NP) (Tb : AhAt tl h h.t.hR2 (eqTab (h.x.ri2 h.S)))
    (hin : ∀ k < h.S.cf.lt, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 1,
      h.S.oIb + (l * h.S.Lam + b / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
        (k * h.S.cf.H + g * h.S.HA + b % h.S.HA) < (h.t.tabLen.lookup h.t.hR2).getD 0) :
    (bitsF h K3 b).value ρ W =
      Blocks.ext ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg + 4)
        (bitCube 4 (L5.dimOf h.S) (cellsK h.S M) b) (pt ρ h.x.scH.r) := by
  have hlT := dim_lT A
  obtain ⟨S0, hS0⟩ := L5.shape_of_hid A.shape
  have h16 : h.S.cf.lt ≤ 16 := by
    rw [(L5.shaped_of_hid A.shape).cfg]
    exact lt_le_16 hS0
  have hr' : h.x.scH.r.size = h.S.cf.lt + h.S.cf.lgk + 4 := hr
  have s1 : (h.x.rg2 h.S).size = h.S.cf.lgk := by
    show (h.x.scH.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s2 : (h.x.ri2 h.S).size = h.S.cf.lt := by
    show (h.x.scH.r.extract 0 h.S.cf.lt).size = _
    rw [size_cut _ (by omega)]
    omega
  have s3 : (h.x.rk h.S).size = 4 := by
    show (h.x.scH.r.extract (h.S.cf.lt + h.S.cf.lgk) (h.S.cf.lt + h.S.cf.lgk + 4)).size = _
    rw [size_cut _ (by omega)]
    omega
  have ha := Nat.mod_lt b (heads_pos hb)
  unfold bitsF
  rw [foldl_pos ρ W _ (fun k => (eqTab (h.x.rk h.S)).getD k zeroE), Aff.value_ofConst, ρ.zero, zero_add,
    list_sum_range, bitCube_ext (L5.dimOf h.S) (cellsK h.S M) 4 (by rw [hlT]; omega) b, hlT]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < h.S.cf.lt := mem_range.mp hk
  have a3 := readIndexBitF_rd2 A Tb (Nat.le_of_eq s1.symm) ha (hin k hk')
  rw [Nat.div_add_mod'] at a3
  have w1 : ρ.val ((eqTab (h.x.rk h.S)).getD k zeroE) =
      Blocks.eqN 4 0 (sh (pt ρ h.x.scH.r) ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg)) k := by
    rw [eqTab_value ρ _ k (by rw [s3]; omega), s3]
    refine eqN_agree (fun j hj => ?_) k
    show pt ρ (h.x.scH.r.extract (h.S.cf.lt + h.S.cf.lgk) (h.S.cf.lt + h.S.cf.lgk + 4))
      (0 + j) = pt ρ h.x.scH.r ((L5.dimOf h.S).lT + h.S.cf.lgk + (0 + j))
    rw [hlT, Nat.zero_add]
    exact pt_extract ρ _ (by omega) (by omega)
  have w2 : rd2 (L5.dimOf h.S) (pt ρ (h.x.rg2 h.S))
      (fun i => ρ.val ((eqTab (h.x.ri2 h.S)).getD i zeroE)) (ibV (cellsK h.S M) k b) =
      rd2 (L5.dimOf h.S) (sh (pt ρ h.x.scH.r) (L5.dimOf h.S).lT)
        (eqT (L5.dimOf h.S) (pt ρ h.x.scH.r)) (ibV (cellsK h.S M) k b) := by
    refine rd2_pts A s2 (fun j hj => ?_) (fun j hj => ?_) _
    · show pt ρ (h.x.scH.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j =
        pt ρ h.x.scH.r ((L5.dimOf h.S).lT + j)
      rw [hlT]
      exact pt_extract ρ _ (by omega) (by omega)
    · show pt ρ (h.x.scH.r.extract 0 h.S.cf.lt) j = pt ρ h.x.scH.r j
      rw [pt_extract ρ _ (by omega) (by omega), Nat.zero_add]
  rw [w1, a3, w2, hlT]

/-- **The end values of "the index's cells are bits", under what claim 8 says.** -/
theorem bits_ends (A : AttAt ρ W tl K3 M h lid cf fs) (hr : h.x.scH.r.size = h.S.nvH) {b : ℕ}
    (hb : b < h.S.NP) (Tb : AhAt tl h h.t.hR2 (eqTab (h.x.ri2 h.S)))
    (hin : ∀ k < h.S.cf.lt, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 1,
      h.S.oIb + (l * h.S.Lam + b / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
        (k * h.S.cf.H + g * h.S.HA + b % h.S.HA) < (h.t.tabLen.lookup h.t.hR2).getD 0)
    (S8 : Say8 ρ W h K3) :
    W.slot (h.x.scH.sEnd + 2 * b) =
        Blocks.ext ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg + 4)
          (bitCube 4 (L5.dimOf h.S) (cellsK h.S M) b) (pt ρ h.x.scH.r) ∧
      W.slot (h.x.scH.sEnd + (2 * b + 1)) =
        Blocks.ext ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg + 4)
          (bitCube 4 (L5.dimOf h.S) (cellsK h.S M) b) (pt ρ h.x.scH.r) - 1 := by
  have e := bitsF_ext A hr hb Tb hin
  have a := S8.ends (2 * b) (by omega)
  have c := S8.ends (2 * b + 1) (by omega)
  unfold endsH at a c
  rw [if_pos (by omega), show 2 * b / 2 = b by omega, e] at a
  rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, Aff.value_sub, Aff.value_ofConst, ρ.one, e] at c
  exact ⟨a, c⟩

end K5Law
