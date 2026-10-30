-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/AgreeKind.lean: kind K5: an entry of the verifier's vector of tables,
at the place of a listed name, is what the library means the late entry of that name to be
(TabW.form, Cb/Pv/Att/End/Tabs.lean): by the kind of the table.

Main names:
  `uAt_eq`: the late entries read off the world (uAt, Johnson/Desc/First/Att/Claims/PortDict.lean)
    are those of Johnson/Road/Rows/AttPortWitN.lean, by definition.
  `agree_row`: a table on single features of the matrix ah. `agree_long`: a table on blocks of
    features of qa or of ao. `agree_col`: a table on the matrix as.
Each takes: AttAt (Johnson/Road/Rows/AttRead.lean: every table of the list is true of the matrices M
in the world W; the list of matrices fits); that the table lies in the list with its weights (TabAt,
AsAt); that these weights read as the library's; that the name's place lies in the table; that the
early entry of each cell under the name is M's entry at the cell's address.
By tab_read and as_read (Johnson/Road/Rows/AttReadLaws.lean) and names_row, names_qa, names_tO,
names_col (Johnson/Road/Rows/AttLayNames.lean). Of OnBytes and Johnson/Road no routine that runs in
a context is named, and no theorem on such a routine's return; the runs spoken of are the kind's own
(Johnson/Desc/First/Att/RunsP.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttLayNames
import Johnson.Road.Rows.AttReadRow
import Johnson.Road.Rows.AttPortWitN
import Johnson.Desc.First.Att.Claims.PortDict

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (Raw)
open Cb.Pv.Att.End (AttTab TabW namesOf LateLay val_aSum val_aSmul val_aEnt)

/-- The late entries read off the world are those of Johnson/Road/Rows/AttPortWitN.lean. -/
theorem uAt_eq {Kf J₂ : Type} (W : World Kf) (h : Attention.Heard) (K3 : ℕ) (Y : LateLay AttTab J₂)
    (tabOf : AttTab → ℕ) (place : AttTab → Raw → ℕ) :
    uAt W h K3 Y tabOf place = OnBytes.Road.Rows.uAt W h K3 Y tabOf place := rfl

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
  {J₁ : Type} [Fintype J₁] [DecidableEq J₁] {cellJ : Raw → J₁} {x : J₁ → Kf}

/-- **A table on single features of ah**: the vector's entry at a listed name's place is what the library means the late entry of that name to be. Ψ: the library's weights on the positions. -/
theorem agree_row (A : AttAt ρ W tl K3 M h lid cf fs) {T : AttTab} (hT : T ∈ rowTabs) {t : ℕ}
    {phi : Array E} (Tb : TabAt tl h t h.S.cf.NAs h.S.T phi) {Ψ : ℕ → Kf}
    (hw : ∀ i < h.S.T, ρ.val (phi.getD i zeroE) = Ψ i) {r : Raw}
    (hr : r ∈ namesOf (L5.dimOf h.S) h.S.ls h.S.cf.lmS T)
    (hx : placeAtt h.S T r < (h.t.tabLen.lookup t).getD 0)
    (hc : ∀ k < h.S.T, x (cellJ (r.atPos k)) = cellsK h.S M (r.atPos k)) :
    rdW W h.iU3 K3 (t + placeAtt h.S T r) =
      ((TabW.row Ψ).form cellJ (L5.dimOf h.S) h.S.ls h.S.cf.lmS r).val x := by
  have Z := sizes_of_hid A.shape
  have hTp : 0 < h.S.T := by rw [Z.T]; exact Nat.two_pow_pos _
  rw [tab_read A Tb (by rw [A.mats.nm]; omega) (Nat.pos_iff_ne_zero.mp hTp) hx, A.mats.ahM,
    Nat.mul_div_cancel _ hTp]
  unfold TabW.form
  rw [val_aSum, dim_T A]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [val_aSmul, val_aEnt, hw i hi', hc i hi']
  unfold cellsK mAt
  rw [names_row h.S hT hr i]

/-- **A table on blocks of features** (of qa, or of ao): likewise. lw, Ψ: the library's weights on the features of a block and on the positions; xp: the name's place; haddr: where the entry's cells lie (names_qa, names_tO). -/
theorem agree_long (A : AttAt ρ W tl K3 M h lid cf fs) {t mat wc : ℕ} {low tok : Array E}
    (Tb : TabAt tl h t mat (2 ^ h.S.cf.la) (blockRows low tok)) (hm : mat < tl.NM)
    (hM : (tl.mats.getD mat {}).m = wc * h.S.T) (hwc : wc % 2 ^ h.S.ls = 0)
    (hlow : low.size = 2 ^ h.S.ls) (htok : tok.size = h.S.T) {lw Ψ : ℕ → Kf}
    (hl : ∀ c < 2 ^ h.S.ls, ρ.val (low.getD c zeroE) = lw c)
    (hΨ : ∀ i < h.S.T, ρ.val (tok.getD i zeroE) = Ψ i) {r : Raw} {xp : ℕ}
    (hx : xp < (h.t.tabLen.lookup t).getD 0)
    (haddr : ∀ k < 2 ^ h.S.ls * h.S.T, L5.addrA h.S ((r.addN (k / h.S.T)).atPos (k % h.S.T)) =
      (mat, xp % (wc / 2 ^ h.S.ls) * (2 ^ h.S.ls * h.S.T) + k, xp / (wc / 2 ^ h.S.ls)))
    (hc : ∀ c < 2 ^ h.S.ls, ∀ i < h.S.T,
      x (cellJ ((r.addN c).atPos i)) = cellsK h.S M ((r.addN c).atPos i)) :
    rdW W h.iU3 K3 (t + xp) = ((TabW.long lw Ψ).form cellJ (L5.dimOf h.S) h.S.ls h.S.cf.lmS r).val x := by
  have Z := sizes_of_hid A.shape
  have hP : 0 < 2 ^ h.S.ls := Nat.two_pow_pos _
  have hT : 0 < h.S.T := by rw [Z.T]; exact Nat.two_pow_pos _
  have hla : 2 ^ h.S.cf.la = 2 ^ h.S.ls * h.S.T := by rw [Z.la, pow_add, Z.T]
  obtain ⟨wb, hwb⟩ := Nat.dvd_of_mod_eq_zero hwc
  have hn : (tl.mats.getD mat {}).m / 2 ^ h.S.cf.la = wb := by
    rw [hM, hla, hwb, show 2 ^ h.S.ls * wb * h.S.T = wb * (2 ^ h.S.ls * h.S.T) by ring]
    exact Nat.mul_div_cancel _ (Nat.mul_pos hP hT)
  have hwd : wc / 2 ^ h.S.ls = wb := by rw [hwb]; exact Nat.mul_div_cancel_left _ hP
  rw [tab_read A Tb hm (Nat.ne_of_gt (Nat.two_pow_pos _)) hx, hn, hla, Alg.sum_range_mul_add]
  unfold TabW.form
  rw [val_aSum]
  refine sum_congr rfl fun c hc' => ?_
  rw [val_aSum, dim_T A]
  refine sum_congr rfl fun i hi => ?_
  have hc'' := mem_range.mp hc'
  have hi' := mem_range.mp hi
  have e := blockRows_getD low tok (r := c) (i := i) (by rw [hlow]; exact hc'') (by rw [htok]; exact hi')
  rw [htok] at e
  rw [e, ρ.mul, val_aSmul, val_aEnt, hl c hc'', hΨ i hi', hc c hc'' i hi']
  have hk : c * h.S.T + i < 2 ^ h.S.ls * h.S.T := by
    calc c * h.S.T + i < c * h.S.T + h.S.T := by omega
      _ = (c + 1) * h.S.T := by ring
      _ ≤ 2 ^ h.S.ls * h.S.T := Nat.mul_le_mul_right _ hc''
  have a := haddr (c * h.S.T + i) hk
  rw [show (c * h.S.T + i) / h.S.T = c by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hT, Nat.div_eq_of_lt hi', Nat.zero_add],
    show (c * h.S.T + i) % h.S.T = i by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi'], hwd] at a
  unfold cellsK mAt
  rw [a]

/-- **A table on the matrix as**: likewise. ph: the library's weights on the cells of an entry. -/
theorem agree_col (A : AttAt ρ W tl K3 M h lid cf fs) {T : AttTab} (hT : T ∈ colTabs) {t : ℕ}
    {phi : Array E} (Tb : AsAt h t phi) {ph : ℕ → Kf}
    (hw : ∀ k < 2 ^ h.S.cf.lmS, ρ.val (phi.getD k zeroE) = ph k) {r : Raw}
    (hr : r ∈ namesOf (L5.dimOf h.S) h.S.ls h.S.cf.lmS T)
    (hx : placeAtt h.S T r < (h.t.tabLen.lookup t).getD 0)
    (hc : ∀ k < 2 ^ h.S.cf.lmS, x (cellJ (r.addX k)) = cellsK h.S M (r.addX k)) :
    rdW W h.iU3 K3 (t + placeAtt h.S T r) =
      ((TabW.col ph).form cellJ (L5.dimOf h.S) h.S.ls h.S.cf.lmS r).val x := by
  have N := norm_of_hid A.shape
  have Z := sizes_of_hid A.shape
  rw [as_read A Tb hx]
  unfold TabW.form
  rw [val_aSum]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  rw [val_aSmul, val_aEnt, hw k hk', hc k hk']
  unfold cellsK mAt
  rw [names_col h.S N Z hT hr hk']

end K5Law
