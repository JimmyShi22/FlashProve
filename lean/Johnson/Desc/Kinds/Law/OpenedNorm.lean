-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OpenedNorm.lean: "OPENED AT THE TRUTH", THE FINAL NORMALIZATION's HALF: the converse of the reading that the norm's
laws make. Where the cells are honest and the hidden scalars that the norm's hearings left ARE THE TRUE ONES, ALL 29
FORMS of the run "norm" (FinalNorm.forms: 3 of the squares, 6 of the products, the row's 17, 3 of "normed") are
worth 0 in a world with true reads. No chance in it. FOR A MEMBER OF K06_law: an honest tape plugs in at NormTruthW's
letters, which are IN THE LAWS' OWN TABLES.
  NormTruthW W c   BY LETTERS: the nine hidden sums and the seven hidden products are the bridge's true extensions at pV
        (sumWAt, prodRAt) · both end values of the squares' level are the table sqTab's extension at its
        challenges · the products' claimed sum is the batch of the true extensions; its four end values are the
        extensions of the row's four fields (fieldK) at its challenges · normed's two end values are the tables
        AtN, BtN at its challenges · THE THREE SUMCHECKS' OWN FORMS, on the end values as shown, ARE WORTH 0.
  the cells        (dataOf c).Holds: every one of the 17 identities at every position (the bridge's word; it gives the
        clause rows of CellRelN: rows_of_holds, Law/NormJoint.lean; the converse is not used here).
  opened_norm      under these, true reads (NormReads, NormedReads) and the sizes: every form of FinalNorm.forms is worth 0.
THE VALUES OF THE FORMS' RIGHT SIDES ARE CUT OUT OF THE SOUNDNESS PROOFS, where they stood inline: field_values:
products_law (Law/NormProducts.lean) · streams_value: squares_end0 (Law/NormSquares.lean) · recip_value |
stream_value: normed_at (Law/Normed.lean): their lines, with the end value's form taken off. The row's 17:
lines_iff_of_true (NormBridge/BridgeCore.lean) and rowForms_valuesW (Law/NormJoint.lean), read backward.
WHAT IT IS NOT. Nothing on soundness. THAT ANY TAPE MEETS NormTruthW IS NOT SHOWN HERE. That honest cells exist: not here. The
values are in K (val W): the step to "atWorld ... = 0" at the ledger's world is not made in this file.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NormRows

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Aff Reading World Fork)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits)
open OnBytes.Desc.First.P1 (mle)
open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)
open Came (val val_sub val_add val_sumTo val_smulE val_natCast mle_point AtN BtN spr_swap spr_sum
  blocks_spr ledgerR UN)
open D6.Bridge (Data)

variable [Sizes] [Policy] [Request] [Token]

section Values
variable [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]

/-- The row's four fields through a true read at a point r: the fields' extensions there. -/
theorem field_values (c : NCells) (W : World K) (D' : Nat → Form) (r : Point)
    (hD : ∀ j, j < NR → val W (D' j) = Blocks.ext lt (fun t => dK c t j) (ptK r)) :
    val W (P6.Row.ofDigits D').a = Blocks.ext lt (fieldK c 0) (ptK r) ∧
    val W (P6.Row.ofDigits D').b = Blocks.ext lt (fieldK c 1) (ptK r) ∧
    val W (P6.Row.ofDigits D').Rlo = Blocks.ext lt (fieldK c 2) (ptK r) ∧
    val W (P6.Row.ofDigits D').Rhi = Blocks.ext lt (fieldK c 3) (ptK r) := by
  have hdv : ∀ j, j < 99 → OnBytes.Desc.First.P6.dv Reading.gl W D' j =
      Blocks.ext lt (fun t => dK c t j) (ptK r) := fun j hj => hD j hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Aff.value Reading.gl W (P6.Row.ofDigits D').a = _
    rw [OnBytes.Desc.First.P6.a_value]
    show _ = Blocks.ext lt (fun t => Inst.Model.Ledger.sa (dK c t)) (ptK r)
    rw [Inst.Model.Ledger.ext_sa lt (fun m t => dK c t m) (ptK r)]
    unfold Inst.Model.Ledger.sa
    rw [hdv 58 (by omega), hdv 59 (by omega), hdv 60 (by omega), hdv 61 (by omega)]
  · show Aff.value Reading.gl W (P6.Row.ofDigits D').b = _
    rw [OnBytes.Desc.First.P6.b_value]
    show _ = Blocks.ext lt (fun t => Inst.Model.Ledger.sb (dK c t)) (ptK r)
    rw [Inst.Model.Ledger.ext_sb lt (fun m t => dK c t m) (ptK r)]
    unfold Inst.Model.Ledger.sb
    rw [hdv 62 (by omega), hdv 63 (by omega)]
  · show Aff.value Reading.gl W (P6.Row.ofDigits D').Rlo = _
    rw [OnBytes.Desc.First.P6.Rlo_value]
    show _ = Blocks.ext lt (fun t => Inst.Model.Ledger.Rlo (dK c t)) (ptK r)
    rw [Inst.Model.Ledger.ext_Rlo lt (fun m t => dK c t m) (ptK r)]
    unfold Inst.Model.Ledger.Rlo Inst.Model.Ledger.b256
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hdv (80 + l) (by have := Finset.mem_range.mp hl; omega)]
  · show Aff.value Reading.gl W (P6.Row.ofDigits D').Rhi = _
    rw [OnBytes.Desc.First.P6.Rhi_value]
    show _ = Blocks.ext lt (fun t => Inst.Model.Ledger.Rhi (dK c t)) (ptK r)
    rw [Inst.Model.Ledger.ext_Rhi lt (fun m t => dK c t m) (ptK r)]
    unfold Inst.Model.Ledger.Rhi Inst.Model.Ledger.b256
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hdv (83 + l) (by have := Finset.mem_range.mp hl; omega)]

/-- The right side of the squares' third form, with a true read of the stream: the table's extension at the
challenges. -/
theorem streams_value (c : NCells) (hls : ls ≤ lPd) (hdS : S2 ∣ d) (W : World K)
    (hr : Norm.squares.r.size = lPd + lt)
    (hread : ∀ i, i < 5 * d / S2 → val W (FinalNorm.entry .streamAtSquares i) =
      rd (readAtN c (.stream, Norm.Read.streams.weights) i)) :
    val W (sumTo 1 fun i => sumTo (d / S2) fun k => sumTo 5 fun l =>
        (eq (Norm.squares.r.extract 0 (Norm.lNI + lPd - ls)) (i * 2 ^ lPd / S2 + k) *
          Norm.gam ^ l) • Norm.limb i l k) =
      Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd Norm.gam)) (ptK Norm.squares.r) := by
  have hN0 : Norm.lNI = 0 := rfl
  have hent : ∀ i, i < 5 * d / S2 → val W (FinalNorm.entry .streamAtSquares i) =
      (Finset.range S2).sum fun j => (Finset.range T).sum fun t =>
        rd (eq (Norm.squares.r.extract (lPd - ls) lPd) j) *
          rd (eq (Norm.squares.r.extract lPd (lPd + lt)) t) *
          ((c.stream (S2 * i + j) t : Int) : K) := by
    intro i hi
    rw [hread i hi]
    show rd (sumTo S2 fun j => sumTo T fun t =>
      eq (Norm.squares.r.extract (Norm.lNI + lPd - ls) (Norm.lNI + lPd)) j *
        eq (Norm.squares.r.extract (Norm.lNI + lPd) (Norm.lNI + lPd + lt)) t *
        ofInt (c.stream (S2 * i + j) t)) = _
    rw [hN0, Nat.zero_add, rd_sumTo]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rd_sumTo]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [rd_mul, rd_mul, rd_ofInt]
  rw [Came.val_sumTo, Finset.sum_range_one, Came.val_sumTo,
    ← streams_batch c Norm.squares.r (rd Norm.gam) hls hdS hr _ hent]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Came.val_sumTo]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Came.val_smulE, rd_mul, rd_pow, hN0, Nat.zero_add, Nat.zero_mul, Nat.zero_div,
    Nat.zero_add]
  rfl

/-- The right side of normed's second form, with a true read of the row: the reciprocal's table at the
challenges. -/
theorem recip_value (c : NCells) (W : World K) (hr : FinalNorm.normed.r.size = lt)
    (hrow : ∀ j, j < NR → val W (FinalNorm.entry .rowAtNormed j)
      = rd (readAtN c (.row, .short (eq FinalNorm.normed.r)) j)) :
    val W (OnBytes.Desc.First.P6.Row.ofDigits fun j => FinalNorm.entry .rowAtNormed j + off1).R
      = mle lt (AtN c) (FinalNorm.normed.r.toList.map rd) := by
  have hw1 : (Finset.range T).sum (fun t => rd (eq FinalNorm.normed.r t)) = 1 := by
    have h := sum_rd_eq FinalNorm.normed.r
    rwa [hr] at h
  have hD : ∀ j, j < NR → OnBytes.Desc.First.P6.dv Reading.gl W
      (fun j => FinalNorm.entry .rowAtNormed j + off1) j
      = (Finset.range T).sum fun t => rd (eq FinalNorm.normed.r t) * ((digZ c t j : Int) : K) := by
    intro j hj
    show val W (FinalNorm.entry .rowAtNormed j + off1) = _
    rw [val_add, val_natCast, hrow j hj]
    show rd (sumTo T fun t => eq FinalNorm.normed.r t * ofInt (c.cell .row j t)) + _ = _
    rw [rd_sumTo]
    have h128 : ((off1 : Nat) : K) = (Finset.range T).sum fun t => rd (eq FinalNorm.normed.r t) * ((off1 : Nat) : K) := by
      rw [← Finset.sum_mul, hw1, one_mul]
    rw [h128, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [rd_mul, rd_ofInt]
    unfold digZ off1
    push_cast
    ring
  show Aff.value Reading.gl W
    ((OnBytes.Desc.First.P6.Row.ofDigits fun j => FinalNorm.entry .rowAtNormed j + off1).Rlo
      + OnBytes.Desc.First.P6.sm (2 ^ 24)
        (OnBytes.Desc.First.P6.Row.ofDigits fun j => FinalNorm.entry .rowAtNormed j + off1).Rhi) = _
  rw [Aff.value_add, OnBytes.Desc.First.P6.sm_value, OnBytes.Desc.First.P6.Rlo_value,
    OnBytes.Desc.First.P6.Rhi_value, ledgerR,
    hD 80 (by unfold NR; omega), hD 81 (by unfold NR; omega), hD 82 (by unfold NR; omega),
    hD 83 (by unfold NR; omega), hD 84 (by unfold NR; omega), hD 85 (by unfold NR; omega)]
  have hm := mle_point FinalNorm.normed.r hr fun t => ((recZ c t : Int) : K)
  refine Eq.trans ?_ hm.symm
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hR := Inst.Model.Ledger.map_R (Int.castRingHom K) (digZ c t)
  simp only [eq_intCast] at hR
  unfold recZ
  rw [hR]
  have hl := ledgerR fun m => ((digZ c t m : Int) : K)
  unfold Inst.Model.Ledger.R
  have h24 : ((2 ^ 24 : Nat) : K) = 2 ^ 24 := by push_cast; rfl
  rw [h24] at hl
  rw [hl]
  ring

/-- The right side of normed's third form, with a true read of the stream: the weighted stream's table at the
challenges. -/
theorem stream_value (c : NCells) (W : World K) (hr : FinalNorm.normed.r.size = lt) (hd : S2 ∣ d)
    (hblock : ∀ x, x < d →
      FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2))
    (hstream : ∀ i, i < 5 * d / S2 → val W (FinalNorm.entry .streamAtNormed i)
      = rd (readAtN c (.stream, .long (eq FinalNorm.zl) (eq FinalNorm.normed.r)) i)) :
    val W (sumTo (d / S2) fun i => sumTo 5 fun l =>
      ((256 : E) ^ l * FinalNorm.ewh .remLow i) • FinalNorm.entry .streamAtNormed (l * d / S2 + i))
      = mle lt (BtN c) (FinalNorm.normed.r.toList.map rd) := by
  have hS2 : 0 < S2 := S2_posN
  have hm := mle_point FinalNorm.normed.r hr fun t =>
    (Finset.range d).sum fun x => UN .remLow x * ((str c t x : Int) : K)
  refine Eq.trans ?_ hm.symm
  rw [← spr_swap (u := UN .remLow) (w := fun t => rd (eq FinalNorm.normed.r t))
    (fun x t => ((str c t x : Int) : K))]
  have hstr : ∀ x t, ((str c t x : Int) : K)
      = (Finset.range 5).sum fun l => (256 : K) ^ l * ((c.stream (l * d + x) t : Int) : K) := by
    intro x t
    unfold str limbZ
    rw [sumZ_eq]
    push_cast
    rfl
  simp only [hstr]
  rw [← spr_sum 5 (fun l => (256 : K) ^ l) fun l x t => ((c.stream (l * d + x) t : Int) : K)]
  rw [val_sumTo]
  simp only [val_sumTo]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl5 := Finset.mem_range.1 hl
  rw [← blocks_spr hS2 hd (UN .remLow) (fun i => rd (FinalNorm.ewh .remLow i))
    (fun j => rd (eq FinalNorm.zl j)) (fun t => rd (eq FinalNorm.normed.r t)) ?_
    (fun x t => ((c.stream (l * d + x) t : Int) : K)), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have hdl : S2 ∣ l * d := Dvd.dvd.mul_left hd l
    have hidx : l * d / S2 + i < 5 * d / S2 := by
      obtain ⟨a, ha⟩ := hdl
      obtain ⟨b, hb⟩ := hd
      rw [ha, Nat.mul_div_cancel_left _ hS2]
      apply (Nat.le_div_iff_mul_le hS2).2
      have h1 : (i + 1) * S2 ≤ d / S2 * S2 := Nat.mul_le_mul_right _ hi'
      rw [Nat.div_mul_cancel ⟨b, hb⟩] at h1
      have h2 : l * d ≤ 4 * d := Nat.mul_le_mul_right d (by omega)
      have h3 : (a + i + 1) * S2 = S2 * a + (i + 1) * S2 := by ring
      rw [h3, ← ha]
      omega
    rw [val_smulE, rd_mul, rd_pow, rd_ofNat, hstream _ hidx]
    show _ * rd (sumTo S2 fun j => sumTo T fun t =>
      eq FinalNorm.zl j * eq FinalNorm.normed.r t * ofInt (c.stream (S2 * (l * d / S2 + i) + j) t)) = _
    rw [rd_sumTo]
    have hin : ∀ j, rd (sumTo T fun t =>
        eq FinalNorm.zl j * eq FinalNorm.normed.r t * ofInt (c.stream (S2 * (l * d / S2 + i) + j) t))
        = (Finset.range T).sum fun t => rd (eq FinalNorm.zl j) * rd (eq FinalNorm.normed.r t)
          * ((c.stream (l * d + (S2 * i + j)) t : Int) : K) := by
      intro j
      rw [rd_sumTo]
      refine Finset.sum_congr rfl fun t _ => ?_
      have e : S2 * (l * d / S2 + i) + j = l * d + (S2 * i + j) := by
        rw [Nat.mul_add, Nat.mul_div_cancel' hdl, Nat.add_assoc]
      rw [rd_mul, rd_mul, rd_ofInt, e]
    simp only [hin]
    push_cast
    ring
  · intro i j hi hj
    have hlt : S2 * i + j < d := by
      have h1 : (i + 1) * S2 ≤ d / S2 * S2 := Nat.mul_le_mul_right _ hi
      rw [Nat.div_mul_cancel hd, Nat.add_mul, Nat.one_mul, Nat.mul_comm] at h1
      omega
    have h1 : (S2 * i + j) / S2 = i := by
      rw [Nat.mul_add_div hS2, Nat.div_eq_of_lt hj, Nat.add_zero]
    have h2 : (S2 * i + j) % S2 = j := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
    unfold UN
    rw [hblock _ hlt, rd_mul, h1, h2]

/-- **The hidden scalars that the norm's hearings left are the true ones, and the three sumchecks' own forms are
worth 0.** -/
structure NormTruthW (W : World K) (c : NCells) : Prop where
  sums : ∀ s, s < 9 → WtOf W s = (dataOf c).sumWAt (ptK Norm.pV) 0 s
  prods : ∀ n, n < 7 → PtOf W n = (dataOf c).prodRAt (ptK Norm.pV) 0 n
  sqRow : val W (Norm.squares.left ((Norm.squares.end_ 0).shown * (Norm.squares.end_ 1).shown)) = 0
  sq0 : val W (Norm.squares.end_ 0).var =
    Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd Norm.gam)) (ptK Norm.squares.r)
  sq1 : val W (Norm.squares.end_ 1).var =
    Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd Norm.gam)) (ptK Norm.squares.r)
  prClaimed : val W Norm.products.claimed.var = (Finset.range 7).sum fun n =>
    rd Norm.om ^ n * (dataOf c).prodRAt (ptK Norm.pV) 0 n
  prRow : val W (Norm.products.left (sumTo 1 fun i => OnBytes.Desc.First.P6.summand
    (fun n => Norm.om ^ (7 * i + n)) fun j => (Norm.products.end_ (4 * i + j)).shown)) = 0
  prEnd : ∀ q, q < 4 → val W (Norm.products.end_ q).var =
    Blocks.ext lt (fieldK c q) (ptK Norm.products.r)
  nmRow : val W (FinalNorm.normed.left
    ((FinalNorm.normed.end_ 0).shown * (FinalNorm.normed.end_ 1).shown)) = 0
  nm0 : val W (FinalNorm.normed.end_ 0).var = mle lt (AtN c) (FinalNorm.normed.r.toList.map rd)
  nm1 : val W (FinalNorm.normed.end_ 1).var = mle lt (BtN c) (FinalNorm.normed.r.toList.map rd)

/-- The row's 17 forms are worth 0. -/
theorem rowForms_zero (c : NCells) (W : World K) (hH : (dataOf c).Holds)
    (hread : ∀ j, j < NR → val W (Norm.digit .rowsAtPV 0 j) =
      Blocks.ext lt (fun t => dK c t j) (ptK Norm.pV))
    (hs : ∀ s, s < 9 → WtOf W s = (dataOf c).sumWAt (ptK Norm.pV) 0 s)
    (hp : ∀ n, n < 7 → PtOf W n = (dataOf c).prodRAt (ptK Norm.pV) 0 n) :
    ∀ f, f ∈ Norm.rowForms → val W f = 0 := by
  have hL : (dataOf c).Lines (ptK Norm.pV) (WtOf W) (PtOf W) := by
    refine (D6.Bridge.lines_iff_of_true (dataOf c) (ptK Norm.pV) (WtOf W) (PtOf W) ?_ ?_).mpr ?_
    · intro i hi s hs'
      obtain rfl : i = 0 := by
        have : i < 1 := hi
        omega
      unfold Data.dW
      rw [Nat.mul_zero, Nat.zero_add, hs s hs', sub_self]
    · intro m hm
      have hm' : m < 7 := by
        have : m < 7 * 1 := hm
        omega
      unfold Data.dP
      rw [Nat.div_eq_of_lt hm', Nat.mod_eq_of_lt hm', hp m hm', sub_self]
    · intro i hi k hk
      have hz : Blocks.ext (dataOf c).lt ((dataOf c).idAt i k) (ptK Norm.pV)
          = Blocks.ext (dataOf c).lt (fun _ => (0 : K)) (ptK Norm.pV) :=
        Blocks.ext_congr (fun t ht => hH i hi k hk t ht) _
      rw [hz, Blocks.ext_const]
  intro f hf
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hf
  have hv := rowForms_valuesW W
  have hlen : Norm.rowForms.length = 17 := by
    have := congrArg List.length hv
    rwa [List.length_map, List.length_map, List.length_range] at this
  have hk17 : k < 17 := by rw [hlen] at hk; exact hk
  have e := congrArg (fun l => l.getD k 0) hv
  simp only at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk17] at e
  simp only [Option.map_some, Option.getD_some] at e
  have eD := D6.Bridge.idnP_congr_D npOf
    (OnBytes.Desc.First.P6.dv Reading.gl W fun s => (Norm.W.getD (9 * 0 + s) {}).var)
    (OnBytes.Desc.First.P6.dv Reading.gl W fun n => (Norm.P.getD (7 * 0 + n) {}).var)
    (D := OnBytes.Desc.First.P6.dv Reading.gl W (Norm.digit .rowsAtPV 0))
    (D' := (dataOf c).digAt (ptK Norm.pV) 0) (fun n hn => hread n hn) k
  rw [eD] at e
  rw [e]
  exact hL 0 Nat.one_pos k hk17

/-- **OPENED AT THE TRUTH: THE NORMALIZATION's 29 FORMS.** -/
theorem opened_norm (c : NCells) (W : World K) (hH : (dataOf c).Holds) (hls : ls ≤ lPd)
    (hdS : S2 ∣ d)
    (hblock : ∀ x, x < d →
      FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2))
    (hrS : Norm.squares.r.size = lPd + lt) (hrN : FinalNorm.normed.r.size = lt)
    (hreads : NormReads W c) (hreadsN : NormedReads W c) (ht : NormTruthW W c) :
    ∀ f, f ∈ FinalNorm.forms → val W f = 0 := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · -- the squares' three
        rw [squareForms_eq] at hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl
        · exact ht.sqRow
        · rw [val_sub, ht.sq0, ht.sq1, sub_self]
        · rw [val_sub, ht.sq0, streams_value c hls hdS W hrS hreads.atSquares, sub_self]
      · -- the products' six
        rw [productForms_eq] at hf
        obtain ⟨va, vb, vl, vh⟩ :=
          field_values c W (Norm.digit .rowsAtProducts 0) Norm.products.r hreads.atProducts
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [val_sub, val_sumTo, ht.prClaimed, sub_eq_zero]
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [val_smulE, rd_pow, ← ht.prods n (Finset.mem_range.mp hn)]
          rfl
        · exact ht.prRow
        · rw [val_sub, ht.prEnd 0 (by omega), va, sub_self]
        · rw [val_sub, ht.prEnd 1 (by omega), vb, sub_self]
        · rw [val_sub, ht.prEnd 2 (by omega), vl, sub_self]
        · rw [val_sub, ht.prEnd 3 (by omega), vh, sub_self]
    · exact rowForms_zero c W hH hreads.atPV ht.sums ht.prods f hf
  · -- normed's three
    simp only [FinalNorm.normedForms, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact ht.nmRow
    · rw [val_sub, ht.nm0]
      exact sub_eq_zero.mpr (recip_value c W hrN hreadsN.row).symm
    · rw [val_sub, ht.nm1]
      exact sub_eq_zero.mpr (stream_value c W hrN hdS hblock hreadsN.stream).symm

end Values

end VerifiableInference.Desc.Kinds.Head.Law

end

#print axioms VerifiableInference.Desc.Kinds.Head.Law.opened_norm
