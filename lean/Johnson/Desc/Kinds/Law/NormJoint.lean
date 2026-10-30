-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormJoint.lean.
WHAT IT DOES NOT SHOW. THE SQUARES' LEVEL: that the batch of the nine hidden sums is the true one
(Data.Squares) is a PREMISE here: it wants the law of HeadParts.lean's "level". That the reads are
true, that the forms are 0, that the world is the ledger's, that no bad element was drawn: premises.
That Norm.lean's whole hearing falls apart into the stretches at which the parts' laws are stated:
not here. Nothing on probabilities: the bad sets and their counts are the bridge's own.
WHAT IT IS. K6's JOINT ON THE PER-POSITION BRIDGE OF A NORM, over the bridge's floor of plain
algebra (OnBytes/Desc/First/NormBridge/BridgeCore.lean: Data, Lines, Squares, Products, the four bad
sets, bridge), at the head's one norm: dataOf c: the bridge's data, of the kind's cells.
lines_of_world: the 17 forms of Norm.rowForms worth 0 in a world with a true read at pV: the
bridge's Lines. products_of_world: the law of "products" (Law/NormProducts.lean) with the batched
form: the bridge's Products. rows_of_holds: from the bridge's conclusion (every identity at every
position) to the clause rows of CellRelN, to the letter. norm_joint: all together.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NormProducts
import OnBytes.Desc.First.NormBridge.BridgeCore
import OnBytes.Desc.First.NormBridge.IdnDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Reading World Fork)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits)
open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)
open Came (val)
open D6.Bridge (Data)

variable [Sizes] [Policy] [Request] [Token]

/-- The bridge's data, of the kind's cells: one norm. -/
def dataOf (c : NCells) : Data K where
  lt := lt
  d := d
  NI := 1
  lNI := 0
  np := fun _ => npOf
  limb := fun _ l j t => ((limbZ c t l j : Int) : K)
  dig := fun _ n t => dK c t n

theorem idAt_eq (c : NCells) (k t : Nat) : (dataOf c).idAt 0 k t = vecK c k t := by
  unfold Data.idAt vecK
  congr 1
  funext s
  show Inst.Model.Ledger.Wsum d (fun l j => ((limbZ c t l j : Int) : K)) s = _
  unfold Inst.Model.Ledger.Wsum wsqZ
  rw [sumZ_eq]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sumZ_eq]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sumZ_eq]
  push_cast
  rfl

/-- **From the bridge's conclusion to the clause rows of CellRelN.** -/
theorem rows_of_holds (c : NCells) (h : (dataOf c).Holds) :
    ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0 := by
  intro t ht v hv
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
  have hk' : k < 17 := by rw [rowsAt_length] at hk; exact hk
  apply eq_of_rd (okE_rowsAt c _ hv) okE_zero
  have e := rd_rowsAt c (bits lt t) (size_bits lt t) hk'
  rw [List.getD_eq_getElem _ _ hk, ext_corner ht, ← idAt_eq, h 0 Nat.one_pos k hk' t ht] at e
  rw [e, rd_zero]

/-- And back: the clause gives the bridge's conclusion. -/
theorem holds_of_rows (c : NCells)
    (h : ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0) : (dataOf c).Holds := by
  intro i hi k hk t ht
  obtain rfl : i = 0 := by
    have : i < 1 := hi
    omega
  have hlen : k < (rowsAt c (bits lt t)).length := by rw [rowsAt_length]; exact hk
  have e := rd_rowsAt c (bits lt t) (size_bits lt t) hk
  rw [List.getD_eq_getElem _ _ hlen, h t ht _ (List.getElem_mem hlen), rd_zero, ext_corner ht] at e
  rw [idAt_eq]
  exact e.symm

section World
variable [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]

/-- The 17 forms' values in any world: NormPoint.lean's rowForms_values, the world a letter. -/
theorem rowForms_valuesW (W : World K) :
    Norm.rowForms.map (val W) = (List.range 17).map fun k =>
      Inst.Model.Ledger.idnP npOf
        (OnBytes.Desc.First.P6.dv Reading.gl W fun s => (Norm.W.getD (9 * 0 + s) {}).var)
        (OnBytes.Desc.First.P6.dv Reading.gl W (Norm.digit .rowsAtPV 0))
        (OnBytes.Desc.First.P6.dv Reading.gl W fun n => (Norm.P.getD (7 * 0 + n) {}).var) k := by
  rw [rowForms_eq, List.map_append]
  have h1 := OnBytes.Desc.First.P6.carries_value Reading.gl W (Norm.digit .rowsAtPV 0)
    (fun s => (Norm.W.getD (9 * 0 + s) {}).var) (fun n => (Norm.P.getD (7 * 0 + n) {}).var) npOf
  have h2 := OnBytes.Desc.First.P6.lines_value Reading.gl W (Norm.digit .rowsAtPV 0)
    (fun s => (Norm.W.getD (9 * 0 + s) {}).var) (fun n => (Norm.P.getD (7 * 0 + n) {}).var) npOf
    ((epsF : Nat) : E) ((2 ^ (MF + 1) : Nat) : Form)
    (by
      show rd ((epsF : Nat) : E) = _
      rw [rd_natCast]
      simp [npOf])
    (by
      show val W ((2 ^ (MF + 1) : Nat) : Form) = _
      rw [Came.val_natCast]
      simp [npOf])
  have e1 : (OnBytes.Desc.First.P6.carries (P6.Row.ofDigits (Norm.digit .rowsAtPV 0))
      (Norm.digit .rowsAtPV 0) fun s => (Norm.W.getD (9 * 0 + s) {}).var).map (val W) = _ := h1
  have e2 : (OnBytes.Desc.First.P6.lines (P6.Row.ofDigits (Norm.digit .rowsAtPV 0))
      (fun n => (Norm.P.getD (7 * 0 + n) {}).var) ((epsF : Nat) : E)
      ((2 ^ (MF + 1) : Nat) : Form)).map (val W) = _ := h2
  rw [e1, e2]
  have h17 : List.range 17 = List.range 9 ++ (List.range 8).map (9 + ·) := by decide
  rw [h17, List.map_append, List.map_map]
  rfl

/-- The hidden sums and products, in a world. -/
def WtOf (W : World K) : Nat → K := fun s => val W (Norm.W.getD s {}).var
def PtOf (W : World K) : Nat → K := fun n => val W (Norm.P.getD n {}).var

/-- **The bridge's Lines**: the 17 forms are worth 0; the read of the row at pV is true. -/
theorem lines_of_world (c : NCells) (W : World K)
    (hread : ∀ j, j < NR → val W (Norm.digit .rowsAtPV 0 j) =
      Blocks.ext lt (fun t => dK c t j) (ptK Norm.pV))
    (hz : ∀ f, f ∈ Norm.rowForms → val W f = 0) :
    (dataOf c).Lines (ptK Norm.pV) (WtOf W) (PtOf W) := by
  intro i hi k hk
  obtain rfl : i = 0 := by
    have : i < 1 := hi
    omega
  have hv := rowForms_valuesW W
  have hlen : Norm.rowForms.length = 17 := by
    have := congrArg List.length hv
    rwa [List.length_map, List.length_map, List.length_range] at this
  have hk' : k < Norm.rowForms.length := by rw [hlen]; exact hk
  have e := congrArg (fun l => l.getD k 0) hv
  simp only at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk',
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk] at e
  simp only [Option.map_some, Option.getD_some] at e
  rw [hz _ (List.getElem_mem hk')] at e
  have eD := D6.Bridge.idnP_congr_D npOf
    (OnBytes.Desc.First.P6.dv Reading.gl W fun s => (Norm.W.getD (9 * 0 + s) {}).var)
    (OnBytes.Desc.First.P6.dv Reading.gl W fun n => (Norm.P.getD (7 * 0 + n) {}).var)
    (D := OnBytes.Desc.First.P6.dv Reading.gl W (Norm.digit .rowsAtPV 0))
    (D' := (dataOf c).digAt (ptK Norm.pV) 0) (fun n hn => hread n hn) k
  rw [eD] at e
  exact e.symm

end World

/-- **The bridge's Products**: the claimed sum's hidden scalar is the batch of the seven hidden
products (the first of productForms) and the batch of the true extensions (products_law). -/
theorem products_of_world (c : NCells) (u : Nat → K) (Pt : Nat → K) (om cl : K)
    (hbatch : cl = (Finset.range 7).sum fun n => om ^ n * Pt n)
    (hlaw : cl = (Finset.range 7).sum fun n =>
      om ^ n * Blocks.ext lt (fun t => Inst.Model.Ledger.prods (dK c t) n) u) :
    (dataOf c).Products u Pt om := by
  unfold Data.Products
  show (Finset.range (7 * 1)).sum (fun m => om ^ m * Pt m) = Blocks.ext lt (fun t =>
    (Finset.range (7 * 1)).sum fun m => om ^ m * (dataOf c).prodR (m / 7) (m % 7) t) u
  rw [Nat.mul_one, ← hbatch, hlaw, Blocks.ext_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.mp hm
  rw [Blocks.ext_smul, Nat.mod_eq_of_lt hm']
  rfl

/-! ## The products' six forms of the kind's own text -/

section ProductsText
variable [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]

/-- Norm.productForms at the head's one norm, written out. -/
theorem productForms_eq :
    Norm.productForms =
      [Norm.products.claimed.var - sumTo 7 fun n => Norm.om ^ n • (Norm.P.getD n {}).var,
       Norm.products.left (sumTo 1 fun i => OnBytes.Desc.First.P6.summand
         (fun n => Norm.om ^ (7 * i + n)) fun j => (Norm.products.end_ (4 * i + j)).shown),
       (Norm.products.end_ 0).var - (P6.Row.ofDigits (Norm.digit .rowsAtProducts 0)).a,
       (Norm.products.end_ 1).var - (P6.Row.ofDigits (Norm.digit .rowsAtProducts 0)).b,
       (Norm.products.end_ 2).var - (P6.Row.ofDigits (Norm.digit .rowsAtProducts 0)).Rlo,
       (Norm.products.end_ 3).var - (P6.Row.ofDigits (Norm.digit .rowsAtProducts 0)).Rhi] := by
  simp [Norm.productForms, Norm.rowAt, Norm.NI, List.range_succ, List.zipIdx]

/-- **The bridge's Products, of the kind's own six forms.** The cells, the masks, the ledger in
front of the sumcheck, pV and om stand first (the last two are letters of the classes here); the
rule for the bad elements is productsRule. -/
theorem products_text (c : NCells) (mask : Nat → E) (F0 : Fork) (hWL : WellLaid F0)
    (hz : (Norm.pV).size = lt) {F1 : Fork} {t : List Fmt.RoundView} (W : World K)
    (hWs : ∀ j, F0.next ≤ j → j < Came.sEndG Norm.pV 4 F0 + 4 → W.slot j = rd (hidden F1 mask j))
    (hcan : Canonical t) (hsum : sumcheck Norm.pV 4 F0 t = some (Norm.products, F1, []))
    (hread : ∀ j, j < NR → val W (Norm.digit .rowsAtProducts 0 j) =
      Blocks.ext lt (fun t => dK c t j) (ptK Norm.products.r))
    (hforms : ∀ f, f ∈ Norm.productForms → val W f = 0)
    (hnb : NoBad (productsRule c mask F0 Norm.pV Norm.om) t) :
    (dataOf c).Products (ptK Norm.pV) (PtOf W) (rd Norm.om) := by
  rw [productForms_eq] at hforms
  have f0 := hforms _ (List.mem_cons_self ..)
  have f1 := hforms _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have f2 := hforms _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have f3 := hforms _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..))))
  have f4 := hforms _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have f5 := hforms _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))
  have hS0 : rd (sumTo 1 fun i => OnBytes.Desc.First.P6.summand
      (fun n => Norm.om ^ (7 * i + n)) fun j => (Norm.products.end_ (4 * i + j)).shown) =
      OnBytes.Desc.First.P1.sumTerms (tsP (rd Norm.om)) fun q =>
        rd (Norm.products.end_ q).shown := by
    rw [rd_sumTo, Finset.sum_range_one]
    have h := rd_summand (fun n => Norm.om ^ (7 * 0 + n))
      (fun j => (Norm.products.end_ (4 * 0 + j)).shown) (rd Norm.om) (fun n _ => by
        show rd (Norm.om ^ (7 * 0 + n)) = _
        rw [Nat.mul_zero, Nat.zero_add, rd_pow])
    simpa using h
  have hlaw := products_law c mask F0 Norm.pV Norm.om hWL hz W (Norm.digit .rowsAtProducts 0) _
    hWs hcan hsum hread hS0 f1 f2 f3 f4 f5 hnb
  refine products_of_world c _ _ _ (val W Norm.products.claimed.var) ?_ hlaw
  rw [Came.val_sub, Came.val_sumTo] at f0
  rw [sub_eq_zero.mp f0]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Came.val_smulE, rd_pow]
  rfl

end ProductsText

/-! ## The point as the bridge takes it -/

/-- A point of lt coordinates, read, as a tuple. -/
def tupK (z : Point) : Fin lt → K := fun i => ptK z i

theorem nat_tupK (z : Point) {t : Nat} (ht : t < lt) : Blocks.nat (tupK z) t = ptK z t := by
  unfold Blocks.nat tupK
  rw [dif_pos ht]

theorem lines_at_tuple (c : NCells) (z : Point) (Wt Pt : Nat → K)
    (h : (dataOf c).Lines (ptK z) Wt Pt) : (dataOf c).Lines (Blocks.nat (tupK z)) Wt Pt := by
  intro i hi k hk
  have e : (dataOf c).digAt (Blocks.nat (tupK z)) i = (dataOf c).digAt (ptK z) i := by
    funext n
    exact ext_congr_pt lt _ fun t ht => nat_tupK z ht
  rw [e]
  exact h i hi k hk

theorem products_at_tuple (c : NCells) (z : Point) (Pt : Nat → K) (om : K)
    (h : (dataOf c).Products (ptK z) Pt om) : (dataOf c).Products (Blocks.nat (tupK z)) Pt om := by
  unfold Data.Products at h ⊢
  rw [h]
  exact (ext_congr_pt lt _ fun t ht => nat_tupK z ht).symm

/-- **K6's JOINT, IN THE BRIDGE's OWN LETTERS.** The cells stand first. At a point P over the
positions, hidden sums Wt, gam, hidden products Pt, om: the bridge's three premises and none of its
four bad events: the clause rows of CellRelN. -/
theorem norm_joint (c : NCells) (P : Fin lt → K) (Wt : Nat → K) (gam : K) (Pt : Nat → K) (om : K)
    (hlines : (dataOf c).Lines (Blocks.nat P) Wt Pt)
    (hsq : (dataOf c).Squares (Blocks.nat P) Wt gam (Blocks.nat (fun _ : Fin 0 => (0 : K))))
    (hpr : (dataOf c).Products (Blocks.nat P) Pt om)
    (hP : ¬ (dataOf c).BadP P) (hG : ¬ (dataOf c).BadG (Blocks.nat P) Wt gam)
    (hI : ¬ (dataOf c).BadI (Blocks.nat P) Wt gam fun _ => 0)
    (hO : ¬ (dataOf c).BadO (Blocks.nat P) Pt om) :
    ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0 :=
  rows_of_holds c
    (D6.Bridge.bridge (dataOf c) P Wt gam (fun _ => 0) Pt om hlines hsq hpr hP hG hI hO)

end VerifiableInference.Desc.Kinds.Head.Law
