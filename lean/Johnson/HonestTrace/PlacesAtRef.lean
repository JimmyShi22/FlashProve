-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PlacesAtRef.lean

At the reference sizes, in every matrix that its segment owns and that holds no planes, and inside
its shape, the laying by formula of Johnson/HonestTrace/Places.lean has the entries of the library's
own laying of a trace, which picks by choice.

The library lays the cells of a trace in one matrix for each of its 25 segments, the matrices of a
segment stacked in slots of 65,536 rows (Cm/SegLayout.lean). Its function from a trace to these
matrices, "Cm.Seg.toMat", asks at each place whether some valid name stands there and picks one by
choice, so it cannot be run. "lay" of Johnson/HonestTrace/Places.lean finds the name by division.
This file shows that at the numbers "Sz.ref" the two have the same entries there.

Main definitions and theorems:
* "slot": the slot of a matrix in the library's matrix of its segment. "toCm", "ofCm": names of
  cells, to and from the library's layout. "ownsCells": a matrix that its segment owns and that
  holds no planes.
* "cm_place": for a name that is valid at "Sz.ref" and is no bit, the library's name is valid at the
  head "Hd.main", and its place is (the segment's number, 65,536 slot + row, column) of the place in
  Johnson/HonestTrace/Places.lean.
* "lay_ref_toMat": for a matrix with "ownsCells", at a row r and a column c inside its shape at
  "Sz.ref", "lay Sz.ref X σ μ r c" is "Cm.Seg.toMat Hd.main X.T" at the segment's number, row
  65,536 slot + r, column c.

Limits. The reference sizes alone: "Cm.Seg.toMat" is written in their numerals. The library's layout
has no names for the bits of the lookups' counts, so nothing is said at b, bA, bH. At a borrowed
matrix (qa in attention, xbI from group 1 on, xbL) the comparison goes through the owner:
"lay_owner" (Johnson/HonestTrace/PlacesBack.lean). Outside a matrix's shape "lay" is 0, while the
library's matrix goes on into padding or the next slot; the two are not compared there. The numbers
of columns are evaluated by Lean's kernel ("decide +kernel").

Not claimed: that any program lays its cells so; anything on the values of the cells.

-/
import Cm.SegLayoutProofs
import Johnson.HonestTrace.PlacesBack

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open Inst.Model.AttSeg.AddrFacts (adr phi pos mat SM SD Phi IsC phi_lt adr_lt addr_feat addr_c)
open Inst.Model.FFSeg.IndexFacts (feat_lt mx_ne_b)

/-! ## Numbers at the reference sizes -/

/-- At the reference numbers a part of af has 5,990 columns. -/
theorem kF_af (p : ℕ) : Sz.ref.kF (.af p) = 5990 :=
  show Sz.ref.kF (.af 0) = 5990 by decide +kernel
/-- At the reference numbers a part of ad has 3,200 columns. -/
theorem kF_ad (p : ℕ) : Sz.ref.kF (.ad p) = 3200 :=
  show Sz.ref.kF (.ad 0) = 3200 by decide +kernel
/-- At the reference numbers ar has 324 columns. -/
theorem kF_ar : Sz.ref.kF .ar = 324 := by decide +kernel
/-- At the reference numbers qa has 1,536 columns. -/
theorem kF_qa : Sz.ref.kF .qa = 1536 := by decide +kernel
/-- At the reference numbers xbO has 400 columns. -/
theorem kF_xbO : Sz.ref.kF .xbO = 400 := by decide +kernel
/-- At the reference numbers xbI has 400 columns. -/
theorem kF_xbI : Sz.ref.kF .xbI = 400 := by decide +kernel
/-- At the reference numbers a part of as has 7,200 columns. -/
theorem kF_as (p : ℕ) : Sz.ref.kF (.as p) = 7200 :=
  show Sz.ref.kF (.as 0) = 7200 by decide +kernel
/-- At the reference numbers ah has 360 columns. -/
theorem kF_ah : Sz.ref.kF .ah = 360 := by decide +kernel
/-- At the reference numbers ao has 640 columns. -/
theorem kF_ao : Sz.ref.kF .ao = 640 := by decide +kernel
/-- At the reference numbers a part of hf has 4,816 columns. -/
theorem kF_hf (p : ℕ) : Sz.ref.kF (.hf p) = 4816 :=
  show Sz.ref.kF (.hf 0) = 4816 by decide +kernel
/-- At the reference numbers hd has 640 columns. -/
theorem kF_hd : Sz.ref.kF .hd = 640 := by decide +kernel
/-- At the reference numbers hr has 15 columns. -/
theorem kF_hr : Sz.ref.kF .hr = 15 := by decide +kernel

/-- At the reference numbers "Sz.DA" is the library's reference sizes of attention. -/
theorem ref_DA : Sz.ref.DA = DA := rfl

/-- At the reference numbers a column of af holds 64 features. -/
theorem wc_af (p : ℕ) : Sz.ref.wc (.af p) = 64 := rfl
/-- At the reference numbers a column of ad holds 32 features. -/
theorem wc_ad (p : ℕ) : Sz.ref.wc (.ad p) = 32 := rfl
/-- At the reference numbers a column of ar holds 8 features. -/
theorem wc_ar : Sz.ref.wc .ar = 8 := rfl
/-- At the reference numbers a column of qa holds 64 features. -/
theorem wc_qa : Sz.ref.wc .qa = 64 := rfl
/-- At the reference numbers a column of xbO holds 64 features. -/
theorem wc_xbO : Sz.ref.wc .xbO = 64 := rfl
/-- At the reference numbers a column of xbI holds 64 features. -/
theorem wc_xbI : Sz.ref.wc .xbI = 64 := rfl
/-- At the reference numbers a column of ah holds 8 features. -/
theorem wc_ah : Sz.ref.wc .ah = 8 := rfl
/-- At the reference numbers a column of ao holds 64 features. -/
theorem wc_ao : Sz.ref.wc .ao = 64 := rfl
/-- At the reference numbers a column of hf holds 64 features. -/
theorem wc_hf (p : ℕ) : Sz.ref.wc (.hf p) = 64 := rfl
/-- At the reference numbers a column of hd holds 16 features. -/
theorem wc_hd : Sz.ref.wc .hd = 16 := rfl
/-- At the reference numbers a column of hr holds 8 features. -/
theorem wc_hr : Sz.ref.wc .hr = 8 := rfl
/-- At the reference numbers there are 2^10 positions. -/
theorem lt_ref : Sz.ref.lt = 10 := rfl
/-- The library's reference sizes of a feed-forward segment have 1,024 positions. -/
theorem T_DF : FFSeg.Dim.T DF = 1024 := rfl
/-- At the reference numbers ad lies in one part. -/
theorem NAd_ref : Sz.ref.NAd = 1 := rfl
/-- At the reference numbers as lies in one part. -/
theorem NAs_ref : Sz.ref.NAs = 1 := rfl
/-- At the reference numbers as has 2^16 rows. -/
theorem lmS_ref : Sz.ref.lmS = 16 := rfl
/-- At the reference numbers hf has 1,232,768 features in use. -/
theorem n_hf (p : ℕ) : Sz.ref.n (.hf p) = 1232768 :=
  show Sz.ref.n (.hf 0) = 1232768 by decide +kernel
/-- At the reference numbers hd has 10,240 features in use. -/
theorem n_hd : Sz.ref.n .hd = 10240 := by decide +kernel
/-- hr has 120 features in use. -/
theorem n_hr : Sz.ref.n .hr = 120 := rfl
/-- The library's reference sizes of attention have 1,024 positions. -/
theorem T_DA : AttSeg.Dim.T DA = 1024 := by decide +kernel
/-- In the library's reference sizes a column of af, qa and the stream holds 2^6 features. -/
theorem fBig_DF : DF.fBig = 6 := rfl
/-- In the library's reference sizes a column of ad holds 2^5 features. -/
theorem fAd_DF : DF.fAd = 5 := rfl
/-- In the library's reference sizes a column of ar holds 2^3 features. -/
theorem fAr_DF : DF.fAr = 3 := rfl

/-- The number of a feature at "Sz.ref.DF" is that at the library's reference sizes: it does not
read the fields in which the two differ. -/
theorem feat_ref (X : FFSeg.Arr) (k inst j : ℕ) :
    FFSeg.feat Sz.ref.DF X k inst j = FFSeg.feat DF X k inst j := rfl

/-- A cell is valid at "Sz.ref.DF" exactly if it is at the library's reference sizes. -/
theorem valid_ref (c : FFSeg.Cell) : c.Valid Sz.ref.DF ↔ c.Valid DF := Iff.rfl

/-! ## The library's one matrix of a segment -/

/-- The slot of 65,536 rows in which a matrix lies in the library's one matrix of its segment
(Cm/SegLayout.lean: "slotFF", "slotAtt", and the head's 0, 4, 5): a part of af, as or hf in the slot
of the part's number. 8 for the planes and xbL, which have no slot there. -/
def slot : MatName → ℕ
  | .af p => p | .ad _ => 3 | .ar => 4 | .qa => 5 | .xbI => 6 | .xbO => 7
  | .as p => p | .ah => 1 | .ao => 2
  | .hf p => p | .hd => 4 | .hr => 5
  | _ => 8

/-- A name of a cell as a name of the library's layout (Cm/SegLayout.lean); "none" for a bit, for
which that layout has no name. -/
def toCm : Name → Option Cm.Seg.Name
  | .ff g c => some (.ff g c)
  | .att g c => some (.att g c)
  | .hf φ i => some (.hf φ i)
  | .hd φ i => some (.hd φ i)
  | .hr φ i => some (.hr φ i)
  | .bit .. => none

/-- A name of the library's layout as a name of Johnson/HonestTrace/Places.lean. -/
def ofCm : Cm.Seg.Name → Name
  | .ff g c => .ff g c
  | .att g c => .att g c
  | .hf φ i => .hf φ i
  | .hd φ i => .hd φ i
  | .hr φ i => .hr φ i

/-- For a column q with q / k < 1, 0 < k ≤ W: the library's "stack" lays it in the slot s itself, at
column q mod k. -/
theorem stack_single {W k s q row : ℕ} (hq : q / k < 1) (hk0 : 0 < k) (hk : k ≤ W) :
    Cm.Seg.stack W s row q = (s * 65536 + row, q % k) := by
  have h1 : q < k := by
    have := (Nat.div_lt_iff_lt_mul hk0).1 hq
    omega
  unfold Cm.Seg.stack
  rw [Cm.Seg.hSlot_eq, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h1 hk),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 hk), Nat.mod_eq_of_lt h1, Nat.add_zero]

/-- From slot 0 the library's "stack" lays column q in slot q / W at column q mod W. -/
theorem stack_multi (W q row : ℕ) :
    Cm.Seg.stack W 0 row q = (q / W * 65536 + row, q % W) := by
  unfold Cm.Seg.stack
  rw [Cm.Seg.hSlot_eq, Nat.zero_add]

/-- For the library's matrices of a feed-forward segment but b, and a feature in use at the
reference numbers: the library's stacked row and column of the feature's cell are the slot's first
row plus the row of "atFeat", and the column of "atFeat". -/
theorem ff_tie (σ : Seg) {μ : FFSeg.Mx} (hμ : μ ≠ .b) (φ i : ℕ)
    (hφ : φ < Sz.ref.n (famOf μ)) :
    Cm.Seg.stack Cm.Seg.colsFF (Cm.Seg.slotFF μ) (FFSeg.featAt DF μ φ i).1
        (FFSeg.featAt DF μ φ i).2 =
      (slot (Sz.ref.atFeat σ (famOf μ) φ i).2.1 * 65536 + (Sz.ref.atFeat σ (famOf μ) φ i).2.2.1,
        (Sz.ref.atFeat σ (famOf μ) φ i).2.2.2) := by
  have hp := (Sz.part_lt ref_ok.1 (Sz.isFeat_famOf 0 hμ) hφ).1
  cases μ with
  | b => exact absurd rfl hμ
  | af =>
    simp only [Cm.Seg.slotFF, FFSeg.featAt, FFSeg.lFeat, Cm.Seg.colsFF_eq, Sz.atFeat, famOf,
      MatName.setPart, slot, kF_af, wc_af, lt_ref, T_DF, fBig_DF, Nat.reducePow]
    exact stack_multi _ _ _
  | ad =>
    simp only [famOf, kF_ad, wc_ad, Sz.np, NAd_ref] at hp
    simp only [Cm.Seg.slotFF, FFSeg.featAt, FFSeg.lFeat, Cm.Seg.colsFF_eq, Sz.atFeat, famOf,
      MatName.setPart, slot, kF_ad, wc_ad, lt_ref, T_DF, fAd_DF, Nat.reducePow]
    exact stack_single hp (by norm_num) (by norm_num)
  | ar =>
    simp only [famOf, kF_ar, wc_ar, Sz.np] at hp
    simp only [Cm.Seg.slotFF, FFSeg.featAt, FFSeg.lFeat, Cm.Seg.colsFF_eq, Sz.atFeat, famOf,
      MatName.setPart, slot, kF_ar, wc_ar, lt_ref, T_DF, fAr_DF, Nat.reducePow]
    exact stack_single hp (by norm_num) (by norm_num)
  | qa =>
    simp only [famOf, kF_qa, wc_qa, Sz.np] at hp
    simp only [Cm.Seg.slotFF, FFSeg.featAt, FFSeg.lFeat, Cm.Seg.colsFF_eq, Sz.atFeat, famOf,
      MatName.setPart, slot, kF_qa, wc_qa, lt_ref, T_DF, fBig_DF, Nat.reducePow]
    exact stack_single hp (by norm_num) (by norm_num)
  | xin =>
    simp only [famOf, kF_xbI, wc_xbI, Sz.np] at hp
    simp only [Cm.Seg.slotFF, FFSeg.featAt, FFSeg.lFeat, Cm.Seg.colsFF_eq, Sz.atFeat, famOf,
      MatName.setPart, slot, kF_xbI, wc_xbI, lt_ref, T_DF, fBig_DF, Nat.reducePow]
    exact stack_single hp (by norm_num) (by norm_num)
  | xout =>
    simp only [famOf, kF_xbO, wc_xbO, Sz.np] at hp
    simp only [Cm.Seg.slotFF, FFSeg.featAt, FFSeg.lFeat, Cm.Seg.colsFF_eq, Sz.atFeat, famOf,
      MatName.setPart, slot, kF_xbO, wc_xbO, lt_ref, T_DF, fBig_DF, Nat.reducePow]
    exact stack_single hp (by norm_num) (by norm_num)

/-- The same for a feature in use of ah. -/
theorem ah_tie (σ : Seg) (φ i : ℕ) (hφ : φ < Sz.ref.n .ah) :
    Cm.Seg.stack Cm.Seg.colsAtt (Cm.Seg.slotAtt .ah) (AttSeg.featAt DA 3 φ i).1
        (AttSeg.featAt DA 3 φ i).2 =
      (slot (Sz.ref.atFeat σ .ah φ i).2.1 * 65536 + (Sz.ref.atFeat σ .ah φ i).2.2.1,
        (Sz.ref.atFeat σ .ah φ i).2.2.2) := by
  have hp := (Sz.part_lt ref_ok.1 (σ := .att 0) (μ := .ah) rfl hφ).1
  simp only [kF_ah, wc_ah, Sz.np] at hp
  simp only [Cm.Seg.slotAtt, AttSeg.featAt, Cm.Seg.colsAtt_eq, Sz.atFeat, MatName.setPart, slot,
    kF_ah, wc_ah, lt_ref, T_DA, Nat.reducePow]
  exact stack_single hp (by norm_num) (by norm_num)

/-- The same for a feature in use of ao. -/
theorem ao_tie (σ : Seg) (φ i : ℕ) (hφ : φ < Sz.ref.n .ao) :
    Cm.Seg.stack Cm.Seg.colsAtt (Cm.Seg.slotAtt .ao) (AttSeg.featAt DA 6 φ i).1
        (AttSeg.featAt DA 6 φ i).2 =
      (slot (Sz.ref.atFeat σ .ao φ i).2.1 * 65536 + (Sz.ref.atFeat σ .ao φ i).2.2.1,
        (Sz.ref.atFeat σ .ao φ i).2.2.2) := by
  have hp := (Sz.part_lt ref_ok.1 (σ := .att 0) (μ := .ao) rfl hφ).1
  simp only [kF_ao, wc_ao, Sz.np] at hp
  simp only [Cm.Seg.slotAtt, AttSeg.featAt, Cm.Seg.colsAtt_eq, Sz.atFeat, MatName.setPart, slot,
    kF_ao, wc_ao, lt_ref, T_DA, Nat.reducePow]
  exact stack_single hp (by norm_num) (by norm_num)

/-- The library's stacked row and column of cell number N of as are the slot's first row plus the
row of "atCell", and the column of "atCell". For every N. -/
theorem as_tie (g N : ℕ) :
    Cm.Seg.stack Cm.Seg.colsAtt (Cm.Seg.slotAtt .as) (AttSeg.asAt DA KA N).1
        (AttSeg.asAt DA KA N).2 =
      (slot (Sz.ref.atCell g N).2.1 * 65536 + (Sz.ref.atCell g N).2.2.1,
        (Sz.ref.atCell g N).2.2.2) := by
  have e : AttSeg.lRow DA KA .as = 16 := rfl
  simp only [Cm.Seg.slotAtt, AttSeg.asAt, e, Cm.Seg.colsAtt_eq, Sz.atCell, slot, kF_as, lmS_ref,
    Nat.reducePow]
  exact stack_multi _ _ _

/-- **The library's place of a name, slot by slot.** For a name n that is valid at the reference
numbers and is no bit, and the library's name m of it: m is valid in the library's layout with the
head "Hd.main", and m's place there is: the number of n's segment; 65,536 times the slot of n's
matrix, plus n's row; n's column. -/
theorem cm_place (n : Name) (m : Cm.Seg.Name) (e : toCm n = some m) (hn : n.Valid Sz.ref) :
    m.Valid Cm.Seg.Hd.main ∧
      m.place = ((n.place Sz.ref).1.no 12,
        slot (n.place Sz.ref).2.1 * 65536 + (n.place Sz.ref).2.2.1, (n.place Sz.ref).2.2.2) := by
  cases n with
  | ff g c =>
    obtain rfl := Option.some.inj e
    refine ⟨hn, ?_⟩
    have hφ : FFSeg.feat Sz.ref.DF c.X c.k c.inst c.j < Sz.ref.n (famOf c.X.mx) := by
      rw [Sz.n_famOf]
      exact feat_lt Sz.ref.DF hn.2.1.1 hn.2.1.2.1 hn.2.1.2.2.1
    exact congrArg (Prod.mk (2 * g)) (ff_tie (.ff g) (mx_ne_b c.X) _ c.i hφ)
  | att g c =>
    obtain rfl := Option.some.inj e
    refine ⟨hn, ?_⟩
    obtain ⟨-, hv, ho⟩ := hn
    by_cases hC : IsC c
    · cases c with
      | c ρ jj b x =>
        show (2 * g + 1, Cm.Seg.plAtt (.c ρ jj b x)) = _
        unfold Cm.Seg.plAtt
        rw [addr_c DA KA ρ jj b x]
        exact congrArg (Prod.mk (2 * g + 1)) (as_tie g _)
      | _ => exact False.elim hC
    · have hφ := (phi_lt Sz.ref.DA c hv hC).1
      show (2 * g + 1, Cm.Seg.plAtt c) = _
      unfold Cm.Seg.plAtt
      rw [addr_feat DA KA c hC]
      rcases place_att_feat (S := Sz.ref) g hC ho with ⟨hm, e'⟩ | ⟨hm, e'⟩
      · rw [e', hm]
        rw [hm] at hφ
        exact congrArg (Prod.mk (2 * g + 1)) (ah_tie (.att g) _ _ hφ)
      · rw [e', hm]
        rw [hm] at hφ
        exact congrArg (Prod.mk (2 * g + 1)) (ao_tie (.att g) _ _ hφ)
  | hf φ i =>
    obtain rfl := Option.some.inj e
    obtain ⟨h1, h2⟩ := hn
    rw [n_hf] at h1
    refine ⟨⟨h1, h2⟩, ?_⟩
    show (24, Cm.Seg.stack Cm.Seg.colsHead 0 (Head.rowOf .hf φ i) (Head.colOf .hf φ)) = _
    refine congrArg (Prod.mk 24) ?_
    simp only [Head.rowOf, Head.colOf, Cm.Seg.perCol_hf, Cm.Seg.colsHead_eq, Name.place, Sz.atFeat,
      MatName.setPart, slot, kF_hf, wc_hf, lt_ref, Nat.reducePow]
    exact stack_multi _ _ _
  | hd φ i =>
    obtain rfl := Option.some.inj e
    obtain ⟨h1, h2⟩ := hn
    have hp := (Sz.part_lt ref_ok.1 (σ := .head) (μ := .hd) rfl h1).1
    simp only [kF_hd, wc_hd, Sz.np] at hp
    rw [n_hd] at h1
    refine ⟨⟨h1, h2⟩, ?_⟩
    show (24, Cm.Seg.stack Cm.Seg.colsHead 4 (Head.rowOf .hd φ i) (Head.colOf .hd φ)) = _
    refine congrArg (Prod.mk 24) ?_
    simp only [Head.rowOf, Head.colOf, Cm.Seg.perCol_hd, Cm.Seg.colsHead_eq, Name.place, Sz.atFeat,
      MatName.setPart, slot, kF_hd, wc_hd, lt_ref, Nat.reducePow]
    exact stack_single hp (by norm_num) (by norm_num)
  | hr φ i =>
    obtain rfl := Option.some.inj e
    obtain ⟨h1, h2⟩ := hn
    have hp := (Sz.part_lt ref_ok.1 (σ := .head) (μ := .hr) rfl h1).1
    simp only [kF_hr, wc_hr, Sz.np] at hp
    rw [n_hr] at h1
    refine ⟨⟨h1, h2⟩, ?_⟩
    show (24, Cm.Seg.stack Cm.Seg.colsHead 5 (Head.rowOf .hr φ i) (Head.colOf .hr φ)) = _
    refine congrArg (Prod.mk 24) ?_
    simp only [Head.rowOf, Head.colOf, Cm.Seg.perCol_hr, Cm.Seg.colsHead_eq, Name.place, Sz.atFeat,
      MatName.setPart, slot, kF_hr, wc_hr, lt_ref, Nat.reducePow]
    exact stack_single hp (by norm_num) (by norm_num)
  | bit σ t c j => exact absurd e (by simp [toCm])

/-! ## In an own matrix of cells, inside its shape, the two layings agree -/

/-- σ owns the matrix μ, and μ holds cells of the model's run, no planes: as in attention, and the
matrices of features that σ owns ("ownsFeat"). -/
def ownsCells : Seg → MatName → Bool
  | .att _, .as _ => true
  | σ, μ => ownsFeat σ μ

/-- A name that is valid in the library's layout with the head "Hd.main" is valid at the reference
numbers, and "toCm" gives it back. -/
theorem valid_ofCm (m : Cm.Seg.Name) (hm : m.Valid Cm.Seg.Hd.main) :
    (ofCm m).Valid Sz.ref ∧ toCm (ofCm m) = some m := by
  cases m with
  | ff g c => exact ⟨hm, rfl⟩
  | att g c => exact ⟨hm, rfl⟩
  | hf φ i => exact ⟨⟨by rw [n_hf]; exact hm.1, hm.2⟩, rfl⟩
  | hd φ i => exact ⟨⟨by rw [n_hd]; exact hm.1, hm.2⟩, rfl⟩
  | hr φ i => exact ⟨⟨by rw [n_hr]; exact hm.1, hm.2⟩, rfl⟩

/-- The cell at a name that is no bit is the library's cell of the trace at its name. -/
theorem get_toCm (X : Src) {n : Name} {m : Cm.Seg.Name} (e : toCm n = some m) :
    X.get n = Cm.Seg.get X.T m := by
  cases n <;> first | (obtain rfl := Option.some.inj e; rfl) | exact absurd e (by simp [toCm])

/-- A matrix whose shape has a row has a number in its segment's list. -/
theorem mu_of_inShape {S : Sz} {σ : Seg} {μ : MatName} {r : ℕ} (hr : r < (S.shape σ μ).1) :
    (S.mu σ μ).isSome = true := by
  by_contra hm
  have e0 : S.shape σ μ = (0, 0) := if_neg hm
  rw [e0] at hr
  exact absurd hr (Nat.not_lt_zero _)

/-- At the reference numbers no matrix has more than 65,536 rows. -/
theorem rows_le (μ : MatName) : Sz.ref.rows μ ≤ 65536 := by
  cases μ <;> norm_num [Sz.rows, Sz.wc, Sz.ref]

/-- A name that has a number in a segment's list has a part's number below the number of parts. -/
theorem part_lt_of_mu {S : Sz} {σ : Seg} {μ : MatName} (h : (S.mu σ μ).isSome = true) :
    μ.part < S.np μ := by
  have hσ := below_of_mu h
  unfold Sz.mu at h
  rw [if_pos hσ] at h
  cases σ <;> cases μ <;>
    first
      | exact Nat.one_pos
      | (simp [MatName.no?] at h; exact h)
      | simp [MatName.no?] at h

/-- A valid name at the reference numbers that is no bit is laid in a matrix with "ownsCells". -/
theorem ownsCells_place {n : Name} {m : Cm.Seg.Name} (e : toCm n = some m)
    (hn : n.Valid Sz.ref) : ownsCells (n.place Sz.ref).1 (n.place Sz.ref).2.1 = true := by
  cases n with
  | ff g c =>
    have key : ∀ (ν : FFSeg.Mx) (p : ℕ), ν ≠ .b → (ν = .xin → g = 0) →
        ownsCells (.ff g) ((famOf ν).setPart p) = true := by
      intro ν p h1 h2
      cases ν with
      | b => exact absurd rfl h1
      | xin =>
        obtain rfl := h2 rfl
        rfl
      | _ => rfl
    exact key c.X.mx _ (mx_ne_b c.X) (fun h => hn.2.2 (x0_of_xin h))
  | att g c =>
    by_cases hC : IsC c
    · cases c with
      | c ρ jj b x => rfl
      | _ => exact False.elim hC
    · rcases place_att_feat (S := Sz.ref) g hC hn.2.2 with ⟨-, e'⟩ | ⟨-, e'⟩ <;> rw [e'] <;> rfl
  | hf φ i => rfl
  | hd φ i => rfl
  | hr φ i => rfl
  | bit σ t c j => exact absurd e (by simp [toCm])

/-- At the reference numbers, two matrices with "ownsCells" in the list of one segment that have one
slot are one matrix. -/
theorem slot_inj {σ : Seg} {μ ν : MatName} (hμ : ownsCells σ μ = true)
    (hν : ownsCells σ ν = true) (mμ : (Sz.ref.mu σ μ).isSome = true)
    (mν : (Sz.ref.mu σ ν).isSome = true) (e : slot μ = slot ν) : μ = ν := by
  have b1 := part_lt_of_mu mμ
  have b2 := part_lt_of_mu mν
  cases σ <;> cases μ <;> cases ν <;>
    first
      | rfl
      | exact Bool.noConfusion hμ
      | exact Bool.noConfusion hν
      | (simp only [MatName.part, Sz.np, Sz.ref, slot] at b1 b2 e
         first | (subst e; rfl) | omega | (congr 1; omega))

/-- **At the reference numbers the laying by formula is the library's laying by choice.** For every
source X of cells, every matrix μ that its segment σ owns and that holds no planes ("ownsCells"),
and every row and column inside its shape: the entry of "lay" is the entry of "Cm.Seg.toMat" at the
head "Hd.main" and X's trace, in the segment's number, at row 65,536 times μ's slot plus r, and
column c. -/
theorem lay_ref_toMat (X : Src) (σ : Seg) (μ : MatName) (r c : ℕ)
    (ho : ownsCells σ μ = true) (hr : r < (Sz.ref.shape σ μ).1) (hc : c < (Sz.ref.shape σ μ).2) :
    lay Sz.ref X σ μ r c =
      Cm.Seg.toMat Cm.Seg.Hd.main X.T (σ.no 12) (slot μ * 65536 + r) c := by
  have hOK : Cm.Seg.Hd.main.OK := ⟨le_refl _, le_refl _⟩
  have hm := mu_of_inShape hr
  have hσ : σ.Below 12 := below_of_mu hm
  have hs : Sz.ref.shape σ μ = (Sz.ref.rows μ, Sz.ref.k σ μ) := if_pos hm
  have hown : Sz.ref.owner σ μ = (σ, μ) := by
    cases σ with
    | ff g =>
      cases μ with
      | xbI => exact if_pos (by simpa [ownsCells, ownsFeat] using ho)
      | _ => rfl
    | att g => cases μ <;> first | rfl | exact Bool.noConfusion ho
    | head => cases μ <;> first | rfl | exact Bool.noConfusion ho
  unfold lay
  rw [if_pos ⟨hr, hc⟩, hown]
  show (match Sz.ref.nameAt σ μ r c with
    | some n => X.get n
    | none => 0) = _
  cases hN : Sz.ref.nameAt σ μ r c with
  | some n =>
    obtain ⟨hv, hp⟩ := nameAt_back Sz.ref ref_ok.1 σ μ r c n hN
    obtain ⟨m, hm'⟩ : ∃ m, toCm n = some m := by
      cases n with
      | bit σ' t c' j =>
        exfalso
        have e1 : σ' = σ := congrArg Prod.fst hp
        have e2 : planeOf σ' = μ := congrArg (fun q : Place => q.2.1) hp
        rw [← e2, e1] at ho
        cases σ <;> exact Bool.noConfusion ho
      | _ => exact ⟨_, rfl⟩
    obtain ⟨hmv, hmp⟩ := cm_place n m hm' hv
    rw [hp] at hmp
    have h1 := Cm.lay_toMat_place Cm.Seg.Hd.main hOK X.T m hmv
    rw [hmp] at h1
    exact (get_toCm X hm').trans h1.symm
  | none =>
    refine (Cm.lay_toMat_off Cm.Seg.Hd.main X.T (σ.no 12, slot μ * 65536 + r, c) ?_).symm
    rintro ⟨m, hmv, hmp⟩
    obtain ⟨hv, ht⟩ := valid_ofCm m hmv
    obtain ⟨-, hp⟩ := cm_place (ofCm m) m ht hv
    rw [hmp] at hp
    have hin' := place_inShape Sz.ref ref_ok.1 _ hv
    have hb := nameAt_place Sz.ref ref_ok.1 _ hv
    have ho' := ownsCells_place ht hv
    generalize (ofCm m).place Sz.ref = q at hp hin' hb ho'
    obtain ⟨σ', μ', r', c'⟩ := q
    simp only at hp hin' hb ho'
    obtain ⟨e1, e23⟩ := Prod.mk.inj hp
    obtain ⟨e2, e3⟩ := Prod.mk.inj e23
    have hm2 := mu_of_inShape hin'.1
    obtain rfl : σ = σ' := Seg.no_inj hσ (below_of_mu hm2) e1
    have hs2 : Sz.ref.shape σ μ' = (Sz.ref.rows μ', Sz.ref.k σ μ') := if_pos hm2
    have b1 : r < 65536 := by
      have := rows_le μ
      rw [hs] at hr
      exact Nat.lt_of_lt_of_le hr this
    have b2 : r' < 65536 := by
      have := rows_le μ'
      have h2 := hin'.1
      rw [hs2] at h2
      exact Nat.lt_of_lt_of_le h2 this
    have es : slot μ = slot μ' ∧ r = r' := by omega
    obtain rfl : μ = μ' := slot_inj ho ho' hm hm2 es.1
    rw [← es.2, ← e3, hN] at hb
    exact absurd hb (by simp)

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.kF_af
#print axioms OnBytes.HonestTrace.kF_ad
#print axioms OnBytes.HonestTrace.kF_ar
#print axioms OnBytes.HonestTrace.kF_qa
#print axioms OnBytes.HonestTrace.kF_xbO
#print axioms OnBytes.HonestTrace.kF_xbI
#print axioms OnBytes.HonestTrace.kF_as
#print axioms OnBytes.HonestTrace.kF_ah
#print axioms OnBytes.HonestTrace.kF_ao
#print axioms OnBytes.HonestTrace.kF_hf
#print axioms OnBytes.HonestTrace.kF_hd
#print axioms OnBytes.HonestTrace.kF_hr
#print axioms OnBytes.HonestTrace.ref_DA
#print axioms OnBytes.HonestTrace.wc_af
#print axioms OnBytes.HonestTrace.wc_ad
#print axioms OnBytes.HonestTrace.wc_ar
#print axioms OnBytes.HonestTrace.wc_qa
#print axioms OnBytes.HonestTrace.wc_xbO
#print axioms OnBytes.HonestTrace.wc_xbI
#print axioms OnBytes.HonestTrace.wc_ah
#print axioms OnBytes.HonestTrace.wc_ao
#print axioms OnBytes.HonestTrace.wc_hf
#print axioms OnBytes.HonestTrace.wc_hd
#print axioms OnBytes.HonestTrace.wc_hr
#print axioms OnBytes.HonestTrace.lt_ref
#print axioms OnBytes.HonestTrace.T_DF
#print axioms OnBytes.HonestTrace.NAd_ref
#print axioms OnBytes.HonestTrace.NAs_ref
#print axioms OnBytes.HonestTrace.lmS_ref
#print axioms OnBytes.HonestTrace.n_hf
#print axioms OnBytes.HonestTrace.n_hd
#print axioms OnBytes.HonestTrace.n_hr
#print axioms OnBytes.HonestTrace.T_DA
#print axioms OnBytes.HonestTrace.fBig_DF
#print axioms OnBytes.HonestTrace.fAd_DF
#print axioms OnBytes.HonestTrace.fAr_DF
#print axioms OnBytes.HonestTrace.feat_ref
#print axioms OnBytes.HonestTrace.valid_ref
#print axioms OnBytes.HonestTrace.stack_single
#print axioms OnBytes.HonestTrace.stack_multi
#print axioms OnBytes.HonestTrace.ff_tie
#print axioms OnBytes.HonestTrace.ah_tie
#print axioms OnBytes.HonestTrace.ao_tie
#print axioms OnBytes.HonestTrace.as_tie
#print axioms OnBytes.HonestTrace.cm_place
#print axioms OnBytes.HonestTrace.valid_ofCm
#print axioms OnBytes.HonestTrace.get_toCm
#print axioms OnBytes.HonestTrace.mu_of_inShape
#print axioms OnBytes.HonestTrace.rows_le
#print axioms OnBytes.HonestTrace.part_lt_of_mu
#print axioms OnBytes.HonestTrace.ownsCells_place
#print axioms OnBytes.HonestTrace.slot_inj
#print axioms OnBytes.HonestTrace.lay_ref_toMat
