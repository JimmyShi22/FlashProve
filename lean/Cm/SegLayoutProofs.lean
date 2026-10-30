-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegLayoutProofs.lean: proofs of the statements of Cm/SegLayout.lean (where every cell of the
model is in the 25 matrices of cells), each proved as it is stated there.

Row and column of a cell inside a matrix are the addresses of Inst/Model/ (`FFSeg.addr`,
`AttSeg.addr`); that those of a valid cell are inside that matrix and that no two valid cells share
matrix, row and column is proved, for sizes that are `OK` (as the reference sizes are:
`FFSeg.ref_ok`, `AttSeg.ref_dim_ok`), in Inst/Model/FF/IndexFacts.lean and
Inst/Model/Att/AddrFacts.lean (`addrRange`, `addrInj`); for the head both are arithmetic. This
file's own part is the stacking in slots (`stack_inj`), the figures of the shapes, and the
bookkeeping of owners and kept rows.
Limits: this file says nothing on conditions, codes or protocols, but for `lay_valid_refK`
(Cm/SegLayout.lean, Limits).
Terms: lean/GLOSSARY.md.
-/
import Cm.SegLayout
import Inst.Model.FF.IndexFacts
import Inst.Model.Att.AddrFacts

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg

open Inst.Model Inst.Model.All

/-! ## Figures -/

theorem hSlot_eq : hSlot = 65536 := by decide
theorem colsFF_eq : colsFF = 5990 := FFSeg.ref_shapes.1
theorem colsAtt_eq : colsAtt = 7200 := AttSeg.ref_cols.1
theorem colsHead_eq : colsHead = 4816 := by decide
theorem nGr_eq : nGr = 12 := rfl
theorem nSeg_eq : nSeg = 25 := rfl
theorem nT_eq : Head.nT = 1024 := rfl
theorem nFeat_hf : Head.nFeat .hf = 1232768 := rfl
theorem nFeat_hd : Head.nFeat .hd = 10240 := rfl
theorem nFeat_hr : Head.nFeat .hr = 120 := rfl
theorem nFeat_x : Head.nFeat .x = 25600 := rfl
theorem perCol_hf : Head.perCol .hf = 64 := by decide
theorem perCol_hd : Head.perCol .hd = 16 := by decide
theorem perCol_hr : Head.perCol .hr = 8 := by decide

theorem ffRow_af : 2 ^ FFSeg.lRow DF .af = 65536 := by decide
theorem ffRow_ad : 2 ^ FFSeg.lRow DF .ad = 32768 := by decide
theorem ffRow_ar : 2 ^ FFSeg.lRow DF .ar = 8192 := by decide
theorem ffRow_qa : 2 ^ FFSeg.lRow DF .qa = 65536 := by decide
theorem ffRow_xin : 2 ^ FFSeg.lRow DF .xin = 65536 := by decide
theorem ffRow_xout : 2 ^ FFSeg.lRow DF .xout = 65536 := by decide
theorem attRow_as : 2 ^ AttSeg.lRow DA KA .as = 65536 := by decide
theorem attRow_ah : 2 ^ AttSeg.lRow DA KA .ah = 8192 := by decide
theorem attRow_ao : 2 ^ AttSeg.lRow DA KA .ao = 65536 := by decide

theorem rowsLog_even {s : ℕ} (h : s % 2 = 0) : 2 ^ rowsLog s = 524288 := by
  unfold rowsLog
  rw [if_neg (by omega)]
  norm_num
theorem rowsLog_odd {s : ℕ} (h : s % 2 = 1) : 2 ^ rowsLog s = 262144 := by
  unfold rowsLog
  rw [if_pos h]
  norm_num
theorem cols_ff {g : ℕ} (h : g < 12) : cols (2 * g) = 5990 := by
  unfold cols
  rw [if_neg (by omega), if_neg (by omega), colsFF_eq]
theorem cols_att (g : ℕ) : cols (2 * g + 1) = 7200 := by
  unfold cols
  rw [if_neg (by omega), if_pos (by omega), colsAtt_eq]
theorem cols_head : cols 24 = 4816 := by
  unfold cols
  rw [if_pos rfl, colsHead_eq]

/-! ## Slots -/

theorem stack_inj {W s r c s' r' c' : ℕ} (hr : r < hSlot) (hr' : r' < hSlot)
    (h : stack W s r c = stack W s' r' c') :
    s + c / W = s' + c' / W ∧ r = r' ∧ c % W = c' % W := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  obtain ⟨e1, e2⟩ := FFSeg.IndexFacts.mr_inj hr hr' h1
  exact ⟨e1, e2, h2⟩

/-! ## Feed-forward and attention segments: where a matrix of Inst/Model/ is -/

/-- matrix, row and column of a valid cell of a feed-forward segment: the six cases with their
figures -/
theorem ff_addr (c : FFSeg.Cell) (hc : c.Valid DF) :
    ((FFSeg.addr DF c).1 = .af ∧ (FFSeg.addr DF c).2.1 < 65536 ∧ (FFSeg.addr DF c).2.2 < 17970) ∨
    ((FFSeg.addr DF c).1 = .ad ∧ (FFSeg.addr DF c).2.1 < 65536 ∧ (FFSeg.addr DF c).2.2 < 3200) ∨
    ((FFSeg.addr DF c).1 = .ar ∧ (FFSeg.addr DF c).2.1 < 65536 ∧ (FFSeg.addr DF c).2.2 < 324) ∨
    ((FFSeg.addr DF c).1 = .qa ∧ (FFSeg.addr DF c).2.1 < 65536 ∧ (FFSeg.addr DF c).2.2 < 1536) ∨
    ((FFSeg.addr DF c).1 = .xin ∧ (FFSeg.addr DF c).2.1 < 65536 ∧ (FFSeg.addr DF c).2.2 < 400) ∨
    ((FFSeg.addr DF c).1 = .xout ∧
      (FFSeg.addr DF c).2.1 < 65536 ∧
      (FFSeg.addr DF c).2.2 < 400) := by
  obtain ⟨h1, h2⟩ := FFSeg.IndexFacts.addrRange DF FFSeg.ref_ok c hc
  have hb : (FFSeg.addr DF c).1 ≠ .b := FFSeg.IndexFacts.mx_ne_b c.X
  obtain ⟨-, s1, s2, s3, -, s5, s6, s7, -⟩ := FFSeg.ref_shapes
  generalize FFSeg.addr DF c = a at h1 h2 hb ⊢
  obtain ⟨μ, r, col⟩ := a
  cases μ with
  | af =>
    have h1' : r < 2 ^ FFSeg.lRow DF .af := h1
    have h2' : col < FFSeg.nCol DF .af := h2
    rw [ffRow_af] at h1'
    rw [s1] at h2'
    exact Or.inl ⟨rfl, h1', h2'⟩
  | ad =>
    have h1' : r < 2 ^ FFSeg.lRow DF .ad := h1
    have h2' : col < FFSeg.nCol DF .ad := h2
    rw [ffRow_ad] at h1'
    rw [s2] at h2'
    exact Or.inr (Or.inl ⟨rfl, lt_trans h1' (by norm_num), h2'⟩)
  | ar =>
    have h1' : r < 2 ^ FFSeg.lRow DF .ar := h1
    have h2' : col < FFSeg.nCol DF .ar := h2
    rw [ffRow_ar] at h1'
    rw [s3] at h2'
    exact Or.inr (Or.inr (Or.inl ⟨rfl, lt_trans h1' (by norm_num), h2'⟩))
  | b => exact absurd rfl hb
  | qa =>
    have h1' : r < 2 ^ FFSeg.lRow DF .qa := h1
    have h2' : col < FFSeg.nCol DF .qa := h2
    rw [ffRow_qa] at h1'
    rw [s5] at h2'
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1', h2'⟩)))
  | xin =>
    have h1' : r < 2 ^ FFSeg.lRow DF .xin := h1
    have h2' : col < FFSeg.nCol DF .xin := h2
    rw [ffRow_xin] at h1'
    rw [s6] at h2'
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1', h2'⟩))))
  | xout =>
    have h1' : r < 2 ^ FFSeg.lRow DF .xout := h1
    have h2' : col < FFSeg.nCol DF .xout := h2
    rw [ffRow_xout] at h1'
    rw [s7] at h2'
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h1', h2'⟩))))

/-- the same for a valid own cell of an attention segment: the three cases -/
theorem att_addr (c : AttSeg.Raw) (hc : c.Valid DA) (ho : c.Own = true) :
    ((AttSeg.addr DA KA c).1 = .as ∧
      (AttSeg.addr DA KA c).2.1 < 65536 ∧
      (AttSeg.addr DA KA c).2.2 < 7200) ∨
    ((AttSeg.addr DA KA c).1 = .ah ∧
      (AttSeg.addr DA KA c).2.1 < 65536 ∧
      (AttSeg.addr DA KA c).2.2 < 360) ∨
    ((AttSeg.addr DA KA c).1 = .ao ∧
      (AttSeg.addr DA KA c).2.1 < 65536 ∧
      (AttSeg.addr DA KA c).2.2 < 640) := by
  obtain ⟨h1, h2⟩ := AttSeg.AddrFacts.addrRange DA KA AttSeg.Calls.ref AttSeg.ref_dim_ok c hc
  have hm : (AttSeg.addr DA KA c).1 = .as ∨
      (AttSeg.addr DA KA c).1 = .ah ∨
      (AttSeg.addr DA KA c).1 = .ao := by
    cases c with
    | c ρ jj b x => cases ρ <;> exact Or.inl rfl
    | mx k b g i => exact Or.inr (Or.inl rfl)
    | den k b g i => exact Or.inr (Or.inl rfl)
    | ib k b g i => exact Or.inr (Or.inl rfl)
    | qh b g i n => exact Or.inr (Or.inr rfl)
    | qh' b g i n => exact Or.inr (Or.inr rfl)
    | qry k b g i n => exact absurd ho Bool.false_ne_true
    | out k b g i n => exact absurd ho Bool.false_ne_true
    | key k lam g j n => exact absurd ho Bool.false_ne_true
    | val k lam g j n => exact absurd ho Bool.false_ne_true
  obtain ⟨s1, s2, s3, -, -⟩ := AttSeg.ref_cols
  generalize AttSeg.addr DA KA c = a at h1 h2 hm ⊢
  obtain ⟨μ, r, col⟩ := a
  rcases hm with hm | hm | hm
  · have hm' : μ = .as := hm
    subst hm'
    have h1' : r < 2 ^ AttSeg.lRow DA KA .as := h1
    have h2' : col < AttSeg.nCol DA KA AttSeg.Calls.ref .as := h2
    rw [attRow_as] at h1'
    rw [s1] at h2'
    exact Or.inl ⟨rfl, h1', h2'⟩
  · have hm' : μ = .ah := hm
    subst hm'
    have h1' : r < 2 ^ AttSeg.lRow DA KA .ah := h1
    have h2' : col < AttSeg.nCol DA KA AttSeg.Calls.ref .ah := h2
    rw [attRow_ah] at h1'
    rw [s2] at h2'
    exact Or.inr (Or.inl ⟨rfl, lt_trans h1' (by norm_num), h2'⟩)
  · have hm' : μ = .ao := hm
    subst hm'
    have h1' : r < 2 ^ AttSeg.lRow DA KA .ao := h1
    have h2' : col < AttSeg.nCol DA KA AttSeg.Calls.ref .ao := h2
    rw [attRow_ao] at h1'
    rw [s3] at h2'
    exact Or.inr (Or.inr ⟨rfl, h1', h2'⟩)

theorem plFF_in (c : FFSeg.Cell) (hc : c.Valid DF) : (plFF c).1 < 524288 ∧ (plFF c).2 < 5990 := by
  have B := ff_addr c hc
  unfold plFF stack
  rw [hSlot_eq, colsFF_eq]
  generalize FFSeg.addr DF c = a at B ⊢
  obtain ⟨μ, r, col⟩ := a
  refine ⟨?_, Nat.mod_lt _ (by norm_num)⟩
  rcases B with ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩
    <;>
    (simp only at e b1 b2; subst e; simp only [slotFF]; omega)

theorem plFF_inj (c c' : FFSeg.Cell) (hc : c.Valid DF) (hc' : c'.Valid DF) (h : plFF c = plFF c') :
    c = c' := by
  apply FFSeg.IndexFacts.addrInj DF FFSeg.ref_ok c c' hc hc'
  have B := ff_addr c hc
  have B' := ff_addr c' hc'
  unfold plFF at h
  generalize FFSeg.addr DF c = a at B h ⊢
  generalize FFSeg.addr DF c' = a' at B' h ⊢
  obtain ⟨μ, r, col⟩ := a
  obtain ⟨μ', r', col'⟩ := a'
  simp only at B B' h
  have hr : r < hSlot := by rw [hSlot_eq]; omega
  have hr' : r' < hSlot := by rw [hSlot_eq]; omega
  obtain ⟨e1, e2, e3⟩ := stack_inj hr hr' h
  rw [colsFF_eq] at e1 e3
  subst e2
  rcases B with ⟨e, -, b2⟩ | ⟨e, -, b2⟩ | ⟨e, -, b2⟩ | ⟨e, -, b2⟩ | ⟨e, -, b2⟩ | ⟨e, -, b2⟩ <;>
    rcases B' with ⟨e', -, b2'⟩ | ⟨e', -, b2'⟩ | ⟨e', -, b2'⟩ | ⟨e', -,
        b2'⟩ | ⟨e', -, b2'⟩ | ⟨e', -, b2'⟩ <;>
    subst e <;> subst e' <;> simp only [slotFF] at e1 <;>
    first
      | (exfalso; omega)
      | (have ec : col = col' := by omega
         subst ec
         rfl)

theorem plAtt_in (c : AttSeg.Raw) (hc : c.Valid DA) (ho : c.Own = true) :
    (plAtt c).1 < 262144 ∧ (plAtt c).2 < 7200 := by
  have B := att_addr c hc ho
  unfold plAtt stack
  rw [hSlot_eq, colsAtt_eq]
  generalize AttSeg.addr DA KA c = a at B ⊢
  obtain ⟨μ, r, col⟩ := a
  refine ⟨?_, Nat.mod_lt _ (by norm_num)⟩
  rcases B with ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ <;>
    (simp only at e b1 b2; subst e; simp only [slotAtt]; omega)

theorem plAtt_inj (c c' : AttSeg.Raw) (hc : c.Valid DA) (hc' : c'.Valid DA) (ho : c.Own = true)
    (ho' : c'.Own = true) (h : plAtt c = plAtt c') : c = c' := by
  apply AttSeg.AddrFacts.addrInj DA KA AttSeg.ref_dim_ok c c' hc hc'
  have B := att_addr c hc ho
  have B' := att_addr c' hc' ho'
  unfold plAtt at h
  generalize AttSeg.addr DA KA c = a at B h ⊢
  generalize AttSeg.addr DA KA c' = a' at B' h ⊢
  obtain ⟨μ, r, col⟩ := a
  obtain ⟨μ', r', col'⟩ := a'
  simp only at B B' h
  have hr : r < hSlot := by rw [hSlot_eq]; omega
  have hr' : r' < hSlot := by rw [hSlot_eq]; omega
  obtain ⟨e1, e2, e3⟩ := stack_inj hr hr' h
  rw [colsAtt_eq] at e1 e3
  subst e2
  rcases B with ⟨e, -, b2⟩ | ⟨e, -, b2⟩ | ⟨e, -, b2⟩ <;>
    rcases B' with ⟨e', -, b2'⟩ | ⟨e', -, b2'⟩ | ⟨e', -, b2'⟩ <;>
    subst e <;> subst e' <;> simp only [slotAtt] at e1 <;>
    first
      | (exfalso; omega)
      | (have ec : col = col' := by omega
         subst ec
         rfl)

/-! ## The head -/

theorem rowHf (φ : ℕ) {i : ℕ} (hi : i < 1024) : Head.rowOf .hf φ i < hSlot := by
  rw [hSlot_eq]
  simp only [Head.rowOf, perCol_hf]
  omega
theorem rowHd (φ : ℕ) {i : ℕ} (hi : i < 1024) : Head.rowOf .hd φ i < hSlot := by
  rw [hSlot_eq]
  simp only [Head.rowOf, perCol_hd]
  omega
theorem rowHr (φ : ℕ) {i : ℕ} (hi : i < 1024) : Head.rowOf .hr φ i < hSlot := by
  rw [hSlot_eq]
  simp only [Head.rowOf, perCol_hr]
  omega

/-! ## Owners -/

theorem ownFF_own {g : ℕ} {c : FFSeg.Cell} (h : c.X = .x0 → g = 0) : ownFF g c = .ff g c := by
  unfold ownFF
  rw [if_neg]
  rintro ⟨hx, hg⟩
  have := h hx
  omega

theorem ownFF_cases (g : ℕ) (c : FFSeg.Cell) :
    ownFF g c = .ff g c ∨ (0 < g ∧ c.X = .x0 ∧ ownFF g c = .ff (g - 1) { c with X := .x8 }) := by
  unfold ownFF
  by_cases h : c.X = .x0 ∧ 0 < g
  · rw [if_pos h]
    exact Or.inr ⟨h.2, h.1, rfl⟩
  · rw [if_neg h]
    exact Or.inl rfl

theorem ownAtt_own {g : ℕ} {c : AttSeg.Raw} (h : c.Own = true) : ownAtt g c = .att g c := by
  cases c <;> first | rfl | exact absurd h Bool.false_ne_true

theorem ownAtt_cases (g : ℕ) (c : AttSeg.Raw) :
    ownAtt g c = .att g c ∨ ∃ c' : FFSeg.Cell, ownAtt g c = .ff g c' ∧ c'.X.mx = .qa := by
  cases c <;> first | exact Or.inl rfl | exact Or.inr ⟨_, rfl, rfl⟩

theorem vFF_eq (T : Trace) (g : ℕ) (c : FFSeg.Cell) : T.vFF g c = get T (ownFF g c) := by
  unfold Trace.vFF ownFF
  split_ifs <;> rfl

theorem vAtt_eq (T : Trace) (g : ℕ) (c : AttSeg.Raw) : T.vAtt g c = get T (ownAtt g c) := by
  cases c <;> rfl

theorem ownFF_valid (h : Hd) {g : ℕ} (hg : g < nGr) {c : FFSeg.Cell} (hc : c.Valid DF) :
    (ownFF g c).Valid h := by
  rcases ownFF_cases g c with e | ⟨h0, hx, e⟩
  · rw [e]
    refine ⟨hg, hc, fun hx => ?_⟩
    by_contra hne
    have e' : ownFF g c = .ff (g - 1) { c with X := .x8 } := by
      unfold ownFF
      rw [if_pos ⟨hx, Nat.pos_of_ne_zero hne⟩]
    rw [e] at e'
    injection e' with e1 _
    omega
  · rw [e]
    obtain ⟨X, k, inst, j, i⟩ := c
    have hx' : X = .x0 := hx
    subst hx'
    exact ⟨lt_of_le_of_lt (Nat.sub_le _ _) hg, hc, fun hh => by cases hh⟩

theorem ownAtt_valid (h : Hd) {g : ℕ} (hg : g < nGr) {c : AttSeg.Raw} (hc : c.Valid DA) :
    (ownAtt g c).Valid h := by
  have ech : DA.ch = 128 := by decide
  have enH : DA.nH = 40 := by decide
  have enG : DA.nG = 8 := by decide
  cases c with
  | c ρ jj b x => exact ⟨hg, hc, rfl⟩
  | mx k b g' i => exact ⟨hg, hc, rfl⟩
  | den k b g' i => exact ⟨hg, hc, rfl⟩
  | ib k b g' i => exact ⟨hg, hc, rfl⟩
  | qh b g' i n => exact ⟨hg, hc, rfl⟩
  | qh' b g' i n => exact ⟨hg, hc, rfl⟩
  | qry k b g' i n =>
    obtain ⟨hk, hb, hg', hi, hn⟩ := hc
    have h1 := AttSeg.AddrFacts.head_lt DA hb hg'
    rw [enH] at h1
    rw [ech] at hn
    refine ⟨hg, ⟨hk, AttSeg.AddrFacts.lam_lt DA hb, ?_, hi⟩, fun hh => by cases hh⟩
    show DA.ch * DA.head g' b + n < 5120
    rw [ech]
    omega
  | out k b g' i n =>
    obtain ⟨hk, hb, hg', hi, hn⟩ := hc
    have h1 := AttSeg.AddrFacts.head_lt DA hb hg'
    rw [enH] at h1
    rw [ech] at hn
    refine ⟨hg, ⟨hk, AttSeg.AddrFacts.lam_lt DA hb, ?_, hi⟩, fun hh => by cases hh⟩
    show DA.ch * DA.head g' b + n < 5120
    rw [ech]
    omega
  | key k lam g' j n =>
    obtain ⟨hk, hl, hg', hj, hn⟩ := hc
    rw [enG] at hg'
    rw [ech] at hn
    refine ⟨hg, ⟨hk, hl, ?_, hj⟩, fun hh => by cases hh⟩
    show DA.ch * g' + n < 1024
    rw [ech]
    omega
  | val k lam g' j n =>
    obtain ⟨hk, hl, hg', hj, hn⟩ := hc
    rw [enG] at hg'
    rw [ech] at hn
    refine ⟨hg, ⟨hk, hl, ?_, hj⟩, fun hh => by cases hh⟩
    show DA.ch * g' + n < 1024
    rw [ech]
    omega

theorem ownX_valid (h : Hd) {φ i : ℕ} (hφ : φ < Head.nFeat .x) (hi : i < Head.nT) :
    (ownX φ i).Valid h := by
  rw [nFeat_x] at hφ
  refine ⟨by decide, ⟨?_, ?_, ?_, hi⟩, fun hh => by cases hh⟩
  · show φ / 5120 < 5
    omega
  · show 0 < 1
    omega
  · show φ % 5120 < 5120
    omega

/-! ## Rows of the two slots that are kept -/

theorem plFF_row (c : FFSeg.Cell) (hc : c.Valid DF) : (FFSeg.addr DF c).2.1 < hSlot := by
  rw [hSlot_eq]
  rcases ff_addr c hc with ⟨_, b, _⟩ | ⟨_, b, _⟩ | ⟨_, b, _⟩ | ⟨_, b, _⟩ | ⟨_, b, _⟩ | ⟨_, b, _⟩
    <;> exact b

theorem plFF_row_qa (c : FFSeg.Cell) (hc : c.Valid DF) (hm : c.X.mx = .qa) :
    (plFF c).1 = 5 * hSlot + (FFSeg.addr DF c).2.1 := by
  have e0 : (FFSeg.addr DF c).1 = .qa := hm
  have hb : (FFSeg.addr DF c).2.2 < 1536 := by
    rcases ff_addr c hc with ⟨e, _, b⟩ | ⟨e, _, b⟩ | ⟨e, _, b⟩ | ⟨e, _, b⟩ | ⟨e, _, b⟩ | ⟨e, _, b⟩
      <;>
      first | exact b | exact absurd (e0.symm.trans e) (by decide)
  unfold plFF stack
  rw [e0, colsFF_eq, Nat.div_eq_of_lt (by omega)]
  rfl

theorem plFF_row_xout (c : FFSeg.Cell) (hc : c.Valid DF) (hm : c.X.mx = .xout) :
    (plFF c).1 = 7 * hSlot + (FFSeg.addr DF c).2.1 := by
  have e0 : (FFSeg.addr DF c).1 = .xout := hm
  have hb : (FFSeg.addr DF c).2.2 < 400 := by
    rcases ff_addr c hc with ⟨e, _, b⟩ | ⟨e, _, b⟩ | ⟨e, _, b⟩ | ⟨e, _, b⟩ | ⟨e, _, b⟩ | ⟨e, _, b⟩
      <;>
      first | exact absurd (e0.symm.trans e) (by decide) | exact b
  unfold plFF stack
  rw [e0, colsFF_eq, Nat.div_eq_of_lt (by omega)]
  rfl

theorem mem_slotRows (s slot : ℕ) {r : ℕ} (hr : r < hSlot) :
    (s, slot * hSlot + r) ∈ slotRows s slot :=
  Finset.mem_image.2 ⟨r, Finset.mem_range.2 hr, rfl⟩

theorem mem_kept_xout {g k r : ℕ} (hg : g < 12) (h1 : 2 * g ≤ k)
    (h2 : k < 2 * g + 2) (hr : r < hSlot) :
    (2 * g, 7 * hSlot + r) ∈ kept k := by
  unfold kept
  rw [if_pos (by omega)]
  by_cases hk : k % 2 = 0
  · rw [if_pos hk]
    have e : k = 2 * g := by omega
    subst e
    exact Finset.mem_union_right _ (mem_slotRows _ 7 hr)
  · rw [if_neg hk]
    have e : k - 1 = 2 * g := by omega
    rw [e]
    exact mem_slotRows _ 7 hr

theorem mem_kept_qa {g r : ℕ} (hg : g < 12) (hr : r < hSlot) :
    (2 * g, 5 * hSlot + r) ∈ kept (2 * g) := by
  unfold kept
  rw [if_pos (by omega), if_pos (by omega)]
  exact Finset.mem_union_left _ (mem_slotRows _ 5 hr)

end Cm.Seg

namespace Cm
open Seg Inst.Model Inst.Model.All

theorem lay_figures : Spec.lay_figures :=
  ⟨hSlot_eq, colsFF_eq, colsAtt_eq, colsHead_eq, ⟨le_refl _, le_refl _⟩, ⟨by decide, by decide⟩⟩

theorem lay_inShape : Spec.lay_inShape := by
  intro h hOK n hn
  obtain ⟨ok1, ok2⟩ := hOK
  rw [nFeat_hf] at ok1
  rw [nFeat_hr] at ok2
  cases n with
  | ff g c =>
    obtain ⟨hg, hc, -⟩ := hn
    rw [nGr_eq] at hg
    obtain ⟨b1, b2⟩ := plFF_in c hc
    refine ⟨?_, ?_, ?_⟩
    · show 2 * g < nSeg
      rw [nSeg_eq]
      omega
    · show (plFF c).1 < 2 ^ rowsLog (2 * g)
      rw [rowsLog_even (by omega)]
      exact b1
    · show (plFF c).2 < cols (2 * g)
      rw [cols_ff hg]
      exact b2
  | att g c =>
    obtain ⟨hg, hc, ho⟩ := hn
    rw [nGr_eq] at hg
    obtain ⟨b1, b2⟩ := plAtt_in c hc ho
    refine ⟨?_, ?_, ?_⟩
    · show 2 * g + 1 < nSeg
      rw [nSeg_eq]
      omega
    · show (plAtt c).1 < 2 ^ rowsLog (2 * g + 1)
      rw [rowsLog_odd (by omega)]
      exact b1
    · show (plAtt c).2 < cols (2 * g + 1)
      rw [cols_att]
      exact b2
  | hf φ i =>
    obtain ⟨hφ, hi⟩ := hn
    rw [nT_eq] at hi
    refine ⟨(by decide : 24 < nSeg), ?_, ?_⟩
    · show (0 + Head.colOf .hf φ / colsHead) * hSlot + Head.rowOf .hf φ i < 2 ^ rowsLog 24
      rw [rowsLog_even (by norm_num), hSlot_eq, colsHead_eq]
      simp only [Head.rowOf, Head.colOf, perCol_hf]
      omega
    · show Head.colOf .hf φ % colsHead < cols 24
      rw [cols_head, colsHead_eq]
      exact Nat.mod_lt _ (by norm_num)
  | hd φ i =>
    obtain ⟨hφ, hi⟩ := hn
    rw [nT_eq] at hi
    rw [nFeat_hd] at hφ
    refine ⟨(by decide : 24 < nSeg), ?_, ?_⟩
    · show (4 + Head.colOf .hd φ / colsHead) * hSlot + Head.rowOf .hd φ i < 2 ^ rowsLog 24
      rw [rowsLog_even (by norm_num), hSlot_eq, colsHead_eq]
      simp only [Head.rowOf, Head.colOf, perCol_hd]
      omega
    · show Head.colOf .hd φ % colsHead < cols 24
      rw [cols_head, colsHead_eq]
      exact Nat.mod_lt _ (by norm_num)
  | hr φ i =>
    obtain ⟨hφ, hi⟩ := hn
    rw [nT_eq] at hi
    refine ⟨(by decide : 24 < nSeg), ?_, ?_⟩
    · show (5 + Head.colOf .hr φ / colsHead) * hSlot + Head.rowOf .hr φ i < 2 ^ rowsLog 24
      rw [rowsLog_even (by norm_num), hSlot_eq, colsHead_eq]
      simp only [Head.rowOf, Head.colOf, perCol_hr]
      omega
    · show Head.colOf .hr φ % colsHead < cols 24
      rw [cols_head, colsHead_eq]
      exact Nat.mod_lt _ (by norm_num)

theorem lay_inj : Spec.lay_inj := by
  intro h hOK n n' hn hn' e
  obtain ⟨ok1, ok2⟩ := hOK
  rw [nFeat_hf] at ok1
  rw [nFeat_hr] at ok2
  cases n with
  | ff g c =>
    obtain ⟨hg, hc, -⟩ := hn
    rw [nGr_eq] at hg
    cases n' with
    | ff g' c' =>
      obtain ⟨hg', hc', -⟩ := hn'
      obtain ⟨e1, e2⟩ := Prod.mk.inj e
      have eg : g = g' := by omega
      subst eg
      rw [plFF_inj c c' hc hc' e2]
    | att g' c' => exact absurd (Prod.mk.inj e).1 (by omega)
    | hf φ i => exact absurd (Prod.mk.inj e).1 (by omega)
    | hd φ i => exact absurd (Prod.mk.inj e).1 (by omega)
    | hr φ i => exact absurd (Prod.mk.inj e).1 (by omega)
  | att g c =>
    obtain ⟨hg, hc, ho⟩ := hn
    rw [nGr_eq] at hg
    cases n' with
    | ff g' c' => exact absurd (Prod.mk.inj e).1 (by omega)
    | att g' c' =>
      obtain ⟨hg', hc', ho'⟩ := hn'
      obtain ⟨e1, e2⟩ := Prod.mk.inj e
      have eg : g = g' := by omega
      subst eg
      rw [plAtt_inj c c' hc hc' ho ho' e2]
    | hf φ i => exact absurd (Prod.mk.inj e).1 (by omega)
    | hd φ i => exact absurd (Prod.mk.inj e).1 (by omega)
    | hr φ i => exact absurd (Prod.mk.inj e).1 (by omega)
  | hf φ i =>
    obtain ⟨hφ, hi⟩ := hn
    rw [nT_eq] at hi
    cases n' with
    | ff g' c' =>
      have hg' := hn'.1
      rw [nGr_eq] at hg'
      exact absurd (Prod.mk.inj e).1 (by omega)
    | att g' c' => exact absurd (Prod.mk.inj e).1 (by omega)
    | hf φ' i' =>
      obtain ⟨hφ', hi'⟩ := hn'
      rw [nT_eq] at hi'
      obtain ⟨e1, e2, e3⟩ := stack_inj (rowHf φ hi) (rowHf φ' hi') (Prod.mk.inj e).2
      simp only [Head.rowOf, Head.colOf, perCol_hf, colsHead_eq] at e1 e2 e3
      have a : φ = φ' := by omega
      have b : i = i' := by omega
      rw [a, b]
    | hd φ' i' =>
      obtain ⟨hφ', hi'⟩ := hn'
      rw [nT_eq] at hi'
      rw [nFeat_hd] at hφ'
      obtain ⟨e1, e2, e3⟩ := stack_inj (rowHf φ hi) (rowHd φ' hi') (Prod.mk.inj e).2
      simp only [Head.rowOf, Head.colOf, perCol_hf, perCol_hd, colsHead_eq] at e1 e2 e3
      omega
    | hr φ' i' =>
      obtain ⟨hφ', hi'⟩ := hn'
      rw [nT_eq] at hi'
      obtain ⟨e1, e2, e3⟩ := stack_inj (rowHf φ hi) (rowHr φ' hi') (Prod.mk.inj e).2
      simp only [Head.rowOf, Head.colOf, perCol_hf, perCol_hr, colsHead_eq] at e1 e2 e3
      omega
  | hd φ i =>
    obtain ⟨hφ, hi⟩ := hn
    rw [nT_eq] at hi
    rw [nFeat_hd] at hφ
    cases n' with
    | ff g' c' =>
      have hg' := hn'.1
      rw [nGr_eq] at hg'
      exact absurd (Prod.mk.inj e).1 (by omega)
    | att g' c' => exact absurd (Prod.mk.inj e).1 (by omega)
    | hf φ' i' =>
      obtain ⟨hφ', hi'⟩ := hn'
      rw [nT_eq] at hi'
      obtain ⟨e1, e2, e3⟩ := stack_inj (rowHd φ hi) (rowHf φ' hi') (Prod.mk.inj e).2
      simp only [Head.rowOf, Head.colOf, perCol_hf, perCol_hd, colsHead_eq] at e1 e2 e3
      omega
    | hd φ' i' =>
      obtain ⟨hφ', hi'⟩ := hn'
      rw [nT_eq] at hi'
      obtain ⟨e1, e2, e3⟩ := stack_inj (rowHd φ hi) (rowHd φ' hi') (Prod.mk.inj e).2
      simp only [Head.rowOf, Head.colOf, perCol_hd, colsHead_eq] at e1 e2 e3
      have a : φ = φ' := by omega
      have b : i = i' := by omega
      rw [a, b]
    | hr φ' i' =>
      obtain ⟨hφ', hi'⟩ := hn'
      rw [nT_eq] at hi'
      obtain ⟨e1, e2, e3⟩ := stack_inj (rowHd φ hi) (rowHr φ' hi') (Prod.mk.inj e).2
      simp only [Head.rowOf, Head.colOf, perCol_hd, perCol_hr, colsHead_eq] at e1 e2 e3
      omega
  | hr φ i =>
    obtain ⟨hφ, hi⟩ := hn
    rw [nT_eq] at hi
    cases n' with
    | ff g' c' =>
      have hg' := hn'.1
      rw [nGr_eq] at hg'
      exact absurd (Prod.mk.inj e).1 (by omega)
    | att g' c' => exact absurd (Prod.mk.inj e).1 (by omega)
    | hf φ' i' =>
      obtain ⟨hφ', hi'⟩ := hn'
      rw [nT_eq] at hi'
      obtain ⟨e1, e2, e3⟩ := stack_inj (rowHr φ hi) (rowHf φ' hi') (Prod.mk.inj e).2
      simp only [Head.rowOf, Head.colOf, perCol_hf, perCol_hr, colsHead_eq] at e1 e2 e3
      omega
    | hd φ' i' =>
      obtain ⟨hφ', hi'⟩ := hn'
      rw [nT_eq] at hi'
      rw [nFeat_hd] at hφ'
      obtain ⟨e1, e2, e3⟩ := stack_inj (rowHr φ hi) (rowHd φ' hi') (Prod.mk.inj e).2
      simp only [Head.rowOf, Head.colOf, perCol_hd, perCol_hr, colsHead_eq] at e1 e2 e3
      omega
    | hr φ' i' =>
      obtain ⟨hφ', hi'⟩ := hn'
      rw [nT_eq] at hi'
      obtain ⟨e1, e2, e3⟩ := stack_inj (rowHr φ hi) (rowHr φ' hi') (Prod.mk.inj e).2
      simp only [Head.rowOf, Head.colOf, perCol_hr, colsHead_eq] at e1 e2 e3
      have a : φ = φ' := by omega
      have b : i = i' := by omega
      rw [a, b]

theorem lay_toMat_place : Spec.lay_toMat_place := by
  intro h hOK T n hn
  have e : ∃ m : Name, m.Valid h ∧ m.place = (n.place.1, n.place.2.1, n.place.2.2) := ⟨n, hn, rfl⟩
  unfold at' toMat
  rw [dif_pos e, lay_inj h hOK _ n e.choose_spec.1 hn e.choose_spec.2]

theorem lay_toMat_off : Spec.lay_toMat_off := by
  intro h T p hp
  unfold at' toMat
  rw [dif_neg hp]

theorem lay_ofMat_get : Spec.lay_ofMat_get := by
  intro h M n
  cases n <;> rfl

theorem lay_ofMat_toMat : Spec.lay_ofMat_toMat := by
  intro h hOK T n hn
  rw [lay_ofMat_get]
  unfold rd
  rw [if_pos hn, lay_toMat_place h hOK T n hn]

theorem lay_toMat_ofMat : Spec.lay_toMat_ofMat := by
  intro h hOK M
  refine ⟨fun n hn => ?_, fun p hp => lay_toMat_off h _ p hp⟩
  rw [lay_toMat_place h hOK _ n hn, lay_ofMat_get]
  unfold rd
  rw [if_pos hn]

theorem lay_ofMat_congr : Spec.lay_ofMat_congr := by
  intro h hOK M M' hM
  have e : rd h M = rd h M' := funext fun n => by
    unfold rd
    by_cases hn : n.Valid h
    · rw [if_pos hn, if_pos hn]
      exact hM _ (lay_inShape h hOK n hn)
    · rw [if_neg hn, if_neg hn]
  unfold ofMat
  rw [e]

theorem lay_own : Spec.lay_own := fun T => ⟨vFF_eq T, vAtt_eq T, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem lay_own_valid : Spec.lay_own_valid := fun h =>
  ⟨fun _ hg _ hc => ownFF_valid h hg hc,
    fun _ hg _ hc => ownAtt_valid h hg hc,
    fun _ hφ _ hi => ownX_valid h hφ hi⟩

/-- the trace of matrices at a valid name -/
theorem get_ofMat_valid (h : Hd) (M : ℕ → ℕ → ℕ → ℤ) {n : Name} (hn : n.Valid h) :
    get (ofMat h M) n = at' M n.place := by
  rw [lay_ofMat_get]
  unfold rd
  rw [if_pos hn]

theorem lay_read_ofMat : Spec.lay_read_ofMat := by
  intro h M
  refine ⟨fun g hg c hc => ?_, fun g hg c hc => ?_, fun φ hφ i hi => ?_, fun φ hφ i hi => ?_,
    fun φ hφ i hi => ?_, fun φ hφ i hi => ?_⟩
  · rw [vFF_eq, get_ofMat_valid h M (ownFF_valid h hg hc)]
  · rw [vAtt_eq, get_ofMat_valid h M (ownAtt_valid h hg hc)]
  · exact get_ofMat_valid h M (n := .hf φ i) ⟨hφ, hi⟩
  · exact get_ofMat_valid h M (n := .hd φ i) ⟨hφ, hi⟩
  · exact get_ofMat_valid h M (n := .hr φ i) ⟨hφ, hi⟩
  · exact get_ofMat_valid h M (ownX_valid h hφ hi)

theorem lay_read_toMat : Spec.lay_read_toMat := by
  intro h hOK T
  refine ⟨fun g hg c hc => ?_, fun g hg c hc => ?_, fun φ hφ i hi => ?_, fun φ hφ i hi => ?_,
    fun φ hφ i hi => ?_, fun φ hφ i hi => ?_⟩
  · rw [vFF_eq, lay_toMat_place h hOK T _ (ownFF_valid h hg hc)]
  · rw [vAtt_eq, lay_toMat_place h hOK T _ (ownAtt_valid h hg hc)]
  · exact (lay_toMat_place h hOK T (.hf φ i) ⟨hφ, hi⟩).symm
  · exact (lay_toMat_place h hOK T (.hd φ i) ⟨hφ, hi⟩).symm
  · exact (lay_toMat_place h hOK T (.hr φ i) ⟨hφ, hi⟩).symm
  · exact (lay_toMat_place h hOK T _ (ownX_valid h hφ hi)).symm

theorem lay_same_readings : Spec.lay_same_readings := by
  intro h hOK T
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := lay_read_ofMat h (toMat h T)
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := lay_read_toMat h hOK T
  exact ⟨fun g hg c hc => (a1 g hg c hc).trans (b1 g hg c hc).symm,
    fun g hg c hc => (a2 g hg c hc).trans (b2 g hg c hc).symm,
    fun φ hφ i hi => (a3 φ hφ i hi).trans (b3 φ hφ i hi).symm,
    fun φ hφ i hi => (a4 φ hφ i hi).trans (b4 φ hφ i hi).symm,
    fun φ hφ i hi => (a5 φ hφ i hi).trans (b5 φ hφ i hi).symm,
    fun φ hφ i hi => (a6 φ hφ i hi).trans (b6 φ hφ i hi).symm⟩

theorem lay_below : Spec.lay_below := by
  intro h hOK B T hB
  constructor
  · intro hN p _
    by_cases e : ∃ n : Name, n.Valid h ∧ n.place = p
    · obtain ⟨n, hn, rfl⟩ := e
      rw [lay_toMat_place h hOK T n hn]
      exact hN n hn
    · rw [lay_toMat_off h T p e, abs_zero]
      exact hB
  · intro hM n hn
    rw [← lay_toMat_place h hOK T n hn]
    exact hM _ (lay_inShape h hOK n hn)

theorem lay_reads : Spec.lay_reads := by
  intro h hOK s _ p hp
  rcases hp with ⟨g, c, rfl, hg, hc, rfl⟩ | ⟨g, c, rfl, hg, hc, rfl⟩ | ⟨rfl,
    ⟨n, hn, hn24, rfl⟩ | ⟨φ, i, hφ, hi, rfl⟩⟩
  · refine ⟨?_, lay_inShape h hOK _ (ownFF_valid h hg hc)⟩
    rcases ownFF_cases g c with e | ⟨_, _, e⟩ <;> rw [e]
    · exact le_refl _
    · show 2 * (g - 1) ≤ 2 * g
      omega
  · refine ⟨?_, lay_inShape h hOK _ (ownAtt_valid h hg hc)⟩
    rcases ownAtt_cases g c with e | ⟨c', e, _⟩ <;> rw [e]
    · exact le_refl _
    · show 2 * g ≤ 2 * g + 1
      omega
  · exact ⟨le_of_eq hn24, lay_inShape h hOK n hn⟩
  · exact ⟨(by decide : 2 * (nGr - 1) ≤ 24), lay_inShape h hOK _ (ownX_valid h hφ hi)⟩

theorem lay_keeps : Spec.lay_keeps := by
  intro h hOK s _ p hp k hk1 hk2
  rcases hp with ⟨g, c, rfl, hg, hc, rfl⟩ | ⟨g, c, rfl, hg, hc, rfl⟩ | ⟨rfl,
    ⟨n, hn, hn24, rfl⟩ | ⟨φ, i, hφ, hi, rfl⟩⟩
  · have hv := ownFF_valid h hg hc
    rw [nGr_eq] at hg
    rcases ownFF_cases g c with e | ⟨h0, _, e⟩
    · rw [e] at hk1
      have : 2 * g ≤ k := hk1
      omega
    · rw [e] at hk1 hv ⊢
      have h1 : 2 * (g - 1) ≤ k := hk1
      show (2 * (g - 1), (plFF { c with X := .x8 }).1) ∈ kept k
      rw [plFF_row_xout _ hv.2.1 rfl]
      exact mem_kept_xout (by omega) h1 (by omega) (plFF_row _ hv.2.1)
  · have hv := ownAtt_valid h hg hc
    rw [nGr_eq] at hg
    rcases ownAtt_cases g c with e | ⟨c', e, hm⟩
    · rw [e] at hk1
      have : 2 * g + 1 ≤ k := hk1
      omega
    · rw [e] at hk1 hv ⊢
      have h1 : 2 * g ≤ k := hk1
      have ek : k = 2 * g := by omega
      subst ek
      show (2 * g, (plFF c').1) ∈ kept (2 * g)
      rw [plFF_row_qa _ hv.2.1 hm]
      exact mem_kept_qa hg (plFF_row _ hv.2.1)
  · rw [hn24] at hk1
    omega
  · have hv := ownX_valid h hφ hi
    have h1 : 2 * 11 ≤ k := hk1
    show (2 * 11, (plFF ⟨.x8, φ / 5120, 0, φ % 5120, i⟩).1) ∈ kept k
    rw [plFF_row_xout _ hv.2.1 rfl]
    exact mem_kept_xout (by omega) h1 (by omega) (plFF_row _ hv.2.1)

theorem lay_keptIn : Spec.lay_keptIn := by
  intro k q hq
  unfold kept at hq
  split_ifs at hq with h1 h2
  · rcases Finset.mem_union.1 hq with hq | hq <;> obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq <;>
      (have hr' := Finset.mem_range.1 hr
       rw [hSlot_eq] at hr'
       refine ⟨le_refl _, by rw [nSeg_eq]; omega, ?_⟩
       show _ * hSlot + r < 2 ^ rowsLog k
       rw [rowsLog_even h2, hSlot_eq]
       omega)
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
    have hr' := Finset.mem_range.1 hr
    rw [hSlot_eq] at hr'
    refine ⟨Nat.sub_le _ _, ?_, ?_⟩
    · show k - 1 < nSeg
      rw [nSeg_eq]
      omega
    · show 7 * hSlot + r < 2 ^ rowsLog (k - 1)
      rw [rowsLog_even (by omega), hSlot_eq]
      omega
  · exact absurd hq (Finset.notMem_empty _)

theorem lay_keptStep : Spec.lay_keptStep := by
  intro k q hq
  unfold kept at hq
  split_ifs at hq with h1 h2
  · rcases Finset.mem_union.1 hq with hq | hq
      <;> obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hq <;> exact Or.inl rfl
  · refine Or.inr ?_
    rw [Nat.add_sub_cancel] at hq
    unfold kept
    rw [if_pos (by omega), if_pos (by omega)]
    exact Finset.mem_union_right _ hq
  · exact absurd hq (Finset.notMem_empty _)

theorem lay_valid_refK : Spec.lay_valid_refK := by
  intro u0
  refine ⟨fun c => ?_, fun j => ?_, fun _ => rfl, fun _ _ => rfl, rfl, fun c => ?_⟩
  · cases c with
    | c ρ jj b x => cases ρ <;> exact Iff.rfl
    | _ => exact Iff.rfl
  · cases j <;> exact Iff.rfl
  · fin_cases c <;> rfl

/-! ## No row is kept in vain -/

namespace Seg

theorem row_x8 (φ i : ℕ) :
    (FFSeg.addr DF ⟨.x8, φ / 5120, 0, φ % 5120, i⟩).2.1 = (φ % 64) * 1024 + i := by
  have e : FFSeg.feat DF .x8 (φ / 5120) 0 (φ % 5120) = φ := by
    show 0 + (φ / 5120 * 1 + 0) * 5120 + φ % 5120 = φ
    omega
  show (FFSeg.feat DF .x8 (φ / 5120) 0 (φ % 5120) % 2 ^ 6) * 2 ^ 10 + i = _
  rw [e]
  norm_num

theorem row_q (j i : ℕ) :
    (FFSeg.addr DF ⟨.q, 0, DA.lamOf 0, DA.ch * DA.head 0 0 + j, i⟩).2.1 = (j % 64) * 1024 + i := by
  have e1 : DA.lamOf 0 = 0 := by decide
  have e2 : DA.head 0 0 = 0 := by decide
  have e : FFSeg.feat DF .q 0 (DA.lamOf 0) (DA.ch * DA.head 0 0 + j) = j := by
    show 0 + (0 * 4 + DA.lamOf 0) * 5120 + (DA.ch * DA.head 0 0 + j) = j
    rw [e1, e2]
    omega
  show (FFSeg.feat DF .q 0 (DA.lamOf 0) (DA.ch * DA.head 0 0 + j) % 2 ^ 6) * 2 ^ 10 + i = _
  rw [e]
  norm_num

/-- For g < 12: every row of the slot xout of a feed-forward segment holds a cell that a segment
after the group's attention segment reads (in the proof: the next feed-forward segment, or the
head). -/
theorem xout_used (h : Hd) {g r : ℕ} (hg : g < 12) (hr : r < hSlot) :
    ∃ s, 2 * g + 1 < s ∧ s < nSeg ∧ ∃ p ∈ reads h s, (p.1, p.2.1) = (2 * g, 7 * hSlot + r) := by
  rw [hSlot_eq] at hr
  have hφ : r / 1024 < Head.nFeat .x := by rw [nFeat_x]; omega
  have hi : r % 1024 < Head.nT := by rw [nT_eq]; omega
  have hv := ownX_valid h hφ hi
  have row : (plFF ⟨.x8, r / 1024 / 5120, 0, r / 1024 % 5120, r % 1024⟩).1 = 7 * hSlot + r := by
    rw [plFF_row_xout _ hv.2.1 rfl, row_x8]
    omega
  by_cases h11 : g = 11
  · subst h11
    refine ⟨24, by omega, by decide, (ownX (r / 1024) (r % 1024)).place,
      Or.inr (Or.inr ⟨rfl, Or.inr ⟨_, _, hφ, hi, rfl⟩⟩), ?_⟩
    show (2 * 11, (plFF ⟨.x8, r / 1024 / 5120, 0, r / 1024 % 5120, r % 1024⟩).1) = _
    rw [row]
  · have e : ownFF (g + 1) ⟨.x0, r / 1024 / 5120, 0, r / 1024 % 5120, r % 1024⟩ =
        .ff g ⟨.x8, r / 1024 / 5120, 0, r / 1024 % 5120, r % 1024⟩ := by
      unfold ownFF
      rw [if_pos ⟨rfl, Nat.succ_pos g⟩]
      rfl
    refine ⟨2 * (g + 1), by omega,
      by rw [nSeg_eq]; omega,
      (ownFF (g + 1) ⟨.x0, r / 1024 / 5120, 0, r / 1024 % 5120, r % 1024⟩).place,
      Or.inl ⟨g + 1, ⟨.x0, r / 1024 / 5120, 0, r / 1024 % 5120, r % 1024⟩,
          rfl, by rw [nGr_eq]; omega, hv.2.1, rfl⟩,
      ?_⟩
    rw [e]
    show (2 * g, (plFF ⟨.x8, r / 1024 / 5120, 0, r / 1024 % 5120, r % 1024⟩).1) = _
    rw [row]

/-- For g < 12: every row of the slot qa of a feed-forward segment holds a cell that the attention
segment of the group reads. -/
theorem qa_used (h : Hd) {g r : ℕ} (hg : g < 12) (hr : r < hSlot) :
    ∃ p ∈ reads h (2 * g + 1), (p.1, p.2.1) = (2 * g, 5 * hSlot + r) := by
  rw [hSlot_eq] at hr
  have eT : DA.T = 1024 := by decide
  have ech : DA.ch = 128 := by decide
  have hc : (AttSeg.Raw.qry 0 0 0 (r % 1024) (r / 1024)).Valid DA :=
    ⟨by decide, by decide, by decide, by rw [eT]; omega, by rw [ech]; omega⟩
  have hg' : g < nGr := by rw [nGr_eq]; exact hg
  have hv := ownAtt_valid h hg' hc
  refine ⟨(ownAtt g (.qry 0 0 0 (r % 1024) (r / 1024))).place,
    Or.inr (Or.inl ⟨g, _, rfl, hg', hc, rfl⟩),
    ?_⟩
  show (2 * g, (plFF ⟨.q, 0, DA.lamOf 0, DA.ch * DA.head 0 0 + r / 1024, r % 1024⟩).1) = _
  rw [plFF_row_qa _ hv.2.1 rfl, row_q]
  have : r / 1024 % 64 * 1024 + r % 1024 = r := by omega
  rw [this]

end Seg

theorem lay_kept_used : Spec.lay_kept_used := by
  intro h k q hq
  unfold kept at hq
  split_ifs at hq with h1 h2
  · have ek : k = 2 * (k / 2) := by omega
    rcases Finset.mem_union.1 hq with hq | hq <;> obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
    · obtain ⟨p, hp, e⟩ := qa_used h (g := k / 2) (by omega) (Finset.mem_range.1 hr)
      refine ⟨2 * (k / 2) + 1, by omega, by rw [nSeg_eq]; omega, p, hp, ?_⟩
      rw [e, ← ek]
    · obtain ⟨s, hs1, hs2, p, hp, e⟩ := xout_used h (g := k / 2) (by omega) (Finset.mem_range.1 hr)
      refine ⟨s, by omega, hs2, p, hp, ?_⟩
      rw [e, ← ek]
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
    have ek : k - 1 = 2 * (k / 2) := by omega
    obtain ⟨s, hs1, hs2, p, hp, e⟩ := xout_used h (g := k / 2) (by omega) (Finset.mem_range.1 hr)
    refine ⟨s, by omega, hs2, p, hp, ?_⟩
    rw [e, ← ek]
  · exact absurd hq (Finset.notMem_empty _)

end Cm
