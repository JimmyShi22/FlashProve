-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PlacesNum.lean: kind K5: every listed name's place (placeAtt,
Johnson/Road/Rows/AttPortLate.lean) lies below its table's number of entries: arithmetic on the
planner's own text.

Main names:
  `Fills cf S`, `fills_of_shape`, `fills_of_hid`: how far the matrices ah, ao and qa are filled
    (roundUp of the features), the heads' number as a product, wcO and wcQ not 0: read off shape
    (OnBytes/Model/AttentionShape.lean). `le_roundUp`, `idx_lt`, `idx_le`, `pair_lt`, `div_add_lt`,
    `ten_top`, `as_room`.
  `placeRow_lt` (names mx, den, ib), `placeTen_lt`, `placeLong_lt` (qry, out, key, val; qh, qh'),
    `placeCol_lt` (c M, c D).
  `lenOf S T`: how many entries table T has. `place_lt_len`: placeAtt S T r < lenOf S T at every
    listed name, at a shape that shapeHid returns with NAs and wcH not 0.
Used of OnBytes and Johnson/Road: plain records and the planner's pure functions; Shaped,
shaped_of_hid, Norm, Sizes, hid_calls, tests_of_hid, lmS_le_nM, blk_div; of_mem_row, of_mem_long,
of_mem_col (Cb/Pv/Att/End/Names.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttLayNames
import Johnson.Road.Lane5AttLaid

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Raw)

/-- **How far the shape's matrices are filled**: read off the planner's text. -/
structure Fills (cf : Cfg) (S : Shape) : Prop where
  heads : cf.H = 2 ^ cf.lgk * (cf.H / 2 ^ cf.lgk)
  fillH : S.fillH = roundUp (8 * 2 ^ cf.ll * cf.H + 2 ^ cf.ll * cf.lt * cf.H) cf.wcH
  fillO : S.fillO = roundUp (2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh)) cf.wcO
  fillQ : S.fillQ = roundUp (2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) +
    2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh)) cf.wcQ
  wcO : 0 < cf.wcO
  wcQ : 0 < cf.wcQ

theorem fills_of_shape {cf : Cfg} {S : Shape} (h : shape cf = Except.ok S) : Fills cf S := by
  unfold Attention.shape at h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨e2, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨Tt, -, h⟩ := L5.bind_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨_, -, h⟩ := L5.bind_ok h
  obtain ⟨_, -, h⟩ := L5.bind_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨e13, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨calls, -, h⟩ := L5.bind_ok h
  have e := Except.ok.inj h
  subst e
  rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at e2
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at e13
  have p : 0 < 2 ^ cf.la := Nat.two_pow_pos _
  refine ⟨(Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero e2.2)).symm, rfl, rfl, rfl, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos cf.wcO with h0 | h0
    · have := e13.1.1.1
      rw [h0, Nat.zero_mul] at this
      omega
    · exact h0
  · rcases Nat.eq_zero_or_pos cf.wcQ with h0 | h0
    · have := e13.1.1.2
      rw [h0, Nat.zero_mul] at this
      omega
    · exact h0

theorem fills_of_hid {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Model.Forest.Shape}
    (h : shapeHid lid cf = Except.ok (S, fs)) : Fills cf S := by
  obtain ⟨A, io, kbA, hA, eS, -⟩ := L5.hid_calls h
  have F := fills_of_shape hA
  rw [eS]
  exact ⟨F.heads, F.fillH, F.fillO, F.fillQ, F.wcO, F.wcQ⟩

/-- Rounding up does not lessen. -/
theorem le_roundUp (x : ℕ) {w : ℕ} (hw : 0 < w) : x ≤ roundUp x w := by
  unfold roundUp
  have h1 := Nat.div_add_mod (x + w - 1) w
  have h2 := Nat.mod_lt (x + w - 1) hw
  rw [Nat.mul_comm] at h1
  omega

/-- A number in a blocks of B. -/
theorem idx_lt {a A b B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  calc a * B + b < a * B + B := by omega
    _ = (a + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right _ ha

/-- The same with room for a whole block. -/
theorem idx_le {a A b B : ℕ} (ha : a < A) (hb : b ≤ B) : a * B + b ≤ A * B := by
  calc a * B + b ≤ a * B + B := by omega
    _ = (a + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right _ ha

variable {cf : Cfg} {S : Shape}

/-- The layer and the query head of a pair; the head of a pair and a head of keys and values. -/
theorem pair_lt (Sh : L5.Shaped cf S) (F : Fills cf S) {b g : ℕ} (hb : b < (L5.dimOf S).nb)
    (hg : g < (L5.dimOf S).nG) :
    b / S.HA < S.Lam ∧ b % S.HA < S.HA ∧ g * S.HA + b % S.HA < S.cf.H := by
  have hb' : b < S.Lam * S.HA := hb
  have hg' : g < 2 ^ S.cf.lgk := hg
  have hp : 0 < S.HA := by
    rcases Nat.eq_zero_or_pos S.HA with h0 | h0
    · rw [h0, Nat.mul_zero] at hb'; omega
    · exact h0
  have h1 : b / S.HA < S.Lam := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb')
  have h2 : b % S.HA < S.HA := Nat.mod_lt _ hp
  refine ⟨h1, h2, ?_⟩
  have e : S.cf.H = 2 ^ S.cf.lgk * S.HA := by rw [Sh.HA, Sh.cfg]; exact F.heads
  rw [e]
  exact idx_lt hg' h2

/-- **The places of the tables on ah lie below the matrix's filled features.** -/
theorem placeRow_lt (Sh : L5.Shaped cf S) (F : Fills cf S) (hw : 0 < cf.wcH)
    (hlT : (L5.dimOf S).lT = S.cf.lt) {b g : ℕ} (hb : b < (L5.dimOf S).nb) (hg : g < (L5.dimOf S).nG) :
    (∀ k < 4, placeRow S (.mx k b g 0) < S.fillH) ∧ (∀ k < 4, placeRow S (.den k b g 0) < S.fillH) ∧
      ∀ k < (L5.dimOf S).lT, placeRow S (.ib k b g 0) < S.fillH := by
  obtain ⟨h1, h2, h3⟩ := pair_lt Sh F hb hg
  have hf : 8 * S.Lam * S.cf.H + S.Lam * S.cf.lt * S.cf.H ≤ S.fillH := by
    rw [F.fillH, Sh.Lam, Sh.cfg]
    exact le_roundUp _ hw
  have eZ : S.oZr = 4 * S.Lam * S.cf.H := by rw [Sh.oZr, Sh.Lam, Sh.cfg]
  have eI : S.oIb = 8 * S.Lam * S.cf.H := by rw [Sh.oIb, Sh.Lam, Sh.cfg]
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · show S.oMr + (k * S.Lam + b / S.HA) * S.cf.H + (g * S.HA + b % S.HA) < _
    have a := idx_lt (idx_lt hk h1) h3
    rw [Sh.oMr]
    have : 4 * S.Lam * S.cf.H ≤ 8 * S.Lam * S.cf.H := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
    omega
  · show S.oZr + (k * S.Lam + b / S.HA) * S.cf.H + (g * S.HA + b % S.HA) < _
    have a := idx_lt (idx_lt hk h1) h3
    rw [eZ]
    have : 4 * S.Lam * S.cf.H + 4 * S.Lam * S.cf.H = 8 * S.Lam * S.cf.H := by ring
    omega
  · show S.oIb + (0 * S.Lam + b / S.HA) * (S.cf.lt * S.cf.H) + (k * S.cf.H + g * S.HA + b % S.HA) < _
    rw [hlT] at hk
    have a1 : k * S.cf.H + (g * S.HA + b % S.HA) < S.cf.lt * S.cf.H := idx_lt hk h3
    have a := idx_lt h1 a1
    rw [eI, Nat.zero_mul, Nat.zero_add]
    have : S.Lam * (S.cf.lt * S.cf.H) = S.Lam * S.cf.lt * S.cf.H := by ring
    omega

/-- A quotient plus a block's number lies below the quotient of a bound with room for the block. -/
theorem div_add_lt {a c p F : ℕ} (hp : 0 < p) (h : a + (c + 1) * p ≤ F) : a / p + c < F / p := by
  have h1 : (a / p + c + 1) * p ≤ F := by
    have := Nat.div_mul_le_self a p
    calc (a / p + c + 1) * p = a / p * p + (c + 1) * p := by ring
      _ ≤ a + (c + 1) * p := by omega
      _ ≤ F := h
  exact (Nat.le_div_iff_mul_le hp).2 h1

/-- A head's features end inside the tensor. -/
theorem ten_top (X : TenAt) {l lam hd dh nH : ℕ} (hl : l < X.nl) (hlam : lam < X.cnt) (hJ : X.J = nH * dh)
    (hh : hd < nH) : tenCell X l lam (hd * dh) + dh ≤ X.off + X.nl * X.cnt * X.J := by
  unfold tenCell
  have a : hd * dh + dh ≤ X.J := by rw [hJ]; exact idx_le hh (Nat.le_refl _)
  have b := idx_le (idx_lt hl hlam) a
  omega

/-- The place of a block of a head's features, in a matrix filled up to F features. -/
theorem placeTen_lt (Z : Sizes S) (hdh : S.dh = 2 ^ S.cf.ldh) (X : TenAt) {l lam hd nH ch F : ℕ} (hl : l < X.nl)
    (hlam : lam < X.cnt) (hJ : X.J = nH * S.dh) (hh : hd < nH) (hch : ch < 2 ^ (S.cf.ldh - S.ls))
    (hF : X.off + X.nl * X.cnt * X.J ≤ F) :
    placeTen S X l lam hd (0 + ch * 2 ^ S.ls) < F * S.T / 2 ^ S.cf.la := by
  have hp : 0 < 2 ^ S.ls := Nat.two_pow_pos _
  have hT : 0 < S.T := by rw [Z.T]; exact Nat.two_pow_pos _
  have e1 : F * S.T / 2 ^ S.cf.la = F / 2 ^ S.ls := by
    rw [Z.la, pow_add, ← Z.T]
    exact Nat.mul_div_mul_right _ _ hT
  have e2 : (ch + 1) * 2 ^ S.ls ≤ S.dh := by
    rw [hdh, show S.cf.ldh = (S.cf.ldh - S.ls) + S.ls by have := Z.ls; omega, pow_add]
    exact Nat.mul_le_mul_right _ hch
  unfold placeTen
  rw [e1, blk_div]
  exact div_add_lt hp (by have := ten_top X hl hlam hJ hh; omega)

/-- **The places of the tables on blocks of features lie in their tables**: qa's four tensors, ao's two. -/
theorem placeLong_lt (Sh : L5.Shaped cf S) (F : Fills cf S) (Z : Sizes S) {b lam g ch : ℕ}
    (hb : b < (L5.dimOf S).nb) (hlam : lam < (L5.dimOf S).nl) (hg : g < (L5.dimOf S).nG)
    (hch : ch < 2 ^ ((L5.dimOf S).ln - S.ls)) :
    (∀ k < 2, placeLong S ((Raw.qry k b g 0 0).addN (ch * 2 ^ S.ls)) < S.fillQ * S.T / 2 ^ S.cf.la) ∧
    (∀ k < 2, placeLong S ((Raw.out k b g 0 0).addN (ch * 2 ^ S.ls)) < S.fillQ * S.T / 2 ^ S.cf.la) ∧
    (∀ k < 2, placeLong S ((Raw.key k lam g 0 0).addN (ch * 2 ^ S.ls)) < S.fillQ * S.T / 2 ^ S.cf.la) ∧
    (∀ k < 2, placeLong S ((Raw.val k lam g 0 0).addN (ch * 2 ^ S.ls)) < S.fillQ * S.T / 2 ^ S.cf.la) ∧
    placeLong S ((Raw.qh b g 0 0).addN (ch * 2 ^ S.ls)) < S.fillO * S.T / 2 ^ S.cf.la ∧
    placeLong S ((Raw.qh' b g 0 0).addN (ch * 2 ^ S.ls)) < S.fillO * S.T / 2 ^ S.cf.la := by
  obtain ⟨h1, h2, h3⟩ := pair_lt Sh F hb hg
  have hlam' : lam < S.Lam := hlam
  have hg' : g < 2 ^ S.cf.lgk := hg
  have hch' : ch < 2 ^ (S.cf.ldh - S.ls) := hch
  have hdh : S.dh = 2 ^ S.cf.ldh := by rw [Sh.dh, Sh.cfg]
  have hL : S.Lam = 2 ^ cf.ll := Sh.Lam
  have hc := Sh.cfg
  have fQ := le_roundUp (2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) +
    2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh)) F.wcQ
  rw [← F.fillQ] at fQ
  have fO := le_roundUp (2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh)) F.wcO
  rw [← F.fillO] at fO
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
  · exact placeTen_lt Z hdh S.atQ (nH := S.cf.H) (by rw [Sh.atQ]; exact hk) (by rw [Sh.atQ, ← hL]; exact h1)
      (by rw [Sh.atQ, hdh, hc]) h3 hch' (by rw [Sh.atQ]; show 0 + 2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) ≤ _; omega)
  · exact placeTen_lt Z hdh S.atO (nH := S.cf.H) (by rw [Sh.atO]; exact hk) (by rw [Sh.atO, ← hL]; exact h1)
      (by rw [Sh.atO, hdh, hc]) h3 hch' (by rw [Sh.atO]; exact fQ)
  · exact placeTen_lt Z hdh S.atK (nH := 2 ^ S.cf.lgk) (by rw [Sh.atK]; exact hk)
      (by rw [Sh.atK, ← hL]; exact hlam') (by rw [Sh.atK, hdh, hc]) hg' hch'
      (by rw [Sh.atK]
          show 2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) ≤ _
          omega)
  · exact placeTen_lt Z hdh S.atV (nH := 2 ^ S.cf.lgk) (by rw [Sh.atV]; exact hk)
      (by rw [Sh.atV, ← hL]; exact hlam') (by rw [Sh.atV, hdh, hc]) hg' hch'
      (by rw [Sh.atV]
          show 2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) +
            2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) ≤ _
          omega)
  · exact placeTen_lt Z hdh (Attention.atRh S) (nH := S.cf.H) (l := 0) (by show 0 < 1; norm_num) h1
      (by show S.dq = _; rw [Sh.dq, hdh, hc]) h3 hch'
      (by show S.oRh + 1 * S.Lam * S.dq ≤ _
          rw [Sh.oRh, Sh.dq, hL, Nat.one_mul]
          have : 2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) = 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) := by ring
          omega)
  · exact placeTen_lt Z hdh (Attention.atRhp S) (nH := S.cf.H) (l := 0) (by show 0 < 1; norm_num) h1
      (by show S.dq = _; rw [Sh.dq, hdh, hc]) h3 hch'
      (by show S.oRhp + 1 * S.Lam * S.dq ≤ _
          rw [Sh.oRhp, Sh.dq, hL, Nat.one_mul]
          have : 2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) = 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) := by ring
          omega)

/-- The parts of the matrix as hold all the regions' cells. -/
theorem as_room (Sh : L5.Shaped cf S) (hN : 0 < S.cf.NAs) :
    5 * S.Lam * S.HA * (2 ^ S.nM + 2 ^ S.nD) ≤ S.cf.NAs * (S.kAs / S.cf.NAs) * 2 ^ S.cf.lmS := by
  have hc := Sh.cfg
  have hu : 0 < S.cf.NAs * 2 ^ S.cf.lmS := Nat.mul_pos hN (Nat.two_pow_pos _)
  have e : S.kAs = (5 * S.Lam * S.HA * (2 ^ S.nM + 2 ^ S.nD) + S.cf.NAs * 2 ^ S.cf.lmS - 1) /
      (S.cf.NAs * 2 ^ S.cf.lmS) * S.cf.NAs := by
    rw [Sh.kAs, Sh.Lam, Sh.HA, Sh.nM, Sh.nD, hc]
  rw [e, Nat.mul_div_cancel _ hN]
  have h1 := le_roundUp (5 * S.Lam * S.HA * (2 ^ S.nM + 2 ^ S.nD)) hu
  unfold roundUp at h1
  calc _ ≤ _ := h1
    _ = _ := by ring

/-- **The places of the tables on as lie in their tables.** -/
theorem placeCol_lt (Sh : L5.Shaped cf S) (N : L5.Norm S) (Z : Sizes S) (hN : 0 < S.cf.NAs)
    {x b hi : ℕ} (hx : x < 5) (hb : b < (L5.dimOf S).nb) :
    (hi < 2 ^ ((L5.dimOf S).lM - S.cf.lmS) →
      placeCol S ((Raw.c .M x b 0).addX (hi * 2 ^ S.cf.lmS)) < S.cf.NAs * (S.kAs / S.cf.NAs)) ∧
    (hi < 2 ^ ((L5.dimOf S).lD - S.cf.lmS) →
      placeCol S ((Raw.c .D x b 0).addX (hi * 2 ^ S.cf.lmS)) < S.cf.NAs * (S.kAs / S.cf.NAs)) := by
  have hb' : b < S.Lam * S.HA := hb
  have hp : 0 < S.HA := by
    rcases Nat.eq_zero_or_pos S.HA with h0 | h0
    · rw [h0, Nat.mul_zero] at hb'; omega
    · exact h0
  have h1 : b / S.HA < S.Lam := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb')
  have h2 : b % S.HA < S.HA := Nat.mod_lt _ hp
  have hi5 : (x * S.Lam + b / S.HA) * S.HA + b % S.HA < 5 * S.Lam * S.HA := idx_lt (idx_lt hx h1) h2
  have room := as_room Sh hN
  have hq : 0 < 2 ^ S.cf.lmS := Nat.two_pow_pos _
  have hM : S.cf.lmS ≤ S.nM := lmS_le_nM S N Z
  have hD : S.cf.lmS ≤ S.nD := Z.lmS
  have blk : ∀ n, S.cf.lmS ≤ n → hi < 2 ^ (n - S.cf.lmS) → (hi + 1) * 2 ^ S.cf.lmS ≤ 2 ^ n := by
    intro n hn hh
    calc (hi + 1) * 2 ^ S.cf.lmS ≤ 2 ^ (n - S.cf.lmS) * 2 ^ S.cf.lmS := Nat.mul_le_mul_right _ hh
      _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
  have fin : ∀ a, a + (hi + 1) * 2 ^ S.cf.lmS ≤ 5 * S.Lam * S.HA * (2 ^ S.nM + 2 ^ S.nD) →
      a / 2 ^ S.cf.lmS + hi < S.cf.NAs * (S.kAs / S.cf.NAs) := by
    intro a ha
    have := div_add_lt hq (Nat.le_trans ha room)
    rwa [Nat.mul_div_cancel _ hq] at this
  have dist : 5 * S.Lam * S.HA * (2 ^ S.nM + 2 ^ S.nD) =
      5 * S.Lam * S.HA * 2 ^ S.nM + 5 * S.Lam * S.HA * 2 ^ S.nD := by ring
  constructor
  · intro hh
    have eM : (L5.dimOf S).lM = S.nM := N.nM.symm
    rw [eM] at hh
    show planeFirst S x (b / S.HA) (b % S.HA) false >>> S.cf.lmS + (0 + hi * 2 ^ S.cf.lmS) / 2 ^ S.cf.lmS < _
    rw [blk_div, Nat.shiftRight_eq_div_pow]
    unfold planeFirst
    simp only [Bool.false_eq_true, if_false, Nat.zero_add, Nat.shiftLeft_eq]
    refine fin _ ?_
    have a := idx_le hi5 (blk _ hM hh)
    rw [dist]
    omega
  · intro hh
    have eD : (L5.dimOf S).lD = S.nD := N.nD.symm
    rw [eD] at hh
    show planeFirst S x (b / S.HA) (b % S.HA) true >>> S.cf.lmS + (0 + hi * 2 ^ S.cf.lmS) / 2 ^ S.cf.lmS < _
    rw [blk_div, Nat.shiftRight_eq_div_pow]
    unfold planeFirst
    simp only [if_true, Nat.shiftLeft_eq]
    refine fin _ ?_
    have a := idx_le hi5 (blk _ hD hh)
    rw [dist]
    omega

open Cb.Pv.Att.End (AttTab namesOf of_mem_row of_mem_long of_mem_col)

/-- How many entries each of the 21 tables has. -/
def lenOf (S : Shape) : AttTab → ℕ
  | .tA => S.cf.NAs * (S.kAs / S.cf.NAs)
  | .tVM => S.cf.NAs * (S.kAs / S.cf.NAs)
  | .tVD => S.cf.NAs * (S.kAs / S.cf.NAs)
  | .tMm => S.fillH
  | .tMd => S.fillH
  | .hW => S.fillH
  | .hX => S.fillH
  | .hE => S.fillH
  | .hT => S.fillH
  | .hPi => S.fillH
  | .hR2 => S.fillH
  | .tO => S.fillO * S.T / 2 ^ S.cf.la
  | _ => S.fillQ * S.T / 2 ^ S.cf.la

/-- **Every listed name's place lies below its table's number of entries**, at a shape that shapeHid returns with NAs and wcH not 0. -/
theorem place_lt_len {lid : ℕ} {fs : Model.Forest.Shape} (hid : shapeHid lid cf = Except.ok (S, fs))
    (hN : 0 < S.cf.NAs) (hw : 0 < cf.wcH) (T : AttTab) (r : Raw)
    (hr : r ∈ namesOf (L5.dimOf S) S.ls S.cf.lmS T) : placeAtt S T r < lenOf S T := by
  have Sh := L5.shaped_of_hid hid
  have F := fills_of_hid hid
  have N := norm_of_hid hid
  have Z := sizes_of_hid hid
  have hlT : (L5.dimOf S).lT = S.cf.lt := N.lt.symm
  have mx : ∀ r ∈ Cb.Pv.Att.End.rowNames (L5.dimOf S) 4 (fun k b g => Raw.mx k b g 0), placeRow S r < S.fillH := by
    intro r hr
    obtain ⟨k, b, g, hk, hb, hg, rfl⟩ := of_mem_row hr
    exact (placeRow_lt Sh F hw hlT hb hg).1 k hk
  have den : ∀ r ∈ Cb.Pv.Att.End.rowNames (L5.dimOf S) 4 (fun k b g => Raw.den k b g 0), placeRow S r < S.fillH := by
    intro r hr
    obtain ⟨k, b, g, hk, hb, hg, rfl⟩ := of_mem_row hr
    exact (placeRow_lt Sh F hw hlT hb hg).2.1 k hk
  have ib : ∀ r ∈ Cb.Pv.Att.End.rowNames (L5.dimOf S) (L5.dimOf S).lT (fun k b g => Raw.ib k b g 0),
      placeRow S r < S.fillH := by
    intro r hr
    obtain ⟨k, b, g, hk, hb, hg, rfl⟩ := of_mem_row hr
    exact (placeRow_lt Sh F hw hlT hb hg).2.2 k hk
  have qry : ∀ r ∈ Cb.Pv.Att.End.longNames (L5.dimOf S) S.ls 2 (L5.dimOf S).nb (fun k b g => Raw.qry k b g 0 0),
      placeLong S r < S.fillQ * S.T / 2 ^ S.cf.la := by
    intro r hr
    obtain ⟨k, b, g, ch, hk, hb, hg, hc, rfl⟩ := of_mem_long hr
    have hl : b / S.HA < (L5.dimOf S).nl := (pair_lt Sh F hb hg).1
    exact (placeLong_lt Sh F Z hb hl hg hc).1 k hk
  have out : ∀ r ∈ Cb.Pv.Att.End.longNames (L5.dimOf S) S.ls 2 (L5.dimOf S).nb (fun k b g => Raw.out k b g 0 0),
      placeLong S r < S.fillQ * S.T / 2 ^ S.cf.la := by
    intro r hr
    obtain ⟨k, b, g, ch, hk, hb, hg, hc, rfl⟩ := of_mem_long hr
    have hl : b / S.HA < (L5.dimOf S).nl := (pair_lt Sh F hb hg).1
    exact (placeLong_lt Sh F Z hb hl hg hc).2.1 k hk
  have hHA : 0 < S.HA := by rw [Sh.HA]; exact (L5.tests_of_hid hid).2
  have key : ∀ r ∈ Cb.Pv.Att.End.longNames (L5.dimOf S) S.ls 2 (L5.dimOf S).nl (fun k l g => Raw.key k l g 0 0),
      placeLong S r < S.fillQ * S.T / 2 ^ S.cf.la := by
    intro r hr
    obtain ⟨k, l, g, ch, hk, hl, hg, hc, rfl⟩ := of_mem_long hr
    have hb : 0 < (L5.dimOf S).nb := Nat.mul_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hl) hHA
    exact (placeLong_lt Sh F Z hb hl hg hc).2.2.1 k hk
  have val : ∀ r ∈ Cb.Pv.Att.End.longNames (L5.dimOf S) S.ls 2 (L5.dimOf S).nl (fun k l g => Raw.val k l g 0 0),
      placeLong S r < S.fillQ * S.T / 2 ^ S.cf.la := by
    intro r hr
    obtain ⟨k, l, g, ch, hk, hl, hg, hc, rfl⟩ := of_mem_long hr
    have hb : 0 < (L5.dimOf S).nb := Nat.mul_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hl) hHA
    exact (placeLong_lt Sh F Z hb hl hg hc).2.2.2.1 k hk
  have cM : ∀ r ∈ Cb.Pv.Att.End.colNames (L5.dimOf S) S.cf.lmS .M, placeCol S r < S.cf.NAs * (S.kAs / S.cf.NAs) := by
    intro r hr
    obtain ⟨x, b, hi, hx, hb, hh, rfl⟩ := of_mem_col hr
    exact (placeCol_lt Sh N Z hN hx hb).1 hh
  have cD : ∀ r ∈ Cb.Pv.Att.End.colNames (L5.dimOf S) S.cf.lmS .D, placeCol S r < S.cf.NAs * (S.kAs / S.cf.NAs) := by
    intro r hr
    obtain ⟨x, b, hi, hx, hb, hh, rfl⟩ := of_mem_col hr
    exact (placeCol_lt Sh N Z hN hx hb).2 hh
  cases T with
  | tA => rcases List.mem_append.mp hr with h | h
          · exact cM r h
          · exact cD r h
  | tVM => exact cM r hr
  | tVD => exact cD r hr
  | tMm => exact mx r hr
  | tMd => exact mx r hr
  | hT => exact mx r hr
  | hW => exact den r hr
  | hE => exact den r hr
  | hX => exact ib r hr
  | hPi => exact ib r hr
  | hR2 => exact ib r hr
  | tO =>
    rcases List.mem_append.mp hr with h | h
    · obtain ⟨k, b, g, ch, hk, hb, hg, hc, rfl⟩ := of_mem_long h
      have hl : b / S.HA < (L5.dimOf S).nl := (pair_lt Sh F hb hg).1
      exact (placeLong_lt Sh F Z hb hl hg hc).2.2.2.2.1
    · obtain ⟨k, b, g, ch, hk, hb, hg, hc, rfl⟩ := of_mem_long h
      have hl : b / S.HA < (L5.dimOf S).nl := (pair_lt Sh F hb hg).1
      exact (placeLong_lt Sh F Z hb hl hg hc).2.2.2.2.2
  | qO => exact out r hr
  | tQm => exact qry r hr
  | tQd => exact qry r hr
  | qF => exact qry r hr
  | tKm => exact key r hr
  | tKd => exact key r hr
  | qKx => exact key r hr
  | qVM => exact val r hr
  | qVD => exact val r hr

end K5Law
