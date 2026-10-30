-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5AttShape.lean

What the verifier's functions "shape" and "shapeHid" (OnBytes/Model/AttentionShape.lean) return: the
fields of the shape that dimOf, sclOf, tbOf and addrA (Johnson/Road/Lane5AttDef.lean) read, as
functions of the configuration. For every configuration.

A shape is a record whose fields have defaults. A statement on a free record says nothing of the
verifier. Here the record comes from the verifier's own call.

* "Shaped cf S": the fields of S, as functions of cf.
* "shaped_of_shape", "shaped_of_hid": shape cf = .ok S, or shapeHid lid cf = .ok (S, fs), gives it.
* "CfRef cf": ten numbers of the configuration are the reference numbers.
* "sized_of_shaped": Shaped cf S, CfRef cf and S.u0 = 2307 give AttSized S
  (Johnson/Road/Lane5AttAddr.lean).
* "wide_of_shaped": Shaped cf S, CfRef cf and 0 < cf.NAs (at least one part) give: the parts of "as"
  have together at least 7,200 columns.

Not here: that the table of exponentials at S = 12, rx = 8 has 2,307 rows
(Johnson/Road/Lane5AttExp.lean); tests that shape has made (two of them:
Johnson/Road/Lane5AttNum.lean; those on the shifts: Johnson/Road/Lane5AttCalls.lean). Only what
shape returns is read here.

Files named above that a package may lack. Johnson/Road/Lane5AttNum.lean,
Johnson/Road/Lane5AttCalls.lean and Johnson/Road/Lane5AttExp.lean are in the library's full tree and
are not imported by this file; a package that is cut to what its front theorems need may not hold
them. Where they lack, what this comment says of them cannot be checked there.

-/
import Johnson.Road.Lane5AttAddr

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

/-- A step of a computation that ends well has ended well. -/
theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = Except.ok b) : ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e =>
    have h' : (Except.error e : Except ε β) = Except.ok b := h
    cases h'
  | ok a => exact ⟨a, rfl, h⟩

theorem orRefuse_ok {α : Type} {x : Option α} {n : String} {a : α}
    (h : Attention.orRefuse x n = Except.ok a) : x = some a := by
  cases x with
  | none =>
    have h' : (Except.error n : Except String α) = Except.ok a := h
    cases h'
  | some b => exact congrArg some (Except.ok.inj (show Except.ok b = Except.ok a from h))

/-- **What the verifier's function shape returns**, as far as these files read it. -/
structure Shaped (cf : Attention.Cfg) (S : Attention.Shape) : Prop where
  cfg : S.cf = cf
  T : S.T = 2 ^ cf.lt
  lnT : S.lnT = cf.lt - cf.lB
  HA : S.HA = cf.H / 2 ^ cf.lgk
  Lam : S.Lam = 2 ^ cf.ll
  dh : S.dh = 2 ^ cf.ldh
  dq : S.dq = cf.H * 2 ^ cf.ldh
  nM : S.nM = Attention.nMOf cf
  nD : S.nD = Attention.nDOf cf
  oMr : S.oMr = 0
  oZr : S.oZr = 4 * 2 ^ cf.ll * cf.H
  oIb : S.oIb = 8 * 2 ^ cf.ll * cf.H
  oRh : S.oRh = 0
  oRhp : S.oRhp = 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh)
  atQ : S.atQ = ⟨0, 2, 2 ^ cf.ll, cf.H * 2 ^ cf.ldh⟩
  atK : S.atK = ⟨2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh), 2, 2 ^ cf.ll, 2 ^ cf.lgk * 2 ^ cf.ldh⟩
  atV : S.atV = ⟨2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh), 2,
    2 ^ cf.ll, 2 ^ cf.lgk * 2 ^ cf.ldh⟩
  atO : S.atO = ⟨2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) +
    2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh), 2, 2 ^ cf.ll, cf.H * 2 ^ cf.ldh⟩
  kAs : S.kAs = (5 * 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) *
      (2 ^ Attention.nMOf cf + 2 ^ Attention.nDOf cf) + cf.NAs * 2 ^ cf.lmS - 1) /
    (cf.NAs * 2 ^ cf.lmS) * cf.NAs
  u0 : S.u0 = S.Tt.size
  exp : Attention.expTable cf.S cf.rx = some S.Tt

theorem shaped_of_shape {cf : Attention.Cfg} {S : Attention.Shape}
    (h : Attention.shape cf = Except.ok S) : Shaped cf S := by
  unfold Attention.shape at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨Tt, hT, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨calls, _, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, orRefuse_ok hT⟩

theorem shaped_of_hid {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape}
    {fs : Model.Forest.Shape} (h : Attention.shapeHid lid cf = Except.ok (S, fs)) :
    Shaped cf S := by
  unfold Attention.shapeHid at h
  obtain ⟨A, hA, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have e := (Prod.mk.inj (Except.ok.inj h)).1
  have P := shaped_of_shape hA
  subst e
  exact ⟨P.cfg, P.T, P.lnT, P.HA, P.Lam, P.dh, P.dq, P.nM, P.nD, P.oMr, P.oZr, P.oIb, P.oRh, P.oRhp,
    P.atQ, P.atK, P.atV, P.atO, P.kAs, P.u0, P.exp⟩

/-- Ten numbers of the configuration are the reference numbers. -/
structure CfRef (cf : Attention.Cfg) : Prop where
  lt : cf.lt = 10
  lB : cf.lB = 6
  lgk : cf.lgk = 3
  ldh : cf.ldh = 7
  ll : cf.ll = 2
  H : cf.H = 40
  lmS : cf.lmS = 16
  wcH : cf.wcH = 8
  wcO : cf.wcO = 64
  wcQ : cf.wcQ = 64

/-- **The shape that the verifier derives from a configuration with the reference numbers has the
reference numbers**, if its table of exponentials has 2,307 rows. -/
theorem sized_of_shaped {cf : Attention.Cfg} {S : Attention.Shape} (P : Shaped cf S)
    (hc : CfRef cf) (hu : S.u0 = 2307) : AttSized S where
  lgk := by rw [P.cfg, hc.lgk]
  lnT := by simp [P.lnT, hc.lt, hc.lB]
  lB := by rw [P.cfg, hc.lB]
  ldh := by rw [P.cfg, hc.ldh]
  HA := by simp [P.HA, hc.H, hc.lgk]
  Lam := by simp [P.Lam, hc.ll]
  lt := by rw [P.cfg, hc.lt]
  H := by rw [P.cfg, hc.H]
  T := by simp [P.T, hc.lt]
  dh := by simp [P.dh, hc.ldh]
  dq := by simp [P.dq, hc.H, hc.ldh]
  nM := by simp [P.nM, Attention.nMOf, hc.lgk, hc.lt]
  nD := by simp [P.nD, Attention.nDOf, hc.lgk, hc.lt, hc.lB]
  lmS := by rw [P.cfg, hc.lmS]
  wcH := by rw [P.cfg, hc.wcH]
  wcO := by rw [P.cfg, hc.wcO]
  wcQ := by rw [P.cfg, hc.wcQ]
  oMr := P.oMr
  oZr := by simp [P.oZr, hc.ll, hc.H]
  oIb := by simp [P.oIb, hc.ll, hc.H]
  oRh := P.oRh
  oRhp := by simp [P.oRhp, hc.ll, hc.H, hc.ldh]
  atQ := by simp [P.atQ, hc.ll, hc.H, hc.ldh]
  atK := by simp [P.atK, hc.ll, hc.H, hc.ldh, hc.lgk]
  atV := by simp [P.atV, hc.ll, hc.H, hc.ldh, hc.lgk]
  atO := by simp [P.atO, hc.ll, hc.H, hc.ldh, hc.lgk]
  u0 := hu

/-- Columns in whole parts: n parts of the least width that holds 7,200 columns of 65,536 rows. -/
theorem ceil_wide (n : ℕ) (hN : 0 < n) :
    7200 ≤ (471859200 + n * 65536 - 1) / (n * 65536) * n := by
  have hu : 0 < n * 65536 := by omega
  have h1 := Nat.div_add_mod (471859200 + n * 65536 - 1) (n * 65536)
  have h2 := Nat.mod_lt (471859200 + n * 65536 - 1) hu
  generalize (471859200 + n * 65536 - 1) % (n * 65536) = r at h1 h2
  generalize (471859200 + n * 65536 - 1) / (n * 65536) = q at h1 ⊢
  have e : n * 65536 * q = 65536 * (q * n) := by ring
  rw [e] at h1
  generalize q * n = t at h1 ⊢
  omega

/-- **The parts of "as" have together at least the library's 7,200 columns**, for a shape that the
verifier derives from a configuration with the reference numbers and at least one part. -/
theorem wide_of_shaped {cf : Attention.Cfg} {S : Attention.Shape} (P : Shaped cf S)
    (hc : CfRef cf) (hN : 0 < cf.NAs) : 7200 ≤ S.kAs / S.cf.NAs * S.cf.NAs := by
  have k : S.kAs = (471859200 + cf.NAs * 65536 - 1) / (cf.NAs * 65536) * cf.NAs := by
    rw [P.kAs]
    simp [Attention.nMOf, Attention.nDOf, hc.ll, hc.H, hc.lgk, hc.lt, hc.lB, hc.lmS]
  rw [P.cfg, k, Nat.mul_div_cancel _ hN]
  exact ceil_wide _ hN

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.wide_of_shaped
#print axioms OnBytes.Road.L5.shaped_of_shape
#print axioms OnBytes.Road.L5.shaped_of_hid
#print axioms OnBytes.Road.L5.sized_of_shaped
