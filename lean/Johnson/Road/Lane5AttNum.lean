-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttNum.lean

FOR EVERY SHAPE that the verifier's function shape returns: the rule of addresses "addrA"
(Johnson/Road/Lane5AttDef.lean), which is written in the verifier's own records (the first features
oMr, oZr, oIb, oRh, oRhp; the places atQ, atK, atV, atO of the tensors; nM, nD), gives every cell
the LIBRARY's own number at the sizes dimOf S: the address of a cell of a place (AddrFacts.adr), or
matrix, feature and position of another cell (AddrFacts.mat, phi, pos;
Inst/Model/Att/AddrFacts.lean). What differs between the two sides off the reference sizes is the
last step alone: how many rows a column has.

* "tested_of_shape": two tests that shape has made: lB + 2 ≤ lt (af-shape-tiles) and 2^lgk divides H
  (af-shape-heads).
* "Norm S", "norm_of_shaped": the fields of the shape that addrA reads, written in S.Lam, S.HA,
  2^lgk, 2^ldh and S.lnT.
* "addrL S": the library's numbers, laid by the same last step as addrA: asCell, featCell and the
  list numbers NAs, NAs + 1, NAs + 3 (Johnson/Road/Lane5AttDef.lean). That step is ours on both
  sides: a fault in it passes this file.
* "addrA_lib": addrA S c = addrL S c, at ALL names c; "addrA_lib_hid", "addrA_lib_group": the same
  for the shapes that shapeHid returns and that stand in the plans of group.

What is compared with what: a definition of ours, written by a reading of the verifier's forms, with
the library's numbering. The library ties its numbering to its own address map for all sizes
(AddrFacts.addr_c, addr_feat) and shows it one-to-one on the valid names (adr_inj, phi_inj).
Not claimed: that the verifier's forms read the cells by addrA.
-/
import Johnson.Road.Lane5AttPlan
import Inst.Model.Att.AddrFacts

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

/-- Two tests that shape has made. -/
theorem tested_of_shape {cf : Attention.Cfg} {S : Attention.Shape}
    (h : Attention.shape cf = Except.ok S) : cf.lB + 2 ≤ cf.lt ∧ cf.H % 2 ^ cf.lgk = 0 := by
  unfold Attention.shape at h
  obtain ⟨e1, h⟩ := refuse_ok h
  obtain ⟨e2, h⟩ := refuse_ok h
  simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at e1 e2
  exact ⟨Nat.not_lt.mp (of_decide_eq_false e1.2), e2.2⟩

/-- The fields of the shape that addrA reads, in five letters. -/
structure Norm (S : Attention.Shape) : Prop where
  H : S.cf.H = 2 ^ S.cf.lgk * S.HA
  dh : S.dh = 2 ^ S.cf.ldh
  dq : S.dq = 2 ^ S.cf.lgk * S.HA * 2 ^ S.cf.ldh
  lt : S.cf.lt = S.lnT - 1 + 1 + S.cf.lB
  nM : S.nM = S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB
  nD : S.nD = S.cf.lgk + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB
  oMr : S.oMr = 0
  oZr : S.oZr = 4 * S.Lam * (2 ^ S.cf.lgk * S.HA)
  oIb : S.oIb = 8 * S.Lam * (2 ^ S.cf.lgk * S.HA)
  oRh : S.oRh = 0
  oRhp : S.oRhp = S.Lam * (2 ^ S.cf.lgk * S.HA * 2 ^ S.cf.ldh)
  atQ : S.atQ = ⟨0, 2, S.Lam, 2 ^ S.cf.lgk * S.HA * 2 ^ S.cf.ldh⟩
  atK : S.atK = ⟨2 * S.Lam * (2 ^ S.cf.lgk * S.HA * 2 ^ S.cf.ldh), 2, S.Lam,
    2 ^ S.cf.lgk * 2 ^ S.cf.ldh⟩
  atV : S.atV = ⟨2 * S.Lam * (2 ^ S.cf.lgk * S.HA * 2 ^ S.cf.ldh) +
    2 * S.Lam * (2 ^ S.cf.lgk * 2 ^ S.cf.ldh), 2, S.Lam, 2 ^ S.cf.lgk * 2 ^ S.cf.ldh⟩
  atO : S.atO = ⟨2 * S.Lam * (2 ^ S.cf.lgk * S.HA * 2 ^ S.cf.ldh) +
    2 * S.Lam * (2 ^ S.cf.lgk * 2 ^ S.cf.ldh) + 2 * S.Lam * (2 ^ S.cf.lgk * 2 ^ S.cf.ldh), 2, S.Lam,
    2 ^ S.cf.lgk * S.HA * 2 ^ S.cf.ldh⟩

theorem norm_of_shaped {cf : Attention.Cfg} {S : Attention.Shape} (P : Shaped cf S)
    (ht : cf.lB + 2 ≤ cf.lt) (hh : cf.H % 2 ^ cf.lgk = 0) : Norm S := by
  have eH : 2 ^ cf.lgk * (cf.H / 2 ^ cf.lgk) = cf.H :=
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hh)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, P.oMr, ?_, ?_, P.oRh, ?_, ?_, ?_, ?_, ?_⟩
  · rw [P.cfg, P.HA, eH]
  · rw [P.dh, P.cfg]
  · rw [P.dq, P.cfg, P.HA, eH]
  · rw [P.cfg, P.lnT]
    omega
  · rw [P.nM, P.cfg, P.lnT]
    unfold Attention.nMOf
    omega
  · rw [P.nD, P.cfg, P.lnT]
    unfold Attention.nDOf
    omega
  · rw [P.oZr, P.Lam, P.cfg, P.HA, eH]
  · rw [P.oIb, P.Lam, P.cfg, P.HA, eH]
  · rw [P.oRhp, P.Lam, P.cfg, P.HA, eH]
  · rw [P.atQ, P.Lam, P.cfg, P.HA, eH]
  · rw [P.atK, P.Lam, P.cfg, P.HA, eH]
  · rw [P.atV, P.Lam, P.cfg, P.HA, eH]
  · rw [P.atO, P.Lam, P.cfg, P.HA, eH]

/-- **The library's numbers at the sizes dimOf S, laid in the verifier's matrices by the verifier's
heights.** -/
def addrL (S : Attention.Shape) : AttSeg.Raw → ℕ × ℕ × ℕ
  | .c ρ jj b x => asCell S (AttSeg.AddrFacts.adr (dimOf S) ρ jj b x)
  | c =>
    match AttSeg.AddrFacts.mat c with
    | .ah =>
      featCell S S.cf.NAs S.cf.wcH (AttSeg.AddrFacts.phi (dimOf S) c) (AttSeg.AddrFacts.pos c)
    | .ao =>
      featCell S (S.cf.NAs + 1) S.cf.wcO (AttSeg.AddrFacts.phi (dimOf S) c)
        (AttSeg.AddrFacts.pos c)
    | _ =>
      featCell S (S.cf.NAs + 3) S.cf.wcQ (AttSeg.AddrFacts.phi (dimOf S) c)
        (AttSeg.AddrFacts.pos c)

/-- Pair number b is the layer b / A and the head b % A. -/
theorem pairG (L A jj b : ℕ) : (jj * L + b / A) * A + b % A = L * A * jj + b := by
  have h := Nat.div_add_mod' b A
  calc (jj * L + b / A) * A + b % A = jj * L * A + (b / A * A + b % A) := by ring
    _ = L * A * jj + b := by
      rw [h]
      ring

/-- **addrA gives every cell the library's own number**, at every name. -/
theorem addrA_norm {S : Attention.Shape} (N : Norm S) : ∀ c : AttSeg.Raw, addrA S c = addrL S c
  | .c .M jj b x => by
    show asCell S (((jj * S.Lam + b / S.HA) * S.HA + b % S.HA) * 2 ^ S.nM + x) =
      asCell S (2 ^ (S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB) * (S.Lam * S.HA
        * jj + b) + x)
    rw [pairG, N.nM]
    refine congrArg (asCell S) ?_
    ring
  | .c .D jj b x => by
    show asCell S (5 * S.Lam * S.HA * 2 ^ S.nM + ((jj * S.Lam + b / S.HA) * S.HA + b % S.HA) * 2 ^
      S.nD + x) =
      asCell S (2 ^ (S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB) * (S.Lam * S.HA
        * 5) + (2 ^ (S.cf.lgk + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB) * (S.Lam * S.HA * jj + b) +
        x))
    rw [pairG, N.nM, N.nD]
    refine congrArg (asCell S) ?_
    ring
  | .mx k b g i => by
    show featCell S S.cf.NAs S.cf.wcH (S.oMr + (k * S.Lam + b / S.HA) * S.cf.H + (g * S.HA + b %
      S.HA)) i =
      featCell S S.cf.NAs S.cf.wcH (2 ^ S.cf.lgk * S.HA * (S.Lam * k + b / S.HA) + (S.HA * g + b %
        S.HA)) i
    rw [N.oMr, N.H]
    refine congrArg (fun φ => featCell S S.cf.NAs S.cf.wcH φ i) ?_
    ring
  | .den k b g i => by
    show featCell S S.cf.NAs S.cf.wcH (S.oZr + (k * S.Lam + b / S.HA) * S.cf.H + (g * S.HA + b %
      S.HA)) i =
      featCell S S.cf.NAs S.cf.wcH (4 * (2 ^ S.cf.lgk * S.HA * S.Lam) + (2 ^ S.cf.lgk * S.HA *
        (S.Lam * k + b / S.HA) + (S.HA * g + b % S.HA))) i
    rw [N.oZr, N.H]
    refine congrArg (fun φ => featCell S S.cf.NAs S.cf.wcH φ i) ?_
    ring
  | .ib k b g i => by
    show featCell S S.cf.NAs S.cf.wcH (S.oIb + (0 * S.Lam + b / S.HA) * (S.cf.lt * S.cf.H) + (k *
      S.cf.H + g * S.HA + b % S.HA)) i =
      featCell S S.cf.NAs S.cf.wcH (8 * (2 ^ S.cf.lgk * S.HA * S.Lam) + (2 ^ S.cf.lgk * S.HA *
        ((S.lnT - 1 + 1 + S.cf.lB) * (b / S.HA) + k) + (S.HA * g + b % S.HA))) i
    rw [N.oIb, N.lt, N.H]
    refine congrArg (fun φ => featCell S S.cf.NAs S.cf.wcH φ i) ?_
    ring
  | .qh b g i n => by
    show featCell S (S.cf.NAs + 1) S.cf.wcO (S.oRh + (0 * S.Lam + b / S.HA) * S.dq + (g * S.HA + b
      % S.HA) * S.dh + n) i =
      featCell S (S.cf.NAs + 1) S.cf.wcO (2 ^ S.cf.ldh * (2 ^ S.cf.lgk * S.HA * (b / S.HA) + (S.HA
        * g + b % S.HA)) + n) i
    rw [N.oRh, N.dq, N.dh]
    refine congrArg (fun φ => featCell S (S.cf.NAs + 1) S.cf.wcO φ i) ?_
    ring
  | .qh' b g i n => by
    show featCell S (S.cf.NAs + 1) S.cf.wcO (S.oRhp + (0 * S.Lam + b / S.HA) * S.dq + (g * S.HA +
      b % S.HA) * S.dh + n) i =
      featCell S (S.cf.NAs + 1) S.cf.wcO ((2 ^ S.cf.ldh * (2 ^ S.cf.lgk * S.HA * S.Lam)) + (2 ^
        S.cf.ldh * (2 ^ S.cf.lgk * S.HA * (b / S.HA) + (S.HA * g + b % S.HA)) + n)) i
    rw [N.oRhp, N.dq, N.dh]
    refine congrArg (fun φ => featCell S (S.cf.NAs + 1) S.cf.wcO φ i) ?_
    ring
  | .qry k b g i n => by
    show featCell S (S.cf.NAs + 3) S.cf.wcQ (Model.tenCell S.atQ k (b / S.HA) ((g * S.HA + b %
      S.HA) * S.dh) + n) i =
      featCell S (S.cf.NAs + 3) S.cf.wcQ (2 ^ S.cf.ldh * (2 ^ S.cf.lgk * S.HA * (S.Lam * k + b /
        S.HA) + (S.HA * g + b % S.HA)) + n) i
    rw [N.atQ, N.dh]
    refine congrArg (fun φ => featCell S (S.cf.NAs + 3) S.cf.wcQ φ i) ?_
    show 0 + (k * S.Lam + b / S.HA) * (2 ^ S.cf.lgk * S.HA * 2 ^ S.cf.ldh) + (g * S.HA + b % S.HA)
      * 2 ^ S.cf.ldh + n = _
    ring
  | .out k b g i n => by
    show featCell S (S.cf.NAs + 3) S.cf.wcQ (Model.tenCell S.atO k (b / S.HA) ((g * S.HA + b %
      S.HA) * S.dh) + n) i =
      featCell S (S.cf.NAs + 3) S.cf.wcQ (2 * (2 ^ S.cf.ldh * (2 ^ S.cf.lgk * S.HA * S.Lam)) + 4 *
        (2 ^ S.cf.ldh * (2 ^ S.cf.lgk * S.Lam)) + (2 ^ S.cf.ldh * (2 ^ S.cf.lgk * S.HA * (S.Lam *
        k + b / S.HA) + (S.HA * g + b % S.HA)) + n)) i
    rw [N.atO, N.dh]
    refine congrArg (fun φ => featCell S (S.cf.NAs + 3) S.cf.wcQ φ i) ?_
    show 2 * S.Lam * (2 ^ S.cf.lgk * S.HA * 2 ^ S.cf.ldh) + 2 * S.Lam * (2 ^ S.cf.lgk * 2 ^
      S.cf.ldh) + 2 * S.Lam * (2 ^ S.cf.lgk * 2 ^ S.cf.ldh) + (k * S.Lam + b / S.HA) * (2 ^
      S.cf.lgk * S.HA * 2 ^ S.cf.ldh) + (g * S.HA + b % S.HA) * 2 ^ S.cf.ldh + n = _
    ring
  | .key k lam g j n => by
    show featCell S (S.cf.NAs + 3) S.cf.wcQ (Model.tenCell S.atK k lam (g * S.dh) + n) j =
      featCell S (S.cf.NAs + 3) S.cf.wcQ (2 * (2 ^ S.cf.ldh * (2 ^ S.cf.lgk * S.HA * S.Lam)) + (2
        ^ S.cf.ldh * (2 ^ S.cf.lgk * (S.Lam * k + lam) + g) + n)) j
    rw [N.atK, N.dh]
    refine congrArg (fun φ => featCell S (S.cf.NAs + 3) S.cf.wcQ φ j) ?_
    show 2 * S.Lam * (2 ^ S.cf.lgk * S.HA * 2 ^ S.cf.ldh) + (k * S.Lam + lam) * (2 ^ S.cf.lgk * 2
      ^ S.cf.ldh) + g * 2 ^ S.cf.ldh + n = _
    ring
  | .val k lam g j n => by
    show featCell S (S.cf.NAs + 3) S.cf.wcQ (Model.tenCell S.atV k lam (g * S.dh) + n) j =
      featCell S (S.cf.NAs + 3) S.cf.wcQ (2 * (2 ^ S.cf.ldh * (2 ^ S.cf.lgk * S.HA * S.Lam)) + 2 *
        (2 ^ S.cf.ldh * (2 ^ S.cf.lgk * S.Lam)) + (2 ^ S.cf.ldh * (2 ^ S.cf.lgk * (S.Lam * k +
        lam) + g) + n)) j
    rw [N.atV, N.dh]
    refine congrArg (fun φ => featCell S (S.cf.NAs + 3) S.cf.wcQ φ j) ?_
    show 2 * S.Lam * (2 ^ S.cf.lgk * S.HA * 2 ^ S.cf.ldh) + 2 * S.Lam * (2 ^ S.cf.lgk * 2 ^
      S.cf.ldh) + (k * S.Lam + lam) * (2 ^ S.cf.lgk * 2 ^ S.cf.ldh) + g * 2 ^ S.cf.ldh + n = _
    ring

/-- **For every shape that the verifier's function shape returns.** -/
theorem addrA_lib {cf : Attention.Cfg} {S : Attention.Shape}
    (h : Attention.shape cf = Except.ok S) (c : AttSeg.Raw) : addrA S c = addrL S c :=
  addrA_norm (norm_of_shaped (shaped_of_shape h) (tested_of_shape h).1 (tested_of_shape h).2) c

/-- shapeHid has called shape. -/
theorem shape_of_hid {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape}
    {fs : Model.Forest.Shape} (h : Attention.shapeHid lid cf = Except.ok (S, fs)) :
    ∃ A, Attention.shape cf = Except.ok A := by
  unfold Attention.shapeHid at h
  obtain ⟨A, hA, -⟩ := bind_ok h
  exact ⟨A, hA⟩

/-- The same for a shape that shapeHid returns. -/
theorem addrA_lib_hid {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape}
    {fs : Model.Forest.Shape} (h : Attention.shapeHid lid cf = Except.ok (S, fs))
    (c : AttSeg.Raw) : addrA S c = addrL S c := by
  obtain ⟨A, hA⟩ := shape_of_hid h
  exact addrA_norm
    (norm_of_shaped (shaped_of_hid h) (tested_of_shape hA).1 (tested_of_shape hA).2) c

/-- The same for the shape in the plan that group returns. -/
theorem addrA_lib_group {P : Model.PolScan} {y : Model.Layer.Lay} {sc : Model.Layer.Scales}
    {midQ : ℕ → ℕ} {lines : List Attention.Line} {g : ℕ} {X : Attention.Plan}
    (h : Attention.group P y sc midQ lines g = Except.ok X) (c : AttSeg.Raw) :
    addrA X.S c = addrL X.S c := by
  obtain ⟨cf, -, hp, -⟩ := group_plan h
  exact addrA_lib_hid (plan_shape hp).1 c

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.addrA_lib_group
#print axioms OnBytes.Road.L5.tested_of_shape
#print axioms OnBytes.Road.L5.norm_of_shaped
#print axioms OnBytes.Road.L5.addrA_lib
