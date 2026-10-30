-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/AttNumsScope.lean: the numbers of the lookup of an attention sub-proof, at all
public files in the goals' scope: they are the library's reference numbers, and they fit the
segment's sizes.

FourCalls (Johnson/Road/Lane5AttLaid.lean:354) bounds each call's number of keys from
below. Here the numbers themselves, for g < 12, at S := Hd.shapeA X g and fs := fsA X g:
  ns_of_list, ns_of_hid: under the usual call list each call's n is the larger of nmin and the
    rounded-up logarithm of what its pieces take. General in the configuration.
  forest_nums: what Forest.shape returns as dT and rK. hid_forest: shapeHid's record has them.
  ns_ref, nums_of_hid: at the reference numbers, nmin at most 25 and the cap 28.
  att_nums_in_scope: the four calls have 2^27, 2^27, 2^26, 2^25 keys; a tree has 2^25 keys (dT); the
    trees' numbers have 4 bits (rK).
  att_dim_in_scope: dimOf S is the library's Dim.ref.
  callsOf_in_scope: Rows.callsOf fs (Johnson/Road/Rows/AttCalls.lean:45) is the library's Calls.ref.
  nOf_in_scope: FoNums.nOf fs is 27, 27, 26, 25 at the calls 0 to 3.
  attFits_in_scope: the library's condition between the lookup's record and the segment's sizes
    (Cb.Rider.AttFits, OnBytes/Tie/Pv/Lookup/Rider/Model/Denom.lean:51) at dimOf S and
    Rows.callsOf fs. attFits_six: its six clauses on numbers as one conjunction.
-/
import Johnson.Goal.Meaning.AttForInScope
import Johnson.Road.Rows.AttCalls
import OnBytes.Tie.Pv.Lookup.Rider.Model.Denom

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Att

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf Public layerShape)
open Attention (ACall Cfg Shape Table Seg Line shape shapeHid expandLine placePieces segBits nMOf
  nDOf)

/-! ## Each call's number of keys, under the usual call list -/

/-- The four numbers, from what shape has run. f: what a later step does to call number i; it leaves
the number n. -/
theorem ns_of_list {cf : Cfg} {S A : Shape} (hA : shape cf = Except.ok A) (U : UsualCalls cf)
    (f : ℕ → ACall → ACall) (hf : ∀ i k, (f i k).call.n = k.call.n)
    (hS : S.calls.toList = A.calls.toList.mapIdx f) :
    S.calls.toList = [callAt S 0, callAt S 1, callAt S 2, callAt S 3] ∧
    (callAt S 0).call.n = max (ceilLog2 (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nMOf cf +
      2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nDOf cf)) cf.nmin ∧
    (callAt S 1).call.n = max (ceilLog2 (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nMOf cf +
      2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nDOf cf)) cf.nmin ∧
    (callAt S 2).call.n = max (ceilLog2 (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .wl +
      2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .ix)) cf.nmin ∧
    (callAt S 3).call.n =
      max (ceilLog2 (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .wh)) cf.nmin := by
  obtain ⟨hlt, hHA⟩ := tests_of_shape hA
  obtain ⟨calls, hM, hc, -, hsz⟩ := calls_of_shape hA
  obtain ⟨n0, n1, n2, n3, hL⟩ := U.lines
  rw [shsOf_one hsz U.one, hL] at hM
  have hx : ([⟨n0, .kr, [.rm, .rd]⟩, ⟨n1, .kfd, [.fm, .fd]⟩, ⟨n2, .r16, [.wl, .ix]⟩,
      ⟨n3, .wh, [.wh]⟩] : List Line).flatMap (expandLine [cf.sh.getD 0 0]) =
      [(n0 ++ "", .kr, cf.sh.getD 0 0, [.rm, .rd]), (n1 ++ "", .kfd, cf.sh.getD 0 0, [.fm, .fd]),
        (n2, .r16, 0, [.wl, .ix]), (n3, .wh, 0, [.wh])] := rfl
  rw [hx] at hM
  obtain ⟨k0, r0, h0, hM0, rfl⟩ := mapM_cons_ok hM
  obtain ⟨k1, r1, h1, hM1, rfl⟩ := mapM_cons_ok hM0
  obtain ⟨k2, r2, h2, hM2, rfl⟩ := mapM_cons_ok hM1
  obtain ⟨k3, r3, h3, hM3, rfl⟩ := mapM_cons_ok hM2
  have hr : r3 = [] := by
    rw [List.mapM_nil] at hM3
    exact (Except.ok.inj hM3).symm
  subst hr
  have hT : S.calls.toList = [f 0 k0, f 1 k1, f 2 k2, f 3 k3] := by
    rw [hS, hc]
    simp [List.mapIdx_cons]
  have c0 : callAt S 0 = f 0 k0 := by rw [callAt_of_list hT]; rfl
  have c1 : callAt S 1 = f 1 k1 := by rw [callAt_of_list hT]; rfl
  have c2 : callAt S 2 = f 2 k2 := by rw [callAt_of_list hT]; rfl
  have c3 : callAt S 3 = f 3 k3 := by rw [callAt_of_list hT]; rfl
  have a4 := (layCall_parts h0).2.2.2
  have b4 := (layCall_parts h1).2.2.2
  have d4 := (layCall_parts h2).2.2.2
  have e4 := (layCall_parts h3).2.2.2
  have hMD : nDOf cf ≤ nMOf cf := by
    unfold Attention.nDOf Attention.nMOf
    omega
  have hWX : segBits cf .ix ≤ segBits cf .wl := by
    show cf.lgk + cf.lt ≤ 1 + cf.lgk + cf.lt + cf.ldh
    omega
  have noSh : ∀ {k : Table}, k.bySh = false →
      k.bySh = true → ∀ lam < 2 ^ cf.ll, cf.sh.getD lam 0 = 0 := by
    intro k hk hk'
    rw [hk] at hk'
    cases hk'
  have P0 := place_two (kind := .kr) hHA (fun _ => U.one) .rm .rd hMD
  have P1 := place_two (kind := .kfd) hHA (fun _ => U.one) .fm .fd hMD
  have P2 := place_two (kind := .r16) hHA (noSh rfl) .wl .ix hWX
  have P3 := place_one (kind := .wh) hHA (noSh rfl) .wh
  refine ⟨by rw [hT, c0, c1, c2, c3], ?_, ?_, ?_, ?_⟩
  · rw [c0, hf 0 k0, a4, P0]
    simp [segBits]
  · rw [c1, hf 1 k1, b4, P1]
    simp [segBits]
  · rw [c2, hf 2 k2, d4, P2]
    simp
  · rw [c3, hf 3 k3, e4, P3]
    simp

/-! ## What Forest.shape returns as dT and rK -/

theorem forest_nums {calls : Array Call} {lid : ℕ} {fo : Forest.Shape}
    (h : Forest.shape calls lid = .ok fo) :
    fo.dT = calls.foldl (fun m c => min m c.n) lid ∧
      fo.rK = clog2 ((calls.map fun c => c.n - fo.dT).foldl (fun s i => s + 2 ^ i) 0) := by
  unfold Forest.shape at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r, -, h⟩ := ok_of_bind h
  obtain ⟨callOf, first, free⟩ := r
  obtain ⟨-, h⟩ := ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨rfl, rfl⟩

/-- shapeHid's record of the lookup has the numbers that Forest.shape returns on shape's calls. -/
theorem hid_forest {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Forest.Shape}
    (h : shapeHid lid cf = Except.ok (S, fs)) :
    ∃ (A : Shape) (fo : Forest.Shape), shape cf = Except.ok A ∧
      Forest.shape (A.calls.map (·.call)) lid = .ok fo ∧ fs.dT = fo.dT ∧ fs.rK = fo.rK := by
  unfold Attention.shapeHid at h
  obtain ⟨A, hA, h⟩ := bind_ok h
  obtain ⟨fo, hfo, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Except.ok.inj h)
  subst e1
  subst e2
  exact ⟨A, fo, hA, hfo, rfl, rfl⟩

/-! ## At the reference numbers -/

theorem clog_a : ceilLog2 94371840 = 27 := by decide +kernel
theorem clog_b : ceilLog2 42106880 = 26 := by decide +kernel
theorem clog_c : ceilLog2 20971520 = 25 := by decide +kernel
theorem clog_t : clog2 11 = 4 := by decide +kernel

/-- The three sums of pieces at the reference numbers. -/
theorem sums_ref {cf : Cfg} (hc : CfRef cf) :
    2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nMOf cf +
        2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nDOf cf = 94371840 ∧
      2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .wl +
        2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .ix = 42106880 ∧
      2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .wh = 20971520 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Attention.nMOf Attention.nDOf
    rw [hc.ll, hc.H, hc.lgk, hc.lt, hc.lB]
    norm_num
  · show 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ (1 + cf.lgk + cf.lt + cf.ldh) +
      2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ (cf.lgk + cf.lt) = 42106880
    rw [hc.ll, hc.H, hc.lgk, hc.lt, hc.ldh]
    norm_num
  · show 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ (cf.lgk + cf.lt + cf.ldh) = 20971520
    rw [hc.ll, hc.H, hc.lgk, hc.lt, hc.ldh]
    norm_num

/-- The four numbers of keys at the reference numbers. -/
theorem ns_ref {cf : Cfg} {S A : Shape} (hA : shape cf = Except.ok A) (U : UsualCalls cf)
    (hc : CfRef cf) (hn : cf.nmin ≤ 25) (f : ℕ → ACall → ACall)
    (hf : ∀ i k, (f i k).call.n = k.call.n) (hS : S.calls.toList = A.calls.toList.mapIdx f) :
    S.calls.toList = [callAt S 0, callAt S 1, callAt S 2, callAt S 3] ∧
      (callAt S 0).call.n = 27 ∧ (callAt S 1).call.n = 27 ∧ (callAt S 2).call.n = 26 ∧
      (callAt S 3).call.n = 25 := by
  obtain ⟨hT, a0, a1, a2, a3⟩ := ns_of_list hA U f hf hS
  obtain ⟨s0, s2, s3⟩ := sums_ref hc
  rw [s0, clog_a] at a0 a1
  rw [s2, clog_b] at a2
  rw [s3, clog_c] at a3
  exact ⟨hT, by omega, by omega, by omega, by omega⟩

/-- All numbers of the lookup at what shapeHid returns on a configuration with the reference numbers
and the usual call list, at the cap 28. -/
theorem nums_of_hid {cf : Cfg} {S : Shape} {fs : Forest.Shape}
    (h : shapeHid 28 cf = Except.ok (S, fs)) (U : UsualCalls cf) (hc : CfRef cf)
    (hn : cf.nmin ≤ 25) :
    ((callAt S 0).call.n = 27 ∧ (callAt S 1).call.n = 27 ∧ (callAt S 2).call.n = 26 ∧
      (callAt S 3).call.n = 25) ∧ fs.dT = 25 ∧ fs.rK = 4 := by
  obtain ⟨A, fo, hA, hfo, e1, e2⟩ := hid_forest h
  obtain ⟨A', io, kbA, hA', eS, -⟩ := hid_calls h
  have eA : A' = A := Except.ok.inj (hA'.symm.trans hA)
  subst eA
  have NS := ns_ref (S := S) hA' U hc hn
    (fun q c => { c with call := { c.call with iota := io q } }) (fun _ _ => rfl)
    (by rw [eS]; exact Array.toList_mapIdx ..)
  obtain ⟨hT, b0, b1, b2, b3⟩ := ns_ref (S := A') hA' U hc hn (fun _ k => k) (fun _ _ => rfl)
    (mapIdx_keep _).symm
  obtain ⟨d1, d2⟩ := forest_nums hfo
  have hd : fo.dT = 25 := by
    rw [d1, ← Array.foldl_toList, Array.toList_map, hT]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [b0, b1, b2, b3]
    rfl
  have hr : fo.rK = 4 := by
    rw [d2, hd, ← Array.foldl_toList, Array.toList_map, Array.toList_map, hT]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [b0, b1, b2, b3]
    exact clog_t
  exact ⟨NS.2, e1.trans hd, e2.trans hr⟩

/-! ## In scope -/

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- The numbers of the lookup of the attention sub-proof of group g. -/
theorem att_nums_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    ((callAt (Hd.shapeA X g) 0).call.n = 27 ∧ (callAt (Hd.shapeA X g) 1).call.n = 27 ∧
      (callAt (Hd.shapeA X g) 2).call.n = 26 ∧ (callAt (Hd.shapeA X g) 3).call.n = 25) ∧
      (fsA X g).dT = 25 ∧ (fsA X g).rK = 4 := by
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.public_of_core h A
  have U := attUsualK_at (attUsualK_in_scope hZ hR h) hg
  obtain ⟨Ag, lines, cf, hA, eS, hf, hh, -⟩ := hid_of_public h B.p4 (by rw [B.groups]; exact hg)
  obtain ⟨hc, -, -, -⟩ := cfRef_of_fill hf (Hd.fillRef_of_core A B)
  have ec : (Hd.shapeA X g).cf = cf := by
    rw [← eS]
    exact (shaped_of_hid hh).cfg
  have ef : fsA X g = Ag.fs := by
    unfold fsA
    rw [hA]
    rfl
  rw [ec] at U
  have hn : cf.nmin ≤ 25 := by
    rw [fill_eq hf]
    show X.P.h.nmin ≤ 25
    rw [Hd.scan_of_scope hZ hR h]
    exact Nat.le_of_ble_eq_true rfl
  have hl : X.P.settings.lidb = 28 := by
    rw [Hd.scan_of_scope hZ hR h]
    rfl
  rw [hl] at hh
  rw [← eS, ef]
  exact nums_of_hid hh (usual_of_test U.1) hc hn

theorem att_dim_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    dimOf (Hd.shapeA X g) = Inst.Model.AttSeg.Dim.ref := by
  obtain ⟨cf, hh, hc, -, h12, h8, -⟩ := hid_in_scope hZ hR h hg
  have hS := attSized_hid hh hc h12 h8
  rw [dimOf_ref hS, hS.u0]
  rfl

/-- A call's record in the lookup's record. -/
theorem att_call_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {k : ℕ} (hk : k < 4) :
    (fsA X g).calls[k]? = some (callAt (Hd.shapeA X g) k).call :=
  (sameCalls_in_scope hZ hR h hg).callAt hk

theorem nOf_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    FoNums.nOf (fsA X g) 0 = 27 ∧ FoNums.nOf (fsA X g) 1 = 27 ∧
      FoNums.nOf (fsA X g) 2 = 26 ∧ FoNums.nOf (fsA X g) 3 = 25 := by
  obtain ⟨⟨n0, n1, n2, n3⟩, -, -⟩ := att_nums_in_scope hZ hR h hg
  unfold FoNums.nOf
  rw [att_call_in_scope hZ hR h hg (by norm_num : 0 < 4),
    att_call_in_scope hZ hR h hg (by norm_num : 1 < 4),
    att_call_in_scope hZ hR h hg (by norm_num : 2 < 4),
    att_call_in_scope hZ hR h hg (by norm_num : 3 < 4)]
  exact ⟨n0, n1, n2, n3⟩

/-- The library's numbers of the lookup, made from the verifier's record, are the reference's. -/
theorem callsOf_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    Rows.callsOf (fsA X g) = Inst.Model.AttSeg.Calls.ref := by
  obtain ⟨⟨n0, n1, n2, n3⟩, hd, hr⟩ := att_nums_in_scope hZ hR h hg
  have ha : ∀ k, k < 4 →
      ((fsA X g).calls.getD k default).n = (callAt (Hd.shapeA X g) k).call.n := by
    intro k hk
    rw [Array.getD_eq_getD_getElem?, att_call_in_scope hZ hR h hg hk]
    rfl
  have hf : (fun c : Fin 4 => ((fsA X g).calls.getD c.val default).n) = ![27, 27, 26, 25] := by
    funext c
    rw [ha c.val c.isLt]
    fin_cases c
    exacts [n0, n1, n2, n3]
  unfold Rows.callsOf Inst.Model.AttSeg.Calls.ref
  rw [hf, hd, hr]

/-- THE LIBRARY's CONDITION BETWEEN THE LOOKUP's RECORD AND THE SEGMENT's SIZES, in scope. -/
theorem attFits_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    Cb.Rider.AttFits (fsA X g) (dimOf (Hd.shapeA X g)) (Rows.callsOf (fsA X g)) := by
  obtain ⟨-, hd, hr⟩ := att_nums_in_scope hZ hR h hg
  rw [att_dim_in_scope hZ hR h hg, callsOf_in_scope hZ hR h hg]
  exact Cb.Rider.attFits_ref hd hr (nOf_in_scope hZ hR h hg).2.2.1

/-- Its six clauses on numbers, as one conjunction. -/
theorem attFits_six (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    FoNums.nOf (fsA X g) 2 = (Rows.callsOf (fsA X g)).a 2 ∧
      (Rows.callsOf (fsA X g)).Dk ≤ (Rows.callsOf (fsA X g)).a 2 ∧
      (Rows.callsOf (fsA X g)).e 2 ≤ (Rows.callsOf (fsA X g)).sg ∧
      (dimOf (Hd.shapeA X g)).lW ≤ (Rows.callsOf (fsA X g)).a 2 ∧
      (dimOf (Hd.shapeA X g)).nb ≤
        2 ^ ((Rows.callsOf (fsA X g)).a 2 - (dimOf (Hd.shapeA X g)).lW) ∧
      1 ≤ (fsA X g).v := by
  have F := attFits_in_scope hZ hR h hg
  exact ⟨F.n2, F.le, F.e2, F.lw, F.nb, F.v1⟩

#print axioms ns_of_list
#print axioms forest_nums
#print axioms nums_of_hid
#print axioms att_nums_in_scope
#print axioms att_dim_in_scope
#print axioms nOf_in_scope
#print axioms callsOf_in_scope
#print axioms attFits_in_scope
#print axioms attFits_six

end Meaning.Att
