-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/KeyNumsOf.lean: kind K5: the record KeyNums
(Johnson/Desc/First/Att/Claims/KeyPubOf.lean), paid: at a shape that shapeHid returns at the usual
call list, the shift of the softmax-table call, its padding key and its pieces' lists are what the
key forms' law takes.

Main names:
  `layCall_kfd`: what layCall returns for a softmax-table call: its padding row is row number
    Tt.size; its table is tableOf kFD (rowKFD …).
  `shTests_parts`: three of the planner's tests on a shift, read off their return.
  `pad_row`: that row of the table is u0 2^sh + 2^32 − 2^sh, as a word of the field.
  `keyNums_of_hid`: shapeHid lid cf = ok (S, fs), UsualCalls cf, CallsFit S fs and NumsA S give
    KeyNums S (callAt S 1). sh and pcs: FourCalls.sh and FourCalls.p1
    (Johnson/Road/Lane5AttLaid.lean); 1 ≤ u0: ExpOK in CallsFit (Johnson/Road/Lane5CallsOf.lean);
    Sm: NumsA.Sm (Johnson/Road/Lane5KvKey.lean).
Limit: UsualCalls is no test of the verifier (Johnson/Road/Lane5AttLaid.lean says so of itself): the
verifier takes other call lists, and groups with two shifts; at another list this file says nothing.
Nor does the verifier ask CallsFit or NumsA.
Used of OnBytes and Johnson/Road: as Johnson/Desc/First/Att/Claims/PlaceOf.lean, and four_of_hid,
shaped_of_hid, forM_mem; the planner's pure functions layCall, shTests, rowKFD, tableOf, shdOf;
Call.tauAt, fOfNat.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Lane5CallsOf
import Johnson.Road.Lane5KvKey
import Johnson.Desc.First.Att.Claims.PlaceOf
import Johnson.Desc.First.Att.Claims.KeyPubOf

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road
open OnBytes.Road.L5 (callAt UsualCalls)

/-- What layCall returns for a softmax-table call: where its padding row stands, and its table. -/
theorem layCall_kfd {cf : Cfg} {HA Sm : ℕ} {Tt : Array ℕ} {name : String} {sh : ℕ}
    {segs : List Attention.Seg} {k : ACall}
    (h : layCall cf HA Sm Tt (name, .kfd, sh, segs) = Except.ok k) :
    k.call.t0 = Tt.size ∧ k.call.tau = tableOf cf.kFD (rowKFD Tt (shdOf Tt.size Sm sh) sh) := by
  unfold Attention.layCall at h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  have e := Except.ok.inj h
  subst e
  exact ⟨rfl, rfl⟩

/-- Three of the tests on a shift, read off their return. -/
theorem shTests_parts {cf : Cfg} {u0 Sm sh : ℕ} (h : shTests cf u0 Sm sh = Except.ok PUnit.unit) :
    sh ≤ 12 ∧ u0 + (shdOf u0 Sm sh).nHD ≤ 2 ^ cf.kFD ∧ (shdOf u0 Sm sh).C + 65536 ≤ 2 ^ 24 := by
  unfold Attention.shTests at h
  obtain ⟨e1, h⟩ := L5.refuse_ok h
  obtain ⟨e2, h⟩ := L5.refuse_ok h
  obtain ⟨e3, h⟩ := L5.refuse_ok h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at e1 e2 e3
  exact ⟨by omega, by omega, by omega⟩

/-- **The padding row of the table of a softmax-table call.** -/
theorem pad_row {k : ℕ} {Tt : Array ℕ} {Sm sh : ℕ} (hs : sh ≤ 12) (h1 : 1 ≤ Tt.size)
    (hr : Tt.size + (shdOf Tt.size Sm sh).nHD ≤ 2 ^ k) (hC : (shdOf Tt.size Sm sh).C + 65536 ≤ 2 ^ 24)
    (c : Call) (ht : c.t0 = Tt.size) (hτ : c.tau = tableOf k (rowKFD Tt (shdOf Tt.size Sm sh) sh)) :
    c.tauAt c.t0 = fOfNat (Tt.size * 2 ^ sh + 2 ^ 32 - 2 ^ sh) := by
  have hp : (2 : ℕ) ^ sh ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hs
  have hrho : 0 < 65536 - 2 ^ sh := by
    have : (2 : ℕ) ^ 12 = 4096 := by norm_num
    omega
  have hn : 0 < (shdOf Tt.size Sm sh).nHD := by
    show 0 < (4 * Sm + 1 + (65536 - 2 ^ sh) - 1) / (65536 - 2 ^ sh)
    exact Nat.div_pos (by omega) hrho
  have hlt : Tt.size < 2 ^ k := by omega
  have hC' : Tt.size * 2 ^ sh + 65536 ≤ 2 ^ 24 := hC
  have hle : 2 ^ sh ≤ Tt.size * 2 ^ sh := Nat.le_mul_of_pos_left _ h1
  have hrow : rowKFD Tt (shdOf Tt.size Sm sh) sh Tt.size = Tt.size * 2 ^ sh + 2 ^ 32 - 2 ^ sh := by
    unfold rowKFD
    simp only [Nat.lt_irrefl, if_false, if_pos (Nat.lt_add_of_pos_right hn), Nat.sub_self, Nat.mul_zero,
      Nat.add_zero]
    show Tt.size * 2 ^ sh - 2 ^ sh + 2 ^ 32 = _
    omega
  unfold Call.tauAt
  rw [hτ, ht]
  unfold tableOf
  simp only
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hlt]
  show UInt64.ofNat (rowKFD Tt (shdOf Tt.size Sm sh) sh Tt.size) = _
  rw [hrow]
  unfold fOfNat
  have hpW : pW.toNat = 18446744069414584321 := rfl
  have h24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have hb : Tt.size * 2 ^ sh + 2 ^ 32 - 2 ^ sh < pW.toNat := by
    refine Nat.lt_of_le_of_lt (Nat.sub_le _ _) ?_
    rw [hpW, h32]
    omega
  rw [Nat.mod_eq_of_lt hb]

/-- **KeyNums, paid**: at a shape that shapeHid returns at the usual call list, whose numbers fit the lookup's and are the library's. -/
theorem keyNums_of_hid {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Model.Forest.Shape}
    (h : shapeHid lid cf = Except.ok (S, fs)) (U : UsualCalls cf) (hF : L5.CallsFit S fs)
    (NA : L5.NumsA S) : KeyNums S (callAt S 1) := by
  have Fo := L5.four_of_hid h U
  have Sh := L5.shaped_of_hid h
  have hu : 0 < S.u0 := hF.2.2.2.2.2.1.pos
  obtain ⟨A, io, kbA, hA, eS, -⟩ := L5.hid_calls h
  obtain ⟨calls, hM, hc, hTs, hsz⟩ := L5.calls_of_shape hA
  obtain ⟨n0, n1, n2, n3, hL⟩ := U.lines
  rw [L5.shsOf_one hsz U.one] at hTs
  rw [L5.shsOf_one hsz U.one, hL] at hM
  have hx : ([⟨n0, .kr, [.rm, .rd]⟩, ⟨n1, .kfd, [.fm, .fd]⟩, ⟨n2, .r16, [.wl, .ix]⟩,
      ⟨n3, .wh, [.wh]⟩] : List Line).flatMap (expandLine [cf.sh.getD 0 0]) =
      [(n0 ++ "", .kr, cf.sh.getD 0 0, [.rm, .rd]), (n1 ++ "", .kfd, cf.sh.getD 0 0, [.fm, .fd]),
        (n2, .r16, 0, [.wl, .ix]), (n3, .wh, 0, [.wh])] := rfl
  rw [hx] at hM
  obtain ⟨k0, r0, h0, hM0, rfl⟩ := L5.mapM_cons_ok hM
  obtain ⟨k1, r1, h1, hM1, rfl⟩ := L5.mapM_cons_ok hM0
  obtain ⟨k2, r2, h2, hM2, rfl⟩ := L5.mapM_cons_ok hM1
  obtain ⟨k3, r3, h3, hM3, rfl⟩ := L5.mapM_cons_ok hM2
  have hr : r3 = [] := by
    rw [List.mapM_nil] at hM3
    exact (Except.ok.inj hM3).symm
  subst hr
  have hT : S.calls.toList =
      [{ k0 with call := { k0.call with iota := io 0 } }, { k1 with call := { k1.call with iota := io 1 } },
        { k2 with call := { k2.call with iota := io 2 } },
        { k3 with call := { k3.call with iota := io 3 } }] := by
    rw [eS]
    show (A.calls.mapIdx _).toList = _
    rw [Array.toList_mapIdx, hc]
    simp [List.mapIdx_cons]
  have c1 : callAt S 1 = { k1 with call := { k1.call with iota := io 1 } } := by
    rw [L5.callAt_of_list hT]; rfl
  obtain ⟨t0, tτ⟩ := layCall_kfd h1
  have hsh : k1.sh = cf.sh.getD 0 0 := (L5.layCall_parts h1).2.1
  obtain ⟨q1, q2, q3⟩ := shTests_parts (L5.forM_mem _ _ hTs _ List.mem_cons_self)
  have eT : S.Tt = A.Tt := by rw [eS]
  have eu : S.u0 = A.Tt.size := by rw [Sh.u0, eT]
  have ecf : S.cf = cf := Sh.cfg
  refine ⟨by rw [Fo.sh, ecf], NA.Sm, hu, ?_, ?_⟩
  · rw [c1]
    show Call.tauAt { k1.call with iota := io 1 } k1.call.t0 = fOfNat (S.u0 * 2 ^ k1.sh + 2 ^ 32 - 2 ^ k1.sh)
    rw [eu, hsh]
    exact pad_row q1 (by rw [← eu]; exact hu) q2 q3 { k1.call with iota := io 1 } t0 tτ
  · intro pc hpc
    rw [Fo.p1] at hpc
    rcases List.mem_append.1 hpc with hm | hm
    · obtain ⟨b, _, rfl⟩ := List.mem_map.1 hm
      exact .inl rfl
    · obtain ⟨b, _, rfl⟩ := List.mem_map.1 hm
      exact .inr rfl

end K5Law
