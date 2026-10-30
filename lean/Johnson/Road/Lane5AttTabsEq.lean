-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttTabsEq.lean

"TabsEq S fs" (Johnson/Road/Lane5KeysIff.lean: the verifier's tables of the four lookup calls of
an attention sub-proof are the library's table formulas at the letters made from the shape, sclOf
S, dimOf S and tbOf S, that is at the verifier's own exponentials: as many rows; row by row,
between integers; the pieces fit; the padding row is a row) as a theorem, at the record that the
verifier's own shapeHid returns. That these exponentials are the reference's is exp_of_hid
(Johnson/Road/Lane5AttHid.lean). With "InsideA" (no piece reaches behind the library's "used") it
makes keys_iff, the lookup's clause at attention both ways, free of tests.

"Hd.IsLut" (Johnson/Road/HeadTabs.lean) says of a row: the verifier's word is the residue of a
natural number that, as an integer, is the library's row. Between integers that is an equation only
where the library's row is below the field's prime.

* "toNat_fOfNat", "rowZ_of_isLut": a word of a number below the prime, read back.
* "lut_row_lt": every row of the four tables, at the letters made from the shape, is below the
  prime, under six premises on the shape: the first shift is at most 12; ldh = 7; u0 is the size of
  the table of exponentials; that size is above 0 and below 65,536; every exponential is at most
  4,096.
* "t0_lt_layCall", "t0_lt_shape", "t0_lt_hid": the padding row of a call is a row of its table.
* "tabsEq_of_luts": TabsEq from these.
* **"tabsEq_of_usual"**: TabsEq S fs from shapeHid lid cf = ok (S, fs), CfRef cf, kFD = 16, S = 12,
  rx = 8, UsualCalls cf.
* "inside_of_four", **"keys_iff_of_usual"**: InsideA; and (callsC S fs cell).InTables ↔ KeysC S cell
  under the same premises on the configuration.

Not claimed: all that Lane5KeysIff.lean and Lane5AttSeam.lean do not claim.
The key vectors in "InTables" are kvA (OnBytes/Tie/Pv/Lookup/Ends/A.lean), a term of this library
over the verifier's records, at the cells that addrA (Johnson/Road/Lane5AttDef.lean) places. The
verifier holds no key vector. That its key forms evaluate kvA is shown elsewhere under a premise
(rule, OnBytes/Tie/Pv/Lookup/Ends/AlgAW.lean); that addrA is the program's rule is shown nowhere.
"The verifier's own" is said here of shapeHid's record alone: sizes, pieces, tables.
-/
import Johnson.Road.Lane5AttSeam
import Johnson.Road.Lane5KeysIff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open OnBytes.Ends OnBytes.Ends.A
open Attention (ACall Cfg Shape Listed shape shapeHid layCall)

/-! ## 1. Words and integers -/

/-- A word of a number below the prime, read back. -/
theorem toNat_fOfNat {n : ℕ} (h : n < 18446744069414584321) : (Model.fOfNat n).toNat = n := by
  have h1 : n < 2 ^ 64 := by omega
  rw [← Hd.word_eq_fOfNat h, show n.toUInt64 = UInt64.ofNat n from rfl,
    UInt64.toNat_ofNat_of_lt' h1]

/-- A row of a call that has the library's table, between integers. -/
theorem rowZ_of_isLut {c : Model.Call} {T : Lut} (h : Hd.IsLut c T) {u : ℕ} (hu : u < T.rows)
    (hb : T.row u < 18446744069414584321) : (((c.tauAt u).toNat : ℕ) : ℤ) = T.row u := by
  obtain ⟨n, hn, hr⟩ := h.row u hu
  have hn' : n < 18446744069414584321 := by omega
  rw [hn, toNat_fOfNat hn', hr]

/-! ## 2. The library's rows are below the prime -/

theorem lut_row_lt {S : Shape} (hsh : S.cf.sh.getD 0 0 ≤ 12) (hl : S.cf.ldh = 7)
    (hu0 : S.u0 = S.Tt.size) (h0 : 0 < S.Tt.size) (hu : S.Tt.size < 65536)
    (hT : ∀ ι : ℕ, ι < S.Tt.size → S.Tt.getD ι 0 ≤ 4096) :
    ∀ (q : Fin 4) (u : ℕ), u < (AttSeg.lut (scl := sclOf S) (dimOf S) (tbOf S) q).rows →
      (AttSeg.lut (scl := sclOf S) (dimOf S) (tbOf S) q).row u < 18446744069414584321
  | ⟨0, _⟩, u, h => by
    have h' : u < 65536 := h
    show (tau1 (S.cf.sh.getD 0 0)).row u < _
    rw [← rowKR_eq]
    have := rowKR_lt (S.cf.sh.getD 0 0) h'
    omega
  | ⟨1, _⟩, u, h => by
    have h' : u < 65536 := h
    show (tau2 (S.cf.sh.getD 0 0) S.u0 (tbOf S)).row u < _
    rw [hu0, ← rowKFD_eq hsh (smOf_ref hl) h0 (fun _ _ => rfl) u]
    have := rowKFD_lt (Sm := smOf S.cf) hsh hu hT h'
    omega
  | ⟨2, _⟩, u, h => by
    have h' : u < 65536 := h
    show ((u : ℕ) : ℤ) < _
    omega
  | ⟨3, _⟩, u, h => by
    have h' : u < 65536 := h
    show tau4.row u < _
    rw [← rowWH_eq]
    have := rowWH_lt h'
    omega

/-! ## 3. The padding row -/

theorem t0_lt_layCall {cf : Cfg} {HA Sm : ℕ} {Tt : Array ℕ} {x : Listed} {k : ACall}
    (h : layCall cf HA Sm Tt x = Except.ok k) (hkF : cf.kFD = 16) (hu : Tt.size < 65536) :
    k.call.t0 < 2 ^ k.call.k := by
  obtain ⟨name, kind, sh, segs⟩ := x
  unfold Attention.layCall at h
  obtain ⟨-, h⟩ := refuse_ok h
  have e := Except.ok.inj h
  subst e
  cases kind with
  | kr => show 0 < 2 ^ 16; norm_num
  | wh => show 0 < 2 ^ 16; norm_num
  | r16 => show 0 < 2 ^ 16; norm_num
  | kfd =>
    show Tt.size < 2 ^ cf.kFD
    rw [hkF]
    exact hu

variable {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Model.Forest.Shape}

/-- The padding row of every call of the shape that shape returns is a row of its table. -/
theorem t0_lt_shape (h : shape cf = Except.ok S) (hkF : cf.kFD = 16) (hu : S.Tt.size < 65536) :
    ∀ k ∈ S.calls.toList, k.call.t0 < 2 ^ k.call.k := by
  obtain ⟨calls, hM, hc, -, -⟩ := calls_of_shape h
  intro k hk
  rw [hc] at hk
  obtain ⟨x, -, hx⟩ := mapM_mem _ _ _ hM k hk
  exact t0_lt_layCall hx hkF hu

/-- The same for the shape that shapeHid returns. -/
theorem t0_lt_hid (h : shapeHid lid cf = Except.ok (S, fs)) (hkF : cf.kFD = 16)
    (hu : S.Tt.size < 65536) : ∀ k ∈ S.calls.toList, k.call.t0 < 2 ^ k.call.k := by
  obtain ⟨A, io, kbA, hA, eS, -⟩ := hid_calls h
  subst eS
  have hu' : A.Tt.size < 65536 := hu
  intro k hk
  have hk' : k ∈ (A.calls.mapIdx fun q c =>
      ({ c with call := { c.call with iota := io q } } : ACall)).toList := hk
  rw [Array.toList_mapIdx, List.mem_mapIdx] at hk'
  obtain ⟨i, hi, rfl⟩ := hk'
  have e := t0_lt_shape hA hkF hu' _ (List.getElem_mem hi)
  exact e

/-! ## 4. TabsEq -/

/-- **The verifier's tables are the library's, from "each call has the library's table".** -/
theorem tabsEq_of_luts {cs : Fin 4 → ACall} (hS : ∀ q : Fin 4, S.calls[q.val]? = some (cs q))
    (hc : ∀ q : Fin 4, fs.calls[q.val]? = some (cs q).call)
    (L : ∀ q : Fin 4,
      Hd.IsLut (cs q).call (AttSeg.lut (scl := sclOf S) (dimOf S) (tbOf S) q))
    (lt : ∀ (q : Fin 4) (u : ℕ), u < (AttSeg.lut (scl := sclOf S) (dimOf S) (tbOf S) q).rows →
      (AttSeg.lut (scl := sclOf S) (dimOf S) (tbOf S) q).row u < 18446744069414584321)
    (room : ∀ q : Fin 4, (dimOf S).used q ≤ 2 ^ (cs q).call.n)
    (pad : ∀ q : Fin 4, (cs q).call.t0 < 2 ^ (cs q).call.k) : TabsEq S fs := by
  have hk : ∀ c : Fin 4, kN fs c.val = (cs c).call.k := by
    intro c
    unfold kN
    rw [hc c]
    rfl
  refine ⟨fun c => ?_, fun c u hu => ?_, fun c => ?_, fun c => ?_⟩
  · rw [hk c]
    exact (L c).rows.symm
  · have ht : tauN fs c.val u = ((cs c).call.tauAt u).toNat := by
      unfold tauN
      rw [hc c]
      rfl
    rw [hk c, (L c).rows] at hu
    rw [ht]
    exact rowZ_of_isLut (L c) hu (lt c u hu)
  · have e : S.calls.getD c.val default = cs c := by
      rw [Array.getD_eq_getD_getElem?, hS c]
      rfl
    rw [e]
    exact room c
  · have e : t0N fs c.val = (cs c).call.t0 := by
      unfold t0N
      rw [hc c]
      rfl
    rw [hk c, e]
    exact pad c

/-- **TabsEq, with nothing left on the shape.** -/
theorem tabsEq_of_usual (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) (U : UsualCalls cf) : TabsEq S fs := by
  have Fo := four_of_hid h U
  have P := shaped_of_hid h
  have La := laidA_of_hid h U
  obtain ⟨hl, hf⟩ := isLut_hid h (fit_hid h hc.ldh U.one) hkF h12 h8
  obtain ⟨hu, hE⟩ := exp_of_shaped P h12 h8
  have hsz : S.Tt.size = 2307 := by rw [← P.u0]; exact hu
  have hT : ∀ ι : ℕ, ι < S.Tt.size → S.Tt.getD ι 0 ≤ 4096 := by
    intro ι hι
    have hι' : ι < 2307 := hsz ▸ hι
    have b : tbRef.Exp (ι : ℕ) ≤ 2 ^ 12 := (tbRef_ok.2.2.2.1 ι hι').2
    rw [← hE ι (by rw [hu]; exact hι')] at b
    have b' : ((S.Tt.getD ι 0 : ℕ) : ℤ) ≤ ((4096 : ℕ) : ℤ) := by
      refine le_trans b ?_
      norm_num
    exact Int.ofNat_le.1 b'
  have hsh : S.cf.sh.getD 0 0 ≤ 12 := by
    obtain ⟨A, -, -, hA, -, -⟩ := hid_calls h
    obtain ⟨-, -, -, hF, hz⟩ := calls_of_shape hA
    rw [P.cfg]
    exact sh_le_of_tests
      (forM_mem _ _ hF _ (by rw [shsOf_one hz U.one]; exact List.mem_singleton.2 rfl))
  have mem : ∀ q : Fin 4, callAt S q.val ∈ S.calls.toList := by
    intro q
    simpa using Array.mem_of_getElem? (La.isCall q)
  refine tabsEq_of_luts La.isCall ?_ ?_
    (lut_row_lt hsh (by rw [P.cfg]; exact hc.ldh) P.u0 (by omega) (by omega) hT)
    (room_of_four P (tests_of_hid h).1 Fo) (fun q => t0_lt_hid h hkF (by omega) _ (mem q))
  · intro q
    rw [hf, Array.getElem?_map, La.isCall q]
    rfl
  · intro q
    have e := hl _ (mem q)
    rwa [kinds_of_four Fo q] at e

/-! ## 5. No piece reaches behind "used"; the lookup's clause both ways -/

theorem famAt_end {s : Attention.Seg} {HA c base n : ℕ} {p : Attention.Piece}
    (h : p ∈ famAt s HA c base n) : p.off + 2 ^ p.b ≤ base + n * 2 ^ c := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
  have hb' := List.mem_range.1 hb
  show base + b * 2 ^ c + 2 ^ c ≤ base + n * 2 ^ c
  have : (b + 1) * 2 ^ c ≤ n * 2 ^ c := Nat.mul_le_mul_right _ hb'
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem inside_of_four (P : Shaped cf S) (hlt : cf.lB + 2 ≤ cf.lt) (Fo : FourCalls cf S) :
    InsideA S fun q : Fin 4 => callAt S q.val := by
  obtain ⟨hnb, hM, hD, hW, hX, h4⟩ := dim_nums P hlt
  intro q
  match q with
  | ⟨0, _⟩ =>
    intro p hp
    show p.off + 2 ^ p.b ≤ (dimOf S).nb * 2 ^ (dimOf S).lM + (dimOf S).nb * 2 ^ (dimOf S).lD
    have hp' : p ∈ (callAt S 0).pcs.toList := hp
    rw [hnb, hM, hD]
    rw [Fo.p0] at hp'
    rcases List.mem_append.1 hp' with h | h
    · have := famAt_end h
      omega
    · exact famAt_end h
  | ⟨1, _⟩ =>
    intro p hp
    show p.off + 2 ^ p.b ≤ (dimOf S).nb * 2 ^ (dimOf S).lM + (dimOf S).nb * 2 ^ (dimOf S).lD
    have hp' : p ∈ (callAt S 1).pcs.toList := hp
    rw [hnb, hM, hD]
    rw [Fo.p1] at hp'
    rcases List.mem_append.1 hp' with h | h
    · have := famAt_end h
      omega
    · exact famAt_end h
  | ⟨2, _⟩ =>
    intro p hp
    show p.off + 2 ^ p.b ≤ (dimOf S).nb * 2 ^ (dimOf S).lW + (dimOf S).nb * 2 ^ (dimOf S).lX
    have hp' : p ∈ (callAt S 2).pcs.toList := hp
    rw [hnb, hW, hX]
    rw [Fo.p2] at hp'
    rcases List.mem_append.1 hp' with h | h
    · have := famAt_end h
      omega
    · exact famAt_end h
  | ⟨3, _⟩ =>
    intro p hp
    show p.off + 2 ^ p.b ≤ (dimOf S).nb * 2 ^ (dimOf S).l4
    have hp' : p ∈ (callAt S 3).pcs.toList := hp
    rw [hnb, h4]
    rw [Fo.p3] at hp'
    have := famAt_end hp'
    omega

/-- **The lookup's clause at attention, both ways, from the verifier's own call.** -/
theorem keys_iff_of_usual (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) (U : UsualCalls cf)
    (cell : NameA → Cb.Gl.E) : (callsC S fs cell).InTables ↔ KeysC S cell :=
  keys_iff (numsA_of_hid h hc.ldh) (laidA_of_hid h U) (tabsEq_of_usual h hc hkF h12 h8 U)
    (inside_of_four (shaped_of_hid h) (tests_of_hid h).1 (four_of_hid h U)) cell

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.tabsEq_of_luts
#print axioms OnBytes.Road.L5.tabsEq_of_usual
#print axioms OnBytes.Road.L5.inside_of_four
#print axioms OnBytes.Road.L5.keys_iff_of_usual
