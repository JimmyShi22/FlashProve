-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
K3PadEqAttention.lean

THE PUBLIC PART: PadEq AT THE TWELVE ATTENTION SHAPES IN SCOPE. Nothing on hiding.
PadEq S fs (Johnson/Road/Lane5KvAll.lean:46): the verifier's padding row of call c, as a number, is the library's padding value, c < 4.
A public decidable fact; elsewhere a #guard at one shape alone. HERE AS A THEOREM:
  pad_lt               the library's four padding values, at the letters made from the shape, lie in [0, the prime): first shift ≤ 12, u0 = 2307
  padEq_of_usual       PadEq S fs from shapeHid lid cf = ok (S, fs), CfRef cf, kFD = 16, S = 12, rx = 8, UsualCalls cf: tabsEq_of_usual's premises
  padEq_in_scope       PadEq (Hd.shapeA X g) (fsAt X g) at every g < 12, for public files in the goals' scope
  kvA_is_keyVec_in_scope   so (kvA_eq_keyVec_all): kvA = the library's keyVec AT EVERY INDEX, the padding included, at every reading of the cells
By Hd.IsLut's field pad (isLut_hid) and toNat_fOfNat: the verifier's word is the residue of a number that, as an integer, is the library's pad.
-/
import Johnson.Road.Lane5AttTabsEq
import Johnson.Road.Lane5KvAll
import Johnson.Goal.Meaning.AttForInScope
import Johnson.HonestTrace.FullPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5.PadAtAttention

open Inst.Model
open OnBytes.Ends OnBytes.Ends.A
open Attention (ACall Cfg shapeHid)

variable {lid : ℕ} {cf : Cfg} {S : Attention.Shape} {fs : Model.Forest.Shape}

/-- The library's padding values at the letters made from the shape are below the prime. -/
theorem pad_lt (hsh : S.cf.sh.getD 0 0 ≤ 12) (hu : S.u0 = 2307) :
    ∀ q : Fin 4, (AttSeg.lut (scl := sclOf S) (dimOf S) (tbOf S) q).pad < 18446744069414584321
  | ⟨0, _⟩ => by
    show (0 : ℤ) < _
    norm_num
  | ⟨1, _⟩ => by
    show cutC (S.cf.sh.getD 0 0) S.u0 - 2 ^ (S.cf.sh.getD 0 0) + 2 ^ 32 < _
    unfold cutC
    rw [hu]
    have h1 : (2 : ℤ) ^ (S.cf.sh.getD 0 0) ≤ 2 ^ 12 := pow_le_pow_right₀ (by norm_num) hsh
    have h2 : (0 : ℤ) < 2 ^ (S.cf.sh.getD 0 0) := by positivity
    generalize (2 : ℤ) ^ (S.cf.sh.getD 0 0) = a at h1 h2 ⊢
    push_cast
    norm_num at h1 ⊢
    omega
  | ⟨2, _⟩ => by
    show (0 : ℤ) < _
    norm_num
  | ⟨3, _⟩ => by
    show (0 : ℤ) < _
    norm_num

/-- **PadEq at the record that the verifier's own shapeHid returns**, under tabsEq_of_usual's premises on the configuration. -/
theorem padEq_of_usual (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) (U : UsualCalls cf) : PadEq S fs := by
  have Fo := four_of_hid h U
  have P := shaped_of_hid h
  have La := laidA_of_hid h U
  obtain ⟨hl, hf⟩ := isLut_hid h (fit_hid h hc.ldh U.one) hkF h12 h8
  obtain ⟨hu, -⟩ := exp_of_shaped P h12 h8
  have hsh : S.cf.sh.getD 0 0 ≤ 12 := by
    obtain ⟨A, -, -, hA, -, -⟩ := hid_calls h
    obtain ⟨-, -, -, hF, hz⟩ := calls_of_shape hA
    rw [P.cfg]
    exact sh_le_of_tests
      (forM_mem _ _ hF _ (by rw [shsOf_one hz U.one]; exact List.mem_singleton.2 rfl))
  intro q
  have mem : callAt S q.val ∈ S.calls.toList := by
    simpa using Array.mem_of_getElem? (La.isCall q)
  have L : Hd.IsLut (callAt S q.val).call (AttSeg.lut (scl := sclOf S) (dimOf S) (tbOf S) q) := by
    have e := hl _ mem
    rwa [kinds_of_four Fo q] at e
  have hcall : fs.calls[q.val]? = some (callAt S q.val).call := by
    rw [hf, Array.getElem?_map, La.isCall q]
    rfl
  obtain ⟨n, hn, hp⟩ := L.pad
  have hlt : n < 18446744069414584321 := by
    have := pad_lt hsh hu q
    omega
  have e : tauN fs q.val (t0N fs q.val) = ((callAt S q.val).call.tauAt (callAt S q.val).call.t0).toNat := by
    unfold tauN t0N
    rw [hcall]
    rfl
  rw [e, hn, toNat_fOfNat hlt, hp]

section Scope
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **PadEq AT THE TWELVE SHAPES**: for public files in the goals' scope, at every group. -/
theorem padEq_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    PadEq (Hd.shapeA X g) (OnBytes.HonestTrace.fsAt X g) := by
  obtain ⟨cf, hh, hc, hk, h12, h8, U⟩ := Meaning.Att.hid_in_scope hZ hR h hg
  exact padEq_of_usual (fs := OnBytes.HonestTrace.fsAt X g) hh hc hk h12 h8 U

/-- **So the key vectors kvA are the library's keyVec at every index, the padding included**, at every reading of the cells over the
protocol's field, at each of the twelve shapes. -/
theorem kvA_is_keyVec_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) (cell : NameA → Cb.Gl.E)
    (c : Fin 4) :
    kvA (Hd.shapeA X g) (OnBytes.HonestTrace.fsAt X g) cell c.val =
      AttSeg.keyVec (scl := sclOf (Hd.shapeA X g)) (dimOf (Hd.shapeA X g)) (tbOf (Hd.shapeA X g))
        (tC (Hd.shapeA X g) cell) c := by
  obtain ⟨cf, hh, hc, hk, h12, h8, U⟩ := Meaning.Att.hid_in_scope hZ hR h hg
  exact kvA_eq_keyVec_all (numsA_of_hid hh hc.ldh) (laidA_of_hid hh U)
    (inside_of_four (shaped_of_hid hh) (tests_of_hid hh).1 (four_of_hid hh U))
    (padEq_in_scope hZ hR h hg) cell c

end Scope

end OnBytes.Road.L5.PadAtAttention

#print axioms OnBytes.Road.L5.PadAtAttention.pad_lt
#print axioms OnBytes.Road.L5.PadAtAttention.padEq_of_usual
#print axioms OnBytes.Road.L5.PadAtAttention.padEq_in_scope
#print axioms OnBytes.Road.L5.PadAtAttention.kvA_is_keyVec_in_scope
