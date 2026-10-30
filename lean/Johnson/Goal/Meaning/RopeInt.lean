-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RopeInt.lean: the verifier's rotary numbers are the library's tables C and S,
as integers, at all public files in the goals' scope; and the test ropeOK says yes there.

  ropeC_in_scope: for every layer L below 48, position t below 1024 and pair i below 64:
    ropeC X.y.h X.layers.sc X.layers.rope L t i false = tbRef.C L t i, and the same for true and S.
  ropeOK_in_scope: ropeOK (Johnson/Road/Ends/AlgRope.lean:27) at X.layers, the library's reference
    sizes and tables, for every group below 12: the premise hrope of layerBridge_of_calls
    (Johnson/Road/Ends/AlgBridgeL5.lean:58).
-/
import Johnson.Goal.Meaning.RopeScope
import Johnson.Road.Ends.AlgRope

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Rope

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ropeC)
open OnBytes.Model.Verify (publicOf Public layerShape)
open Inst.Model (tbRef refC refS rotaryOff)
open Inst.Model.All (DF)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- The verifier's rotary numbers are the library's, as integers. -/
theorem ropeC_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {L t i : ℕ} (hL : L < 48) (ht : t < 1024)
    (hi : i < 64) :
    ropeC X.y.h X.layers.sc X.layers.rope L t i false = tbRef.C L t i ∧
      ropeC X.y.h X.layers.sc X.layers.rope L t i true = tbRef.S L t i := by
  have hh := (shape_of_public h).trans (P34.shape_in_scope hZ hR h)
  have hcs : X.y.h.cs = 12 := by
    rw [hh]
    rfl
  have hdh0 : X.y.h.dh = 128 := by
    rw [hh]
    rfl
  have hdh : X.y.h.dh / 2 = 64 := by rw [hdh0]
  have hlt : X.y.h.lt = 10 := by
    rw [hh]
    rfl
  have fl : X.layers.sc.klRp L = if L % 4 = 3 then 0 else 1 := flags_in_scope hZ hR h ⟨L, hL⟩
  by_cases hp : L % 4 = 3
  · have h0 : X.layers.sc.klRp L = 0 := by rw [fl, if_pos hp]
    have off : rotaryOff L := hp
    rw [ropeC_off h0, ropeC_off h0, hcs]
    exact ⟨(if_pos off).symm, (if_pos off).symm⟩
  · have h0 : X.layers.sc.klRp L ≠ 0 := by
      rw [fl, if_neg hp]
      decide
    have on : ¬ rotaryOff L := hp
    obtain ⟨w1, w2⟩ := table_words ht hi
    obtain ⟨d1, d2⟩ := data_le ht hi
    rw [ropeC_on h0, ropeC_on h0, rope_in_scope hZ hR h, hdh, hlt]
    have e0 : (if false = true then 2 ^ 10 * 64 else 0) + t * 64 + i = t * 64 + i := by simp
    have e3 : (if true = true then 2 ^ 10 * 64 else 0) + t * 64 + i = (1024 + t) * 64 + i := by
      rw [if_pos rfl]
      omega
    rw [e0, e3, w1, w2]
    have c1 := clamp_back d1
    have c2 := clamp_back d2
    refine ⟨?_, ?_⟩
    · show _ = refC L t i
      unfold refC
      rw [if_neg on]
      omega
    · show _ = refS L t i
      unfold refS
      rw [if_neg on]
      omega

/-- The test on the rotary tables says yes, for every group. -/
theorem ropeOK_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    Alg.ropeOK X.layers DF tbRef (g * X.y.Lam) = true := by
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.public_of_core h A
  have hLam : X.y.Lam = 4 := by
    rw [(laid_of_layout B.lay B.switches.p3).2.Lam, shape_of_public h,
      P34.shape_in_scope hZ hR h]
    rfl
  unfold Alg.ropeOK
  rw [List.all_eq_true]
  intro l hl
  rw [List.all_eq_true]
  intro t ht
  rw [List.all_eq_true]
  intro i hi
  have hl' : l < 4 := List.mem_range.mp hl
  have ht' : t < 1024 := List.mem_range.mp ht
  have hi' : i < 64 := List.mem_range.mp hi
  obtain ⟨a, b⟩ := ropeC_in_scope hZ hR h (L := g * X.y.Lam + l) (by rw [hLam]; omega) ht' hi'
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨a.symm, b.symm⟩

#print axioms ropeC_in_scope
#print axioms ropeOK_in_scope

end Meaning.Rope
