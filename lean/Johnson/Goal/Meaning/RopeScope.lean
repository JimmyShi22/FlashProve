-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RopeScope.lean: the field R of the record Pub34 (RopeFits,
Johnson/Road/FormsKeysQK.lean:616) at all public files in the goals' scope.

RopeFits says: the rotary numbers that the verifier reads for a layer, at every position and every
pair of channels, read as the library's tables C and S at that layer. It has two halves.
  THE FLAGS. Whether a layer has the rotary step the verifier takes from the scale file (the last
    word of the layer's record, Scales.klRp), the library from a fixed pattern (rotaryOff: every
    fourth layer has none). The scale file is free in the goals' scope, but the goals' reader
    refuses flags that are not the pattern (KLFile.rpRef in ofKL, Inst/Model/ProgTests.lean:238).
    flags_in_scope (Johnson/Goal/Meaning/RopeFlags.lean).
  THE WORDS. The verifier computes its table in whole numbers (ropeTable); the library's refC and
    refS read stored words (Data.cos, Data.sin). table_words joins the bridge table_spec
    (Johnson/Meaning/RopeSpec.lean) with the kernel's 64 evaluations (row_eq,
    Johnson/Meaning/RopeWords.lean).
Main theorems: table_words, data_le, ropeFits_in_scope.
Asked beside the three facts on the files: Numerals ρ; that the environment has X's layout, scales
and rotary table; that the group's number is below 12.
-/
import Johnson.Goal.Meaning.RopeFlags
import Johnson.Meaning.RopeSpec
import Johnson.Meaning.RopeWords
import Johnson.Road.FormsKeysQK

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Rope

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv ropeTable ropeOf fxOne)
open OnBytes.Model.Verify (publicOf Public layerShape)
open Inst.Model (dec tbRef refC refS rotaryOff)
open Inst.Model.All (DF)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-! ## The words -/

/-- THE WORDS: the verifier's rotary table at the stored example's numbers holds the library's
stored words. -/
theorem table_words {t i : ℕ} (ht : t < 1024) (hi : i < 64) :
    (ropeTable 12 500000 128 10).getD (t * 64 + i) 0 = dec Inst.Model.Data.cos 14 (64 * t + i) ∧
    (ropeTable 12 500000 128 10).getD ((1024 + t) * 64 + i) 0 =
      dec Inst.Model.Data.sin 14 (64 * t + i) := by
  have y := table_spec 12 500000 128 10 (t := t) (i := i) ht hi
  have e1 : (2 : ℕ) ^ 10 = 1024 := rfl
  have e2 : 128 / 2 = 64 := rfl
  rw [e1, e2, pairList_get 12 1024 (uOf 500000 64) 64 fxOne i hi, row_eq hi] at y
  have d : (dataRow i).getD t (0, 0) =
      (dec Inst.Model.Data.cos 14 (64 * t + i), dec Inst.Model.Data.sin 14 (64 * t + i)) := by
    unfold dataRow
    simp [List.getD_eq_getElem?_getD, ht]
  rw [d] at y
  exact y

/-- No stored word passes 8192. -/
theorem data_le {t i : ℕ} (ht : t < 1024) (hi : i < 64) :
    dec Inst.Model.Data.cos 14 (64 * t + i) ≤ 8192 ∧
      dec Inst.Model.Data.sin 14 (64 * t + i) ≤ 8192 := by
  have h2 := List.all_eq_true.mp (row_small hi) _
    (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  simpa using h2

/-- R: RopeFits at all public files in the goals' scope, at the library's reference tables, for
every layer of every group. -/
theorem ropeFits_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ)
    (c : ClaimEnv) (hy : c.v.y = X.y) (hsc : c.v.sc = X.layers.sc) (hrp : c.rope = X.layers.rope)
    (hg : c.v.g < 12) :
    ∀ lam, lam < c.v.y.Lam → RopeFits ρ c DF tbRef (c.v.g * c.v.y.Lam) lam := by
  intro lam hlam
  have hh : c.v.y.h = _ := (congrArg (·.h) hy).trans
    ((shape_of_public h).trans (P34.shape_in_scope hZ hR h))
  have hcs : c.v.y.h.cs = 12 := by
    rw [hh]
    rfl
  have hdh0 : c.v.y.h.dh = 128 := by
    rw [hh]
    rfl
  have hdh : c.v.y.h.dh / 2 = 64 := by rw [hdh0]
  have hlt : c.v.y.h.lt = 10 := by
    rw [hh]
    rfl
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.public_of_core h A
  have hLam : c.v.y.Lam = 4 := by
    rw [hy, (laid_of_layout B.lay B.switches.p3).2.Lam, shape_of_public h,
      P34.shape_in_scope hZ hR h]
    rfl
  rw [hLam] at hlam
  have hl : c.v.lay lam = c.v.g * c.v.y.Lam + lam := rfl
  have hl48 : c.v.g * c.v.y.Lam + lam < 48 := by
    rw [hLam]
    omega
  have fl := flags_in_scope hZ hR h ⟨c.v.g * c.v.y.Lam + lam, hl48⟩
  rw [← hsc] at fl
  have fl' : c.v.sc.klRp (c.v.lay lam) =
      if (c.v.g * c.v.y.Lam + lam) % 4 = 3 then 0 else 1 := fl
  refine ropeFits_of_words hρ c DF tbRef _ lam (fun h0 t i _ _ => ?_) (fun h0 t i ht hi => ?_)
  · have off : rotaryOff (c.v.g * c.v.y.Lam + lam) := by
      by_contra hn
      have hn' : ¬ (c.v.g * c.v.y.Lam + lam) % 4 = 3 := hn
      rw [fl', if_neg hn'] at h0
      cases h0
    rw [hcs]
    exact ⟨if_pos off, if_pos off⟩
  · have on : ¬ rotaryOff (c.v.g * c.v.y.Lam + lam) := by
      intro hn
      have hn' : (c.v.g * c.v.y.Lam + lam) % 4 = 3 := hn
      rw [fl', if_pos hn'] at h0
      exact h0 rfl
    have ht' : t < 1024 := ht
    rw [hdh] at hi
    obtain ⟨w1, w2⟩ := table_words ht' hi
    obtain ⟨d1, d2⟩ := data_le ht' hi
    rw [hrp, rope_in_scope hZ hR h, hdh, hlt]
    have e3 : 2 ^ 10 * 64 + t * 64 + i = (1024 + t) * 64 + i := by omega
    rw [e3, w1, w2]
    exact ⟨(clamp_back d1).trans (by
        show _ = refC _ t i + 4096
        unfold refC
        rw [if_neg on]),
      (clamp_back d2).trans (by
        show _ = refS _ t i + 4096
        unfold refS
        rw [if_neg on])⟩

#print axioms table_words
#print axioms data_le
#print axioms ropeFits_in_scope

end Meaning.Rope
