-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RopeFlags.lean: two public facts on the rotary step at all public files in the
goals' scope.

  flags_in_scope. Whether a layer has the rotary step the verifier takes from the scale file (the
    last word of the layer's record, Scales.klRp), the library from a fixed pattern (rotaryOff:
    every fourth layer has none). The scale file is free in the goals' scope, but the goals' reader
    refuses flags that are not the pattern (KLFile.rpRef in ofKL, Inst/Model/ProgTests.lean:238,
    :263).
  rope_in_scope. The rotary table that publicOf hands on is ropeTable at the stored example's four
    numbers.
  clamp_back: a word that does not pass 8192 comes back from the library's clamp.
-/
import Johnson.Goal.Meaning.Pub34Scope
import Johnson.Flat.ScalesSame
import Johnson.Road.FormsKeysLawP

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

/-! ## The flags -/

/-- THE FLAGS: at all public files in the goals' scope the scale file's rotary flags, as the
verifier reads them, are the library's pattern. -/
theorem flags_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (L : Fin 48) :
    X.layers.sc.klRp L.val = if L.val % 4 = 3 then 0 else 1 := by
  obtain ⟨P, f, hP, hf, ho⟩ := OnBytes.Flat.settingsAny_parts (OnBytes.Flat.settingsAtRef_eq hR)
  have rp : f.rpRef := by
    unfold Inst.Model.ofKL at ho
    split at ho
    · assumption
    · cases ho
  have eP' : P = X.P := Except.ok.inj (hP.symm.trans (Hd.scan_of_public h))
  subst eP'
  obtain ⟨g1, -⟩ := VerifiableInference.OnPublicFiles.Flat.klFileOf_fields hf
  have A := Hd.core_of_scope hZ hR h
  have hL : X.P.h.L = 48 := A.num 2
  have hr := Hd.scales_of_public h
  rw [shape_of_public h] at hr
  have hsc := reader_record hr
  rw [if_pos (Hd.public_of_core h A).p4] at hsc
  have y := rp L
  rw [g1 L 12 (by rw [hL]; exact L.isLt), VerifiableInference.OnPublicFiles.Flat.word_same] at y
  rw [hsc]
  show (fileWords Z.KL).getD (13 * L.val + 13 - 1) 0 = _
  exact y

/-- A stored word that does not pass 8192 comes back from the clamp. -/
theorem clamp_back {w : ℕ} (h : w ≤ 8192) :
    (w : ℤ) = Inst.Model.clamp 4096 ((w : ℤ) - 4096) + 4096 := by
  unfold Inst.Model.clamp
  have h' : (w : ℤ) ≤ 8192 := by exact_mod_cast h
  have h0 : (0 : ℤ) ≤ w := Int.natCast_nonneg w
  rw [max_eq_left (by omega), min_eq_left (by omega)]
  omega

/-- At all public files in the goals' scope the rotary table that publicOf hands on is the table at
the stored example's numbers. -/
theorem rope_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : X.layers.rope = ropeTable 12 500000 128 10 := by
  have hr := (P34.more_of_public h).2.2.1
  rw [shape_of_public h, P34.shape_in_scope hZ hR h] at hr
  unfold ropeOf at hr
  obtain ⟨-, hr⟩ := ok_of_refuse hr
  exact (Except.ok.inj hr).symm

#print axioms flags_in_scope
#print axioms rope_in_scope

end Meaning.Rope
