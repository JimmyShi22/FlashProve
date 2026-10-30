-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/ScopeCore.lean: at all public files in the goals' scope, the 41 numbers of the
parameter file that the way to "true under its policy" asks are the reference's.

`VerifierAndGoals.InScope Z` (Ladder.lean) says that the parameter file is the stored full-size example's,
byte for byte, but for eight free numbers. `Hd.PublicCore` (Johnson/Meaning/PublicCore.lean) speaks
of the scan of a parameter file: 41 numbers and two switches. This file joins the two, for all
values of the eight free numbers. No test is added to a verifier, and nothing is evaluated at
particular free numbers.

How. 40 of the 41 numbers are values of fixed lines from prof to F: `Lines.value_fixed`
(Johnson/Goal/Meaning/ScopeLines.lean) gives them off the bytes. The 41st, the number of limbs (the
line xl), and the two switches gcl and rcl are optional lines, which that theorem does not cover:
they come from the test that the goals' reader makes on the scanned file (`otherLinesHeld`,
Johnson/Flat/SettingsRead.lean).

Main theorems:
  `core_of_stored`: where the scan returns on `policyFile v` and the reader's test holds.
  `scan_of_public`: the field P of what `publicOf` returns is the scan of the parameter file.
  `core_of_scope`: InScope Z, readFiles Z = ok pp, publicOf Z.pol Z.KL lay = ok X give
    `Hd.PublicCore X.P`.
  `layers_of_scope`: so the file has 48 layers.

What is not claimed. That `publicOf` or the reader returns at any file. Nothing on the layout file
or the scale file. The program does not import this file.
-/
import Johnson.Meaning.PublicCore
import Johnson.Goal.Meaning.ScopeLines
import Ladder

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (polScan PolScan hdrOf)
open OnBytes.Flat (otherLinesHeld otherLinesHeld_all otherLinesOf settingsAtRef_held)
open VerifierAndGoals (FreeLines policyFile)

/-- **The 41 numbers and the two switches, at the stored example's parameter file with any values of
the eight free numbers.** -/
theorem core_of_stored {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P)
    (hh : otherLinesHeld P = true) : PublicCore P := by
  have V : ∀ (n : String) (k : ℕ), (n, k) ∈ VerifierAndGoals.Lines.fixedValues → P.value n = k :=
    fun n k hp => VerifierAndGoals.Lines.value_fixed h hp
  have a := otherLinesHeld_all hh
  have xl : P.xl.toNat = 1 := a ("xl", P.xl.toNat, 1) (by simp [otherLinesOf])
  have gcl : P.gcl.toNat = 1 := a ("gcl", P.gcl.toNat, 1) (by simp [otherLinesOf])
  have rcl : P.rcl.toNat = 1 := a ("rcl", P.rcl.toNat, 1) (by simp [otherLinesOf])
  have xl' : P.xl = true := by cases hx : P.xl <;> simp [hx] at xl ⊢
  have gcl' : P.gcl = true := by cases hx : P.gcl <;> simp [hx] at gcl ⊢
  have rcl' : P.rcl = true := by cases hx : P.rcl <;> simp [hx] at rcl ⊢
  refine ⟨?_, gcl', rcl'⟩
  have hH := Model.ConfigReaders.polScan_h h
  unfold coreOf PolScan.XL
  rw [hH, xl']
  simp only [hdrOf]
  rw [V "prof" 20 (by decide), V "lt" 10 (by decide), V "L" 48 (by decide), V "ll" 2 (by decide),
    V "d" 5120 (by decide), V "H" 40 (by decide), V "G" 8 (by decide), V "dh" 128 (by decide),
    V "f" 16384 (by decide), V "fe" 8192 (by decide), V "NE" 128 (by decide),
    V "V" 202048 (by decide), V "la" 16 (by decide), V "lmaf" 16 (by decide),
    V "NAf" 3 (by decide), V "lmad" 15 (by decide), V "NAd" 1 (by decide),
    V "lmar" 13 (by decide), V "lmq" 16 (by decide), V "lmx" 16 (by decide),
    V "lmhf" 16 (by decide), V "NHf" 4 (by decide), V "lmhd" 14 (by decide),
    V "lmhr" 13 (by decide), V "hq" 2 (by decide), V "hv" 1 (by decide), V "ho" 1 (by decide),
    V "hgD" 1 (by decide), V "huD" 1 (by decide), V "hdD" 1 (by decide), V "hr" 1 (by decide),
    V "sh" 8 (by decide), V "sT" 4 (by decide), V "lB" 6 (by decide), V "S" 12 (by decide),
    V "rx" 8 (by decide), V "lmS" 16 (by decide), V "lmh" 13 (by decide), V "lmo" 16 (by decide),
    V "NAs" 1 (by decide)]
  rfl

/-- The field P of what the verifier's `publicOf` returns is the strict scan of the parameter file.
-/
theorem scan_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) : polScan pol = .ok X.P := by
  obtain ⟨P, y, hpl, eP, -⟩ := public_parts h
  unfold Model.Verify.polLayout at hpl
  obtain ⟨P0, hP, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨y0, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  cases hpl
  rw [eP]
  exact hP

/-- In scope, the parameter file is the stored example's at the free numbers that the reader read.
-/
theorem policy_of_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) : Z.pol = policyFile (VerifierAndGoals.freeLinesOf pp) := by
  unfold VerifierAndGoals.InScope at hZ
  rw [hR] at hZ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hZ
  exact hZ.2.1

/-- **At all public files in the goals' scope the 41 numbers are the reference's**, in what the
verifier's own function returns on them, with or without the layout file. -/
theorem core_of_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Model.Verify.publicOf Z.pol Z.KL lay = .ok X) : PublicCore X.P := by
  obtain ⟨S, hS, hh⟩ := settingsAtRef_held hR
  have hX := scan_of_public h
  have e : S = X.P := Except.ok.inj (hS.symm.trans hX)
  rw [policy_of_scope hZ hR] at hX
  exact core_of_stored hX (e ▸ hh)

/-- So the parameter file has 48 layers. -/
theorem layers_of_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Model.Verify.publicOf Z.pol Z.KL lay = .ok X) : X.P.h.L = 48 :=
  (core_of_scope hZ hR h).num 2

#print axioms core_of_stored
#print axioms core_of_scope
#print axioms layers_of_scope

end OnBytes.Road.Hd
