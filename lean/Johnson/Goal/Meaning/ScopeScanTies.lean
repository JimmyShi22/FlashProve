-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/ScopeScanTies.lean: what the closed form of the scan of `VerifierAndGoals.policyFile v`
(Johnson/Goal/Meaning/ScopeScan.lean) pays in other files' letters.

Main theorems, each under "the strict scan returns on `policyFile v`", for all v:
  `scan_unique`: two scans at two values of the free numbers differ in the values and the record
    alone.
  `scan_withPol`: where the scan returns P on `policyFile v` and P' on the same file with other
    numbers C, theta, cap: P' = `P.withPol C theta cap` (OnBytes/Tie/PlanAtPolicy.lean). It serves
    the hypothesis hs of `dryProof_plannedAt_withPol` (OnBytes/Tie/PlanAtPolicyDry.lean) and
    `dry_bigReq_plannedAt_withPol` (Johnson/Flat/DryAtPolicy.lean), "the strict scan of the second
    file is p.X.P.withPol C theta cap". Still to be paid there: that the two files are `policyFile`
    at such numbers, that the second scan returns, and that p.X.P is the first file's scan.
  `core_of_scan`: `Hd.PublicCore` (Johnson/Meaning/PublicCore.lean) off the bytes alone, without the
    test that the goals' reader makes on the scanned file.
  `scan_of_scope`, `calls_of_scope`: at all public files in the goals' scope, the scan in what
    `publicOf` returns is the closed form; so its call lines are the stored example's.

What is not claimed. That the scan returns. The verifier program does not import this file.
-/
import Johnson.Goal.Meaning.ScopeScan
import Johnson.Goal.Meaning.ScopeCore
import OnBytes.Tie.PlanAtPolicy

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifierAndGoals.Lines

open OnBytes OnBytes.Model

/-- Two scans at two values of the free numbers: each is the closed form at one frame. -/
theorem scan_unique {v v' : FreeLines} {P P' : PolScan} (h : polScan (policyFile v) = .ok P)
    (h' : polScan (policyFile v') = .ok P') : P' = scanAt P.frame v' := by
  rw [frame_eq h]
  exact scan_closed h'

/-- Pairs under other names than C, theta, cap stay. -/
theorem valuesWithPol_keep {l : List (String × Nat)} (C theta cap : Nat)
    (h : l.all (fun x => x.1 != "C" && x.1 != "theta" && x.1 != "cap") = true) :
    Tie.valuesWithPol l C theta cap = l := by
  unfold Tie.valuesWithPol
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  have a := List.all_eq_true.1 h x hx
  simp only [Bool.and_eq_true, bne_iff_ne] at a
  rw [if_neg a.1.1, if_neg a.1.2, if_neg a.2]
  rfl

/-- The list of values at other numbers C, theta, cap. -/
theorem valuesAt_withPol (v : FreeLines) (C theta cap : Nat) :
    valuesAt { v with C := C, theta := theta, cap := cap } =
      Tie.valuesWithPol (valuesAt v) C theta cap := by
  have m : ∀ a b : List (String × Nat), Tie.valuesWithPol (a ++ b) C theta cap =
      Tie.valuesWithPol a C theta cap ++ Tie.valuesWithPol b C theta cap :=
    fun a b => List.map_append
  unfold valuesAt
  rw [m, m, m, m, m, m, valuesWithPol_keep C theta cap (l := valuesA1) (by decide +kernel),
    valuesWithPol_keep C theta cap (l := valuesA2) (by decide +kernel),
    valuesWithPol_keep C theta cap (l := valuesA3) (by decide +kernel),
    valuesWithPol_keep C theta cap (l := valuesB) (by decide +kernel),
    valuesWithPol_keep C theta cap (l := (freeValues v).take 4) rfl,
    valuesWithPol_keep C theta cap (l := ((freeValues v).drop 4).take 4) rfl]
  rfl

/-- The closed form at other numbers C, theta, cap. -/
theorem scanAt_withPol (fr : Params.Lines) (v : FreeLines) (C theta cap : Nat) :
    scanAt fr { v with C := C, theta := theta, cap := cap } =
      (scanAt fr v).withPol C theta cap := by
  have hv := valuesAt_withPol v C theta cap
  have nd : ((valuesAt { v with C := C, theta := theta, cap := cap }).map Prod.fst).Nodup := by
    rw [valuesAt_names]
    exact ConfigReaders.valueNames_nodup 4
  have mem : ∀ p ∈ freeValues { v with C := C, theta := theta, cap := cap },
      p ∈ (freeValues { v with C := C, theta := theta, cap := cap }).drop 8 →
      ((valuesAt { v with C := C, theta := theta, cap := cap }).lookup p.1).getD 0 = p.2 :=
    fun p _ hp => by
      have hm : p ∈ valuesAt { v with C := C, theta := theta, cap := cap } := by
        unfold valuesAt
        simp only [List.mem_append]
        exact .inl (.inr hp)
      rw [lookup_of_mem nd p hm]
      rfl
  have hh := hdrOf_pol (g := fun n => ((valuesAt v).lookup n).getD 0)
    (g' := fun n => ((valuesAt { v with C := C, theta := theta, cap := cap }).lookup n).getD 0)
    fun n h1 h2 h3 => by
      have a := Tie.value_withPol (scanAt fr v) C theta cap n h1 h2 h3
      show ((valuesAt { v with C := C, theta := theta, cap := cap }).lookup n).getD 0 = _
      rw [hv]
      exact a
  have cC := mem ("C", C) (by simp [freeValues]) (by simp [freeValues])
  have cT := mem ("theta", theta) (by simp [freeValues]) (by simp [freeValues])
  have cK := mem ("cap", cap) (by simp [freeValues]) (by simp [freeValues])
  dsimp only at hh cC cT cK
  rw [cC, cT, cK] at hh
  unfold scanAt PolScan.withPol Hdr.withPol
  dsimp only
  rw [hh, hv]

/-- **The scan at other numbers C, theta, cap is `PolScan.withPol` of the scan.** -/
theorem scan_withPol {v : FreeLines} {C theta cap : Nat} {P P' : PolScan}
    (h : polScan (policyFile v) = .ok P)
    (h' : polScan (policyFile { v with C := C, theta := theta, cap := cap }) = .ok P') :
    P' = P.withPol C theta cap := by
  rw [scan_unique h h', scanAt_withPol, ← scan_eq h]

end VerifierAndGoals.Lines

namespace OnBytes.Road.Hd

open OnBytes.Model (polScan PolScan hdrOf)
open VerifierAndGoals (FreeLines policyFile)

/-- **The 41 numbers and the two switches, off the bytes alone.** -/
theorem core_of_scan {v : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P) :
    PublicCore P := by
  obtain ⟨-, -, -, -, -, -, -, -, rcl, gcl, xl, -⟩ := VerifierAndGoals.Lines.scan_rest h
  have V : ∀ (n : String) (k : ℕ), (n, k) ∈ VerifierAndGoals.Lines.fixedValues → P.value n = k :=
    fun n k hp => VerifierAndGoals.Lines.value_fixed h hp
  refine ⟨?_, gcl, rcl⟩
  have hH := Model.ConfigReaders.polScan_h h
  unfold coreOf PolScan.XL
  rw [hH, xl]
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

/-- **At all public files in the goals' scope: the scan in what the verifier's `publicOf` returns is
the closed form at the free numbers that the goals' reader read.** -/
theorem scan_of_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    X.P = VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef (VerifierAndGoals.freeLinesOf pp) := by
  have hX := scan_of_public h
  rw [policy_of_scope hZ hR] at hX
  exact VerifierAndGoals.Lines.scan_closed hX

/-- So its call lines are the stored example's. -/
theorem calls_of_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Model.Verify.publicOf Z.pol Z.KL lay = .ok X) :
    X.P.polCalls = VerifierAndGoals.Lines.callsRef ∧ X.P.polCallsA = VerifierAndGoals.Lines.callsARef ∧
      X.P.polCallsH = VerifierAndGoals.Lines.callsHRef := by
  rw [scan_of_scope hZ hR h]
  exact ⟨rfl, rfl, rfl⟩

end OnBytes.Road.Hd

#print axioms VerifierAndGoals.Lines.scan_unique
#print axioms VerifierAndGoals.Lines.scan_withPol
#print axioms OnBytes.Road.Hd.core_of_scan
#print axioms OnBytes.Road.Hd.scan_of_scope
#print axioms OnBytes.Road.Hd.calls_of_scope
