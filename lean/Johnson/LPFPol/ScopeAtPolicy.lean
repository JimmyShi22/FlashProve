-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/ScopeAtPolicy.lean: public files in the goals' scope stay in scope if the three
numbers C, theta, cap of the parameter file are replaced by others in an explicit range:
C < 2^32, theta ≤ C, cap ≤ 1024 and 2^8 ≤ theta.

Why. Johnson/Goal/Files/ScopeExample.lean shows of two sets of files that they are in scope
(`VerifierAndGoals.inScope_full`, `VerifierAndGoals.inScope_gap`), by the kernel's evaluation. A law that
speaks of "every policy in scope" says little unless one knows which policies these are.

Main names.
* `read_withPol`: where the goals' reader (`settingsAtRef`, Johnson/Flat/SettingsRead.lean) returns
  pp at `policyFile v` and KL, it returns pp with the policy (C, theta, cap) at
  `policyFile { v with C, theta, cap }` and KL, if C < 2^32, theta ≤ C and cap ≤ 1024.
* `inScope_withPol`: THE LAW. Premises: h0, the files `policyFile v`, lay, KL are in scope; h1 to
  h4, the range. Then the files `policyFile { v with C, theta, cap }`, lay, KL are in scope.
* `inScope_iff_range`: with h0, the second set is in scope exactly if the numbers are in the range.
* `scope_parts`: what being in scope gives at files whose parameter file is `policyFile v`. One
  direction.
* `policyFile_inj`: two values of the free numbers with one file, at which the scan returns, are
  one.
* `klFileOf_withPol`, `ofKL_withPol`, `lawful_withPol`, `otherLinesHeld_withPol`: the reader's
  steps.

Limits. That the first set is in scope is a premise. Which scale files and which values of the five
other free numbers are in scope is not said: Lean holds one scale file and one set of the five in
scope (Johnson/Goal/Files/ScopeExample.lean). The scale file, the layout file and the five
other free numbers are the same in both sets. Being in scope says nothing on a verifier or on any
proof. Nothing on soundness.

For proofs only; no program imports this file.


-/
import Johnson.LPFPol.ScanReturns
import Johnson.LPFPol.PublicInScope
import Johnson.Goal.Meaning.ScopeScanTies
import Johnson.Flat.SettingsRead
import Ladder

set_option autoImplicit false

namespace LPFPol

open OnBytes OnBytes.Model
open VerifierAndGoals (FreeLines policyFile freeLinesOf InScope readFiles)
open VerifierAndGoals.Lines
open OnBytes.Flat
open Inst.Model (ScalesAndPolicy AcceptancePolicy KLFile ofKL Lawful)

/-! ### the reader's steps -/

/-- The scale file's reader lays the header's three numbers through, and reads them nowhere else. -/
theorem klFileOf_withPol (h : Hdr) (C theta cap : Nat) (KL : ByteArray) :
    klFileOf (h.withPol C theta cap) KL =
      (klFileOf h KL).map fun f => { f with C := C, theta := theta, cap := cap } := by
  unfold klFileOf
  dsimp only
  show (if h.L ≤ 48 ∧ KL.size % 4 = 0 ∧
      ((Model.fileWords KL).map (·.toUInt32)).size = 13 * h.L + 3 * (h.L / 2) then _ else _) = _
  split <;> rfl

/-- So does `ofKL`. -/
theorem ofKL_withPol (f : KLFile) (C theta cap : Nat) :
    ofKL { f with C := C, theta := theta, cap := cap } =
      (ofKL f).map fun pp => { pp with pol := ⟨C, theta, cap⟩ } := by
  unfold ofKL
  by_cases r : f.rpRef
  · rw [if_pos r, if_pos (show KLFile.rpRef { f with C := C, theta := theta, cap := cap } from r)]
    rfl
  · rw [if_neg r, if_neg (show ¬ KLFile.rpRef { f with C := C, theta := theta, cap := cap } from r)]
    rfl

/-- Lawful settings stay lawful at a policy with C < 2^32, theta ≤ C and cap ≤ 1024. -/
theorem lawful_withPol {pp : ScalesAndPolicy} (h : Lawful pp) {C theta cap : Nat} (h1 : C < 2 ^ 32)
    (h2 : theta ≤ C) (h3 : cap ≤ 1024) : Lawful { pp with pol := ⟨C, theta, cap⟩ } :=
  ⟨⟨h.ff, h.sh, h.one, h.nf, ⟨h1, h2, h3⟩⟩, h.km⟩

/-- The test on the further model lines does not read the three numbers. -/
theorem otherLinesHeld_withPol (S : PolScan) (C theta cap : Nat) :
    otherLinesHeld (S.withPol C theta cap) = otherLinesHeld S := rfl

/-- **The reader at the second file.** -/
theorem read_withPol {v : FreeLines} {KL : ByteArray} {pp : ScalesAndPolicy}
    (hR : settingsAtRef (policyFile v) KL = .ok pp) {C theta cap : Nat} (h1 : C < 2 ^ 32)
    (h2 : theta ≤ C) (h3 : cap ≤ 1024) :
    settingsAtRef (policyFile { v with C := C, theta := theta, cap := cap }) KL =
      .ok { pp with pol := ⟨C, theta, cap⟩ } := by
  obtain ⟨S, hS, hh⟩ := settingsAtRef_held hR
  obtain ⟨S0, hS0, hk, hL⟩ := settingsAny_iff.1 (settingsAtRef_eq hR)
  obtain rfl : S0 = S := Except.ok.inj (hS0.symm.trans hS)
  obtain ⟨S', hS'⟩ := scan_returns_withPol hS h1 (Nat.lt_of_le_of_lt h2 h1)
    (Nat.lt_of_le_of_lt h3 (by decide))
  obtain rfl : S' = S0.withPol C theta cap := scan_withPol hS hS'
  refine settingsAtRef_of hS' (by rw [otherLinesHeld_withPol]; exact hh)
    (settingsAny_iff.2 ⟨_, hS', ?_, lawful_withPol hL h1 h2 h3⟩)
  show (klFileOf (S0.h.withPol C theta cap) KL).bind ofKL = _
  rw [klFileOf_withPol]
  cases hf : klFileOf S0.h KL with
  | none =>
    rw [hf] at hk
    cases hk
  | some f =>
    rw [hf] at hk
    show ofKL { f with C := C, theta := theta, cap := cap } = _
    rw [ofKL_withPol, show ofKL f = some pp from hk]
    rfl

/-! ### the scope -/

/-- Two values of the free numbers with one file, at which the scan returns, are one. -/
theorem policyFile_inj {v w : FreeLines} {P : PolScan} (h : polScan (policyFile v) = .ok P)
    (e : policyFile v = policyFile w) : v = w := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hdr_free h
  rw [e] at h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hdr_free h
  have c : v.eps1 = w.eps1 ∧ v.eps2 = w.eps2 := by simpa using a1.symm.trans b1
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := v
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := w
  dsimp only at a2 a3 a4 a5 a6 a7 b2 b3 b4 b5 b6 b7 c
  rw [c.1, c.2, ← a2, b2, ← a3, b3, ← a4, b4, ← a5, b5, ← a6, b6, ← a7, b7]

/-- What being in scope gives, at files whose parameter file is `policyFile v`. One direction. -/
theorem scope_parts {v : FreeLines} {lay KL : ByteArray}
    (h0 : InScope ⟨policyFile v, lay, KL⟩ = true) :
    lay = VerifierAndGoals.storedPublicFiles.lay ∧ ∃ pp, settingsAtRef (policyFile v) KL = .ok pp ∧
      freeLinesOf pp = v ∧ 2 ^ 8 ≤ pp.pol.theta := by
  cases hR : readFiles ⟨policyFile v, lay, KL⟩ with
  | error e =>
    unfold InScope at h0
    rw [hR] at h0
    simp at h0
  | ok pp =>
    unfold InScope at h0
    rw [hR] at h0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
    obtain ⟨S, hS, -⟩ := settingsAtRef_held hR
    exact ⟨h0.1, pp, hR, (policyFile_inj hS h0.2.1).symm, h0.2.2⟩

/-- **THE LAW.** Premises: h0, the files `policyFile v`, lay, KL are in the goals' scope; h1 to h4:
the numbers C, theta, cap are in the range. Then the same files with these three numbers are in
scope. -/
theorem inScope_withPol {v : FreeLines} {lay KL : ByteArray}
    (h0 : InScope ⟨policyFile v, lay, KL⟩ = true) {C theta cap : Nat} (h1 : C < 2 ^ 32)
    (h2 : theta ≤ C) (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    InScope ⟨policyFile { v with C := C, theta := theta, cap := cap }, lay, KL⟩ = true := by
  obtain ⟨hl, pp, hR, hv, -⟩ := scope_parts h0
  have hR' : readFiles ⟨policyFile { v with C := C, theta := theta, cap := cap }, lay, KL⟩ =
      .ok { pp with pol := ⟨C, theta, cap⟩ } := read_withPol hR h1 h2 h3
  have hv' : freeLinesOf { pp with pol := ⟨C, theta, cap⟩ } =
      { v with C := C, theta := theta, cap := cap } := by
    rw [← hv]
    rfl
  unfold InScope
  rw [hR']
  show (decide (lay = VerifierAndGoals.storedPublicFiles.lay) &&
    (decide (policyFile { v with C := C, theta := theta, cap := cap } =
      policyFile (freeLinesOf { pp with pol := ⟨C, theta, cap⟩ })) &&
        decide (2 ^ 8 ≤ theta))) = true
  rw [hv', decide_eq_true hl, decide_eq_true rfl, decide_eq_true h4]
  rfl

/-- With the first set in scope, the second is in scope exactly if the numbers are in the range. -/
theorem inScope_iff_range {v : FreeLines} {lay KL : ByteArray}
    (h0 : InScope ⟨policyFile v, lay, KL⟩ = true) (C theta cap : Nat) :
    InScope ⟨policyFile { v with C := C, theta := theta, cap := cap }, lay, KL⟩ = true ↔
      C < 2 ^ 32 ∧ theta ≤ C ∧ cap ≤ 1024 ∧ 2 ^ 8 ≤ theta := by
  constructor
  · intro h
    obtain ⟨-, pp, hR, hv, ht⟩ := scope_parts h
    obtain ⟨-, -, p1, p2, p3⟩ := premises_of_read hR
    have e : pp.pol.theta = theta := congrArg FreeLines.theta hv
    exact ⟨p3, p1, p2, by rw [← e]; exact ht⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact inScope_withPol h0 h1 h2 h3 h4

end LPFPol

#print axioms LPFPol.policyFile_inj
#print axioms LPFPol.scope_parts
#print axioms LPFPol.read_withPol
#print axioms LPFPol.inScope_withPol
#print axioms LPFPol.inScope_iff_range
