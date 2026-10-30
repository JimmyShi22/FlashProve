-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Files/FilesReadAtRef.lean: what the reader of the public files returns at the two named
sets (`storedPublicFiles`, `zGap`, Ladder/Stored.lean) beyond the policy: the scales of all 48 layers and the
final normalisation are the reference table's (`Cm.sRef`, Cm/Rel2Guards.lean). So the integer
model's settings there are `settingsOf Cm.sRef`. Statements with proofs; no definition; no goal is
stated.

Why. `FilesRead` (Ladder.lean) and `VerifierAndGoals.filesRead` (Johnson/Goal/Files/FilesReadProof.lean) say
nothing of what the reader returns beyond its policy and its eight free numbers: of the 48 layers'
scales nothing but two constants of the first layer's. A theorem that is stated "at the reference
scales" (at `settingsOf Cm.sRef`) could therefore not be carried to the stored files. The tests that
the kernel has evaluated (Johnson/Goal/Files/FilesReadChecks.lean) hold more than `VerifierAndGoals.filesRead`
tells: `CheckKL` asks that the table's scales of the layers and its final normalisation are the
reference's.

  `Read.read_of_check_ref`: `Read.read_of_check` (Ladder/FilesReadLaws.lean) with two clauses more
    in its conclusion. Its proof is that theorem's, line for line, but for the one `refine`: there
    the two facts were at hand and were dropped.
  `scales_of_ref`, **`settingsOfRead_of_ref`**: a table with the reference's scales of the layers
    (`Words`) and final normalisation has the reference's settings, whatever its policy.
  `read_full_ref`, `read_gap_ref`: the two named sets are read, with their policies, as such tables.
  **`settingsOfRead_full`**, **`settingsOfRead_gap`**: whatever the reader returns at a named set
    has the settings `settingsOf Cm.sRef`. `pol_full`, `pol_gap`: and the set's policy.
  **`of_ref_full`**, **`of_ref_gap`**: so whatever holds of the reference's settings and the set's
    policy holds of what the reader returns there.

How to use it. State the fact as a property of settings and a policy and call `of_ref_full` or
`of_ref_gap`; or pass `(settingsOfRead_full read).symm` as the hypothesis `tie` of a theorem that
takes one (`tie : settingsOf scales = settings`, as in Policy/Front/TrueUnder.lean). A statement
that holds a proof about `settingsOf Cm.sRef` inside it (say `settingsAreValid_settingsOf
Cm.lawful_sRef`) may first have to be stated for all settings, with that proof as a hypothesis:
not tried.

Limits. It speaks of the bytes written in Ladder/Stored.lean. That they are the bytes of the
repository's folder examples/ is not said. It serves at the reference table alone: of files in scope
with another scale file, or with other values of the five free numbers that enter the table, it
says nothing. No goal states the scales. Nothing on a description or a verifier: no goal is met by
it.

-/
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifierAndGoals.Read
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Flat Inst.Model OnBytes.Tie.Pv.Plan

/-- What the two halves of the test give of the reader, with the table's scales: `read_of_check`
and, beside it, that the scales of all layers and the final normalisation are the reference's. -/
theorem read_of_check_ref {pol KL : ByteArray} {v : FreeLines}
    (h : checkPol pol.data.toList v = true) (h' : CheckKL KL v) :
    ∃ pp, settingsAtRef pol KL = .ok pp ∧ freeLinesOf pp = v ∧ 2 ^ 8 ≤ pp.pol.theta ∧
      pp.w = Cm.sRef.w ∧ pp.nf = Cm.sRef.nf := by
  unfold checkPol at h
  obtain ⟨hrest, hrows⟩ := h'
  unfold restOK at hrest
  cases hS : polScanL pol.data.toList with
  | error e => rw [hS] at h; cases h
  | ok S =>
    rw [hS] at h
    have hP : polScan pol = .ok S := (polScan_eq pol).trans hS
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h0, hL⟩, hv0⟩ := h
    cases hk : tableOf KL v with
    | none => rw [hk] at hrest; cases hrest
    | some pp =>
      rw [hk] at hrest
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
      obtain ⟨⟨⟨hnf, hpol⟩, hv⟩, ht⟩ := hrest
      have hw : ∀ L, pp.w L = Cm.sRef.w L := by
        intro L
        have hr := hrows
        unfold rowsOK at hr
        simp only [List.all_eq_true, decide_eq_true_eq] at hr
        rw [w_of_table hk L]
        exact hr L (List.mem_finRange L)
      refine ⟨pp, ?_, sameLines_eq hv, ht, funext hw, hnf⟩
      have hn : firstOtherLine S = none := Option.isNone_iff_eq_none.1 h0
      have hk' : (klFileOf S.h KL).bind ofKL = some pp := by
        rw [klFileOf_eq, hL, sameLines_eq hv0]
        exact hk
      have ha : settingsAny pol KL = .ok pp :=
        settingsAny_iff.2 ⟨S, hP, hk', lawful_of_ref hw hnf hpol⟩
      unfold settingsAtRef
      rw [hP]
      show (match firstOtherLine S with
        | some name => (throw ("model-line-not-the-reference's: " ++ name) : Except String ScalesAndPolicy)
        | none => settingsAny pol KL) = .ok pp
      rw [hn]
      exact ha

end VerifierAndGoals.Read

namespace VerifierAndGoals
open VerifiableInference

/-- A table with the reference's scales of the layers (`Words`) and final normalisation has the
reference's scales. The policy is no part of the scales. -/
theorem scales_of_ref {pp : Inst.Model.ScalesAndPolicy} (hw : pp.w = Cm.sRef.w) (hn : pp.nf = Cm.sRef.nf) :
    Cm.Scales.of pp = Cm.sRef := by
  obtain ⟨w, nf, p⟩ := pp
  subst hw hn
  rfl

/-- **A table with the reference's scales of the layers and final normalisation has the
reference's settings**, whatever its policy. -/
theorem settingsOfRead_of_ref {pp : Inst.Model.ScalesAndPolicy} (hw : pp.w = Cm.sRef.w)
    (hn : pp.nf = Cm.sRef.nf) : settingsOfRead pp = settingsOf Cm.sRef :=
  congrArg settingsOf (scales_of_ref hw hn)

/- The named files stay folded from here on: left to unfold them, Lean compares whole files byte by
byte and runs out of stack (Johnson/Goal/Files/FilesReadProof.lean's own note). -/
attribute [local irreducible] storedPublicFiles zGap

/-- The stored full-size example's files are read as the reference table at exact match. -/
theorem read_full_ref : ∃ pp, readFiles storedPublicFiles = .ok pp ∧ pp.pol = Inst.Model.AcceptancePolicy.exact ∧
    pp.w = Cm.sRef.w ∧ pp.nf = Cm.sRef.nf := by
  obtain ⟨pp, hr, hv, -, hw, hn⟩ := Read.read_of_check_ref Read.polFull Read.klFull
  refine ⟨pp, hr, ?_, hw, hn⟩
  have hp : pp.pol = ⟨storedLines.C, storedLines.theta, storedLines.cap⟩ := by
    rw [← hv]
    rfl
  exact hp

/-- The second named set's files are read as the reference table at the policy (25856, 512, 1). -/
theorem read_gap_ref : ∃ pp, readFiles zGap = .ok pp ∧ pp.pol = ⟨25856, 512, 1⟩ ∧
    pp.w = Cm.sRef.w ∧ pp.nf = Cm.sRef.nf := by
  obtain ⟨pp, hr, hv, -, hw, hn⟩ := Read.read_of_check_ref Read.polGap Read.klGap
  refine ⟨pp, hr, ?_, hw, hn⟩
  have hp : pp.pol = ⟨Read.gapLines.C, Read.gapLines.theta, Read.gapLines.cap⟩ := by
    rw [← hv]
    rfl
  exact hp

/-- **Whatever the reader returns at the stored full-size example's files has the reference's
settings.** -/
theorem settingsOfRead_full {pp : Inst.Model.ScalesAndPolicy} (read : readFiles storedPublicFiles = .ok pp) :
    settingsOfRead pp = settingsOf Cm.sRef := by
  obtain ⟨pp', hr, -, hw, hn⟩ := read_full_ref
  obtain rfl : pp = pp' := Except.ok.inj (read.symm.trans hr)
  exact settingsOfRead_of_ref hw hn

/-- **The same at the second named set.** -/
theorem settingsOfRead_gap {pp : Inst.Model.ScalesAndPolicy} (read : readFiles zGap = .ok pp) :
    settingsOfRead pp = settingsOf Cm.sRef := by
  obtain ⟨pp', hr, -, hw, hn⟩ := read_gap_ref
  obtain rfl : pp = pp' := Except.ok.inj (read.symm.trans hr)
  exact settingsOfRead_of_ref hw hn

/-- The policy that the reader returns at the stored full-size example's files is exact match. -/
theorem pol_full {pp : Inst.Model.ScalesAndPolicy} (read : readFiles storedPublicFiles = .ok pp) :
    pp.pol = Inst.Model.AcceptancePolicy.exact := by
  obtain ⟨pp', hr, hp, -, -⟩ := read_full_ref
  obtain rfl : pp = pp' := Except.ok.inj (read.symm.trans hr)
  exact hp

/-- The policy that the reader returns at the second named set is (25856, 512, 1). -/
theorem pol_gap {pp : Inst.Model.ScalesAndPolicy} (read : readFiles zGap = .ok pp) :
    pp.pol = ⟨25856, 512, 1⟩ := by
  obtain ⟨pp', hr, hp, -, -⟩ := read_gap_ref
  obtain rfl : pp = pp' := Except.ok.inj (read.symm.trans hr)
  exact hp

/-- **Whatever holds of the reference's settings at exact match holds of what the reader returns at
the stored full-size example's files.** -/
theorem of_ref_full {P : IntegerTransformer.Settings → Inst.Model.AcceptancePolicy → Prop}
    (h : P (settingsOf Cm.sRef) Inst.Model.AcceptancePolicy.exact) {pp : Inst.Model.ScalesAndPolicy}
    (read : readFiles storedPublicFiles = .ok pp) : P (settingsOfRead pp) pp.pol := by
  rw [settingsOfRead_full read, pol_full read]
  exact h

/-- **Whatever holds of the reference's settings at the policy (25856, 512, 1) holds of what the
reader returns at the second named set.** -/
theorem of_ref_gap {P : IntegerTransformer.Settings → Inst.Model.AcceptancePolicy → Prop}
    (h : P (settingsOf Cm.sRef) ⟨25856, 512, 1⟩) {pp : Inst.Model.ScalesAndPolicy}
    (read : readFiles zGap = .ok pp) : P (settingsOfRead pp) pp.pol := by
  rw [settingsOfRead_gap read, pol_gap read]
  exact h

end VerifierAndGoals

#print axioms VerifierAndGoals.Read.read_of_check_ref
#print axioms VerifierAndGoals.scales_of_ref
#print axioms VerifierAndGoals.settingsOfRead_of_ref
#print axioms VerifierAndGoals.read_full_ref
#print axioms VerifierAndGoals.read_gap_ref
#print axioms VerifierAndGoals.settingsOfRead_full
#print axioms VerifierAndGoals.settingsOfRead_gap
#print axioms VerifierAndGoals.pol_full
#print axioms VerifierAndGoals.pol_gap
#print axioms VerifierAndGoals.of_ref_full
#print axioms VerifierAndGoals.of_ref_gap
