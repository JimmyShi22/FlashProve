-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/SettingsAtRef.lean: how the reading of the integer model's settings at any acceptance
policy (`settingsAny`, `settingsAtRef`, Johnson/Flat/SettingsRead.lean) stands to the reading at
exact match (`settingsOfFiles`, Johnson/Flat/ScalesOf.lean; `scalesAtRef`,
Johnson/Flat/ModelLines.lean).

Purpose. `scalesAtRef` reads a table of scales off a parameter file and a scale file. It refuses
every parameter file whose acceptance policy is not exact match, and it drops the policy's three
numbers C, theta, cap from what it returns. `settingsAtRef` is the same reading without that
refusal, and keeps the three numbers. The four theorems here say that at exact match the two
readings agree.

Theorems.
  `settingsOfFiles_eq`, `settingsOfFiles_iff`: `settingsOfFiles` is `sizesAt`, then `settingsAny`.
    It returns a value exactly if `settingsAny` returns it and the scanned file passes
    `exactPolicy`.
  `exactPolicy_iff`: at sh = 8 and sT = 4, `exactPolicy` holds exactly when (C, theta, cap) is
    `AcceptancePolicy.exact`: 256, 256, 0.
  `scalesAtRef_iff`: `scalesAtRef` returns s exactly if `settingsAtRef` returns settings whose
    policy is `AcceptancePolicy.exact` and whose scales are s. So at exact match the two readings agree.

Limits. Nothing on a protocol, on soundness or on what a proof under a policy means.
`settingsOfFiles_iff` speaks of `exactPolicy` and not of `AcceptancePolicy.exact`: `exactPolicy` also passes C =
theta = 2 ^ sh, cap = 0, sT = sh - 4 at an sh other than 8. All limits in the heads of
Johnson/Flat/SettingsRead.lean, Johnson/Flat/ScalesOf.lean and Johnson/Flat/ModelLines.lean hold
here too.
Nothing is evaluated at a file here.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ModelLines

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales here: each table is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Flat

open OnBytes.Model Inst.Model

/-- `settingsOfFiles` is `settingsAny` behind the call of `sizesAt`. -/
theorem settingsOfFiles_eq (policy KL : ByteArray) :
    settingsOfFiles policy KL = (sizesAt policy >>= fun _ => settingsAny policy KL) := rfl

/-- `settingsOfFiles` returns pp exactly if `settingsAny` returns pp and the scanned parameter
file's lines C, theta, cap, sh, sT pass `exactPolicy`. -/
theorem settingsOfFiles_iff {policy KL : ByteArray} {pp : ScalesAndPolicy} :
    settingsOfFiles policy KL = .ok pp ↔
      settingsAny policy KL = .ok pp ∧ ∃ P, polScan policy = .ok P ∧ exactPolicy P.h = true := by
  rw [settingsOfFiles_eq]
  constructor
  · intro h
    cases h1 : sizesAt policy with
    | error e =>
      rw [h1] at h
      cases h
    | ok P0 =>
      rw [h1] at h
      refine ⟨h, ?_⟩
      unfold sizesAt at h1
      cases hP : polScan policy with
      | error e =>
        rw [hP] at h1
        cases h1
      | ok P =>
        rw [hP] at h1
        have h2 : (if exactPolicy P.h = true then (pure (sizesOf P.h) : Except String _)
          else throw "policy-not-exact-match") = .ok P0 := h1
        by_cases hx : exactPolicy P.h = true
        · exact ⟨P, rfl, hx⟩
        · rw [if_neg hx] at h2
          cases h2
  · rintro ⟨h, P, hP, hx⟩
    have h1 : sizesAt policy = .ok (sizesOf P.h) := by
      unfold sizesAt
      rw [hP]
      show (if exactPolicy P.h = true then (pure (sizesOf P.h) : Except String _)
        else throw "policy-not-exact-match") = _
      rw [if_pos hx]
      rfl
    rw [h1]
    exact h

/-- At sh = 8 and sT = 4 a header passes `exactPolicy` exactly if its lines C, theta, cap are those
of `AcceptancePolicy.exact`: 256, 256, 0. -/
theorem exactPolicy_iff {h : Hdr} (h8 : h.digSh = 8) (h4 : h.tabS = 4) :
    exactPolicy h = true ↔ (⟨h.clipC, h.theta, h.cap⟩ : AcceptancePolicy) = AcceptancePolicy.exact := by
  unfold exactPolicy exactMatch AcceptancePolicy.exact
  rw [h8, h4]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, AcceptancePolicy.mk.injEq]
  constructor
  · rintro ⟨⟨⟨⟨-, a⟩, b⟩, -⟩, c⟩
    exact ⟨a.trans c, c, b⟩
  · rintro ⟨a, b, c⟩
    exact ⟨⟨⟨⟨by norm_num, a.trans b.symm⟩, c⟩, trivial⟩, b⟩

/-- **The reading at exact match is this one at `AcceptancePolicy.exact`.** `scalesAtRef` returns the table s
exactly if `settingsAtRef` returns settings whose policy is `AcceptancePolicy.exact` and whose scales are s. -/
theorem scalesAtRef_iff {policy KL : ByteArray} {s : Cm.Scales} :
    scalesAtRef policy KL = .ok s ↔
      ∃ pp, settingsAtRef policy KL = .ok pp ∧ pp.pol = AcceptancePolicy.exact ∧ s = Cm.Scales.of pp := by
  constructor
  · intro h
    obtain ⟨S, hS, hh⟩ := scalesAtRef_held h
    obtain ⟨-, h8, h4, -⟩ := otherLinesHeld_policy hh
    have h0 := scalesAtRef_eq h
    unfold scalesOfFiles at h0
    cases h1 : settingsOfFiles policy KL with
    | error e =>
      rw [h1] at h0
      cases h0
    | ok pp =>
      rw [h1] at h0
      have hs : Cm.Scales.of pp = s := Except.ok.inj h0
      obtain ⟨ha, P, hP, hx⟩ := settingsOfFiles_iff.1 h1
      have e0 : P = S := Except.ok.inj (hP.symm.trans hS)
      subst e0
      exact ⟨pp, settingsAtRef_of hS hh ha,
        (settingsAny_pol hS ha).trans ((exactPolicy_iff h8 h4).1 hx), hs.symm⟩
  · rintro ⟨pp, h, hp, rfl⟩
    obtain ⟨S, hS, hh⟩ := settingsAtRef_held h
    obtain ⟨-, h8, h4, -⟩ := otherLinesHeld_policy hh
    have ha := settingsAtRef_eq h
    have hx : exactPolicy S.h = true :=
      (exactPolicy_iff h8 h4).2 ((settingsAny_pol hS ha).symm.trans hp)
    have h1 : settingsOfFiles policy KL = .ok pp := settingsOfFiles_iff.2 ⟨ha, S, hS, hx⟩
    refine scalesAtRef_of hS hh ?_
    unfold scalesOfFiles
    rw [h1]
    rfl

end OnBytes.Flat
