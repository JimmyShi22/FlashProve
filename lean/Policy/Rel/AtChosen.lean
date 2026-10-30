-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/AtChosen.lean

Guards on a policy (C, θ, cap), stated once for every policy in a named range. They bear on the
question whether three given numbers are a policy with content. `InRange pol` says
257 ≤ θ < C < 16,767,233 and cap < 1,023. For given numbers it is settled by evaluating four
comparisons (`inRange_qExample`).

For every policy in the range:
* `polTests_of_inRange`, `polCond_of_inRange`, `lawful_of_inRange`: it passes `PolTests`
  (Inst/Model/ProgTests.lean), meets `PolCond` (Policy/Rel/True.lean), and with a lawful table of
  scales it makes valid settings (`Lawful`, Inst/Model/Scales.lean).
* `looser_of_inRange`: it admits a request that exact match refuses.
* `zeroWeights_of_inRange`: a caution. At the all-zero weights it admits every request that has its
  form, with y = 0 if e = 1,024, whatever the tokens.
* `teeth_of_inRange`: it refuses a request that another policy admits (`Teeth.teeth_in_range`,
  Policy/Rel/Teeth.lean).
* `each_number_decides`: under four further hypotheses on the numbers, each of the three alone
  decides a request (Policy/Rel/TeethCount.lean). The four are narrow. Three of them are 1 ≤ cap (in
  the part on C the one costly position has to be let above the clip), θ < 2,303 and 2,303 ≤ C (the
  part on θ uses the votes a = 1, b = 0); the fourth is `room`. At a larger θ this theorem says
  nothing. `Teeth.theta_alone_decides` reaches costs up to 16,767,233. `Teeth.C_alone_decides` asks
  1,023 θ < C' + 1,022 · 2^8 for a C' < 16,767,233: so its hypotheses cannot be met at a large θ.
* `not_idle_of_inRange`: neither premise of `TrueGuards.idle` (Policy/Rel/TrueGuards.lean) holds of
  it.

`qExample` is a clipped-gap policy at which the guards of this file are read. "Chosen" in the file's
name says only that its three numbers were picked to read the guards at. They are made up: C and θ
are multiples of 2^sh = 2^8, cap is 1. They were fitted to no model or reply, and nothing says that
they are a sensible policy. They are the three numbers that the library's reader of the public files
(`VerifierAndGoals.readFiles`, Ladder.lean) returns at `VerifierAndGoals.zGap`, the second of the two sets of public
files that Ladder.lean names (`Policy.qExample_eq`, Policy/Front/MeetsPolicyAtGap.lean;
`VerifierAndGoals.read_gap_ref`, `VerifierAndGoals.pol_gap`, Johnson/Goal/Files/FilesReadAtRef.lean). `zGap` is a term
of Ladder/Stored.lean: no theorem ties its bytes to a file on disk.

Limits:
* `InRange` is this file's own name for a range in which these guards hold. It is no judgement on a
  policy outside it.
* The refusal in `teeth_of_inRange` is by clause (a), the mean. A refusal by clause (b), the count,
  of a request that (a) admits is shown in `Teeth.cap_alone_decides` (Policy/Rel/TeethCount.lean)
  and, at this range, in `each_number_decides`, each under its further hypotheses.
* All weights are made up: the all-zero weights, and those of Policy/Rel/Teeth.lean, whose limits
  hold here too. `teeth_of_inRange` and `each_number_decides` are at the reference scales
  (`Cm.sRef`) alone. Nothing is shown at a trained model.
* `PolTests` is this library's rendering of the programs' tests on the three lines. That it says
  what the programs test is a reading, and no theorem.
* What `aboveClip` and `policyEmpty` (OnBytes/Model/Config.lean) return at the numbers of `qExample`
  and sh = 8, for every n, is stated in `Policy.aboveClip_qExample` and
  `Policy.policyEmpty_qExample` (Johnson/IMR/MeetsPolicyAtPort.lean). For `policyKind`
  OnBytes/Model/ConfigPolicyLaws.lean has the law at letters, at sh = 8 and sT = 4; its value at
  these numbers comes of putting the numbers in by hand.
* Nothing here speaks of a protocol, a prover or a verifier.

Terms: lean/GLOSSARY.md.

-/
import Policy.Rel.TeethCount
noncomputable section

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.AtChosen

open Inst.Model Inst.Model.ScalesSanity Inst.Model.ProgramRGuards Inst.Model.RequestGuards2

/-- The range for which this file's guards are stated: 257 ≤ θ < C < 16,767,233 and cap < 1,023. -/
structure InRange (pol : AcceptancePolicy) : Prop where
  mean : 257 ≤ pol.theta
  clip : pol.theta < pol.C
  top : pol.C < 16767233
  cap : pol.cap < 1023

/-- A policy in the range meets the clause on the policy in `LawfulBut` (Inst/Model/Scales.lean). -/
theorem lawfulClause_of_inRange {pol : AcceptancePolicy} (h : InRange pol) :
    pol.C < 2 ^ 32 ∧ pol.theta ≤ pol.C ∧ pol.cap ≤ 1024 :=
  ⟨by have := h.top; omega, le_of_lt h.clip, by have := h.cap; omega⟩

/-- A policy in the range passes `PolTests`. -/
theorem polTests_of_inRange {pol : AcceptancePolicy} (h : InRange pol) : PolTests pol :=
  (polTests_iff _).2 (lawfulClause_of_inRange h)

/-- A policy in the range meets `PolCond`. -/
theorem polCond_of_inRange {pol : AcceptancePolicy} (h : InRange pol) : PolCond pol :=
  polCond_of_tests (polTests_of_inRange h)

/-- A lawful table of scales (the hypothesis `hs`) with a policy in the range makes valid
settings. -/
theorem lawful_of_inRange {pol : AcceptancePolicy} (h : InRange pol) {s : Cm.Scales} (hs : s.Lawful) :
    Lawful (ppOf s pol) :=
  ⟨⟨hs.toPP.ff, hs.toPP.sh, hs.toPP.one, hs.toPP.nf, lawfulClause_of_inRange h⟩, hs.toPP.km⟩

/-- A policy in the range is looser than exact match: at every lawful table and the all-zero weights
it admits `x1` (all tokens 1, r = 0, e = 1,023; Inst/Model/RequestGuards2.lean), which exact match
refuses there. -/
theorem looser_of_inRange {pol : AcceptancePolicy} (h : InRange pol) {s : Cm.Scales} (hs : s.Lawful) :
    IsTrueUnder s pol (Cm.Idx.ofIndex iZero) x1 ∧
      ¬ IsTrueUnder s AcceptancePolicy.exact (Cm.Idx.ofIndex iZero) x1 :=
  ⟨TrueGuards.zero_all hs pol h.mean (le_of_lt (lt_of_le_of_lt h.mean h.clip)) x1
      ⟨by decide, by decide, fun _ => rfl⟩ (fun e => absurd e (by decide)),
    fun t => (budget (pp := ppOf s AcceptancePolicy.exact) hs.toPP).2 ((isTrueUnder_ofIndex s _ iZero x1).1 t)⟩

/-- A caution. At every lawful table and the all-zero weights, a policy in the range admits every
request that has its form (`h3`), with y = 0 if e = 1,024 (`hy`), whatever its tokens. -/
theorem zeroWeights_of_inRange {pol : AcceptancePolicy} (h : InRange pol) {s : Cm.Scales} (hs : s.Lawful)
    (x : Instance ppref) (h3 : Head3 x) (hy : x.e = ppref.T → x.y.val = 0) :
    IsTrueUnder s pol (Cm.Idx.ofIndex iZero) x :=
  TrueGuards.zero_all hs pol h.mean (le_of_lt (lt_of_le_of_lt h.mean h.clip)) x h3 hy

/-- At the reference scales a policy in the range refuses the request `Teeth.xTeeth` at the index
`Teeth.iTeeth`, by clause (a); the policy (16,767,233, 16,767,233, 0) admits it there. -/
theorem teeth_of_inRange {pol : AcceptancePolicy} (h : InRange pol) :
    ¬ IsTrueUnder Cm.sRef pol Teeth.iTeeth Teeth.xTeeth ∧
      IsTrueUnder Cm.sRef ⟨16767233, 16767233, 0⟩ Teeth.iTeeth Teeth.xTeeth :=
  Teeth.teeth_in_range pol (Or.inl ⟨h.clip, lt_trans h.clip h.top⟩)

/-- Neither premise of `TrueGuards.idle` holds of a policy in the range. -/
theorem not_idle_of_inRange {pol : AcceptancePolicy} (h : InRange pol) :
    ¬ (pol.C ≤ pol.theta) ∧ ¬ (1023 ≤ pol.cap) :=
  ⟨not_le.2 h.clip, not_le.2 h.cap⟩

/-- The votes a = 1, b = 0, at which a position that checks token 0 costs 2^8 + 2,047 = 2,303. -/
theorem votes_one : Teeth.Votes 1 0 := ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Each of the three numbers alone decides a request.** Hypotheses: the policy is in the range;
1 ≤ cap; `room`: cap + 1 costs of C and 1,022 - cap costs of 2^8 add up to at most 1,023 θ;
θ < 2,303 ≤ C. Then, at the reference scales and the made-up weights of Policy/Rel/Teeth.lean:
* cap: a request with cap + 1 costly positions is not true under (C, θ, cap) and is true under
  (C, θ, cap + 1);
* θ: a request whose 1,023 counted positions all cost 2,303 is not true under (C, θ, cap) and is
  true under (C, 2,303, cap);
* C: a request with one costly position is true under (C, θ, cap) and is not true under
  (16,767,232, θ, cap). -/
theorem each_number_decides {pol : AcceptancePolicy} (h : InRange pol) (hcap : 1 ≤ pol.cap)
    (room : (pol.cap + 1) * pol.C + (1022 - pol.cap) * 2 ^ 8 ≤ pol.theta * 1023)
    (hθ : pol.theta < 2303) (hC : 2303 ≤ pol.C) :
    (¬ IsTrueUnder Cm.sRef pol Teeth.iTeeth (Teeth.xMiss (pol.cap + 1)) ∧
      IsTrueUnder Cm.sRef ⟨pol.C, pol.theta, pol.cap + 1⟩ Teeth.iTeeth
        (Teeth.xMiss (pol.cap + 1))) ∧
    (¬ IsTrueUnder Cm.sRef pol (Teeth.idxAB votes_one) Teeth.xTeeth ∧
      IsTrueUnder Cm.sRef ⟨pol.C, 2303, pol.cap⟩ (Teeth.idxAB votes_one) Teeth.xTeeth) ∧
    (IsTrueUnder Cm.sRef pol Teeth.iTeeth (Teeth.xMiss 1) ∧
      ¬ IsTrueUnder Cm.sRef ⟨16767232, pol.theta, pol.cap⟩ Teeth.iTeeth (Teeth.xMiss 1)) := by
  have hC0 : 2 ^ 8 ≤ pol.C := by omega
  have hc := Teeth.cap_alone_decides pol hC0 h.top h.cap room
  have room1 : pol.C + 1022 * 2 ^ 8 ≤ pol.theta * 1023 := by
    have e1 : (pol.cap + 1) * pol.C = pol.cap * pol.C + pol.C := by ring
    have e2 : pol.cap * 2 ^ 8 ≤ pol.cap * pol.C := Nat.mul_le_mul_left _ hC0
    have e3 : (1022 - pol.cap) * 2 ^ 8 + pol.cap * 2 ^ 8 = 1022 * 2 ^ 8 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by have := h.cap; omega)]
    rw [e1] at room
    omega
  exact ⟨⟨hc.1, hc.2.1⟩,
    Teeth.theta_alone_decides votes_one pol (by norm_num; exact_mod_cast hθ) (by norm_num) hC,
    Teeth.C_alone_decides pol hC0 hcap room1 (by norm_num) (by omega)⟩

/-- A clipped-gap policy at which the guards of this file are read: C = 25,856 = 101 · 2^8,
θ = 512 = 2 · 2^8, cap = 1. -/
def qExample : AcceptancePolicy := ⟨25856, 512, 1⟩

/-- It lies in the range. -/
theorem inRange_qExample : InRange qExample := ⟨by decide, by decide, by decide, by decide⟩

/-- It meets the further hypotheses of `each_number_decides`. -/
theorem each_number_decides_qExample :
    (¬ IsTrueUnder Cm.sRef qExample Teeth.iTeeth (Teeth.xMiss 2) ∧
      IsTrueUnder Cm.sRef ⟨25856, 512, 2⟩ Teeth.iTeeth (Teeth.xMiss 2)) ∧
    (¬ IsTrueUnder Cm.sRef qExample (Teeth.idxAB votes_one) Teeth.xTeeth ∧
      IsTrueUnder Cm.sRef ⟨25856, 2303, 1⟩ (Teeth.idxAB votes_one) Teeth.xTeeth) ∧
    (IsTrueUnder Cm.sRef qExample Teeth.iTeeth (Teeth.xMiss 1) ∧
      ¬ IsTrueUnder Cm.sRef ⟨16767232, 512, 1⟩ Teeth.iTeeth (Teeth.xMiss 1)) :=
  each_number_decides inRange_qExample (by decide) (by decide) (by decide) (by decide)

end Policy.AtChosen
