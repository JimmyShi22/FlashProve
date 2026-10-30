-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/SoundAtStored.lean: the library's two soundness theorems at named public files:
names for their instances at `storedPublicFiles`, at `zGap` and at `zAt C theta cap`.

`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap` are sets of three public files as Ladder/Stored.lean spells them;
`VerifierAndGoals.zAt C theta cap` (Johnson/Goal/Files/ScopeAtPolicies.lean) is `storedPublicFiles` with the acceptance
policy (C, theta, cap).

What it adds. Names, and one small fact on the reader. No new fact on soundness.
`sound_of_verify_at` (Johnson/Goal/Skeleton/SoundOfVerifyAt.lean) holds at all public files in the
goals' scope that the reader reads and that state exact match. `soundUnderPolicy_of_verify_at`
(Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean) holds at all public files in scope that the reader
reads. Here they are called at files of which these premises are shown: at `storedPublicFiles` and `zGap` by
`VerifierAndGoals.filesRead` (Johnson/Goal/Files/FilesReadProof.lean), at `zAt` by `VerifierAndGoals.inScope_zAt` and
this file's `read_zAt`.

Main names.
* `sound_zFull`: the reader returns settings at `storedPublicFiles`, they state exact match, and `Sound` holds
  of the verifier with the description's own parser there, at `VerifierAndGoals.soundnessErrorInQueries t 1`.
* `soundUnderPolicy_zFull`, `soundUnderPolicy_zGap`: the reader returns settings with the files'
  policy, and `SoundUnderPolicyAtZ` holds there at `VerifierAndGoals.soundnessErrorInQueries`: for every form of proof and every
  parser within n queries, as the called file's head says.
* `read_zAt`: for every policy within the four bounds (C below 2 to the 32, theta at most C, cap at
  most 1024, theta at least 256) the reader returns settings at `zAt C theta cap`, with that policy.
  A short proof of its own, over `LPFPol.scope_parts` (Johnson/LPFPol/ScopeAtPolicy.lean).
* `soundUnderPolicy_zAt`: the policy form at `zAt C theta cap`, within the four bounds.

Limits.
* Every limit in the heads of the two called files holds here, whole: calls, worth what the called
  theorems and the statements' definitions are worth; soundness alone: no binding, no completeness,
  nothing on hiding; one set of public files at a time, fixed before the hash function is drawn; the
  second hash function is a fixed function; the full size alone; the verifier with fourteen entry
  tests; `sound_zFull` at the description's own parser; the error grows with the parser's queries n;
  beneath six of the called rows (the two called files'
  heads say five) stand files on coding theory adapted
  from third-party Lean (lean/LIMITS.md, L15).
* One name is not enough. These statements would stand unchanged if the verifier rejected everything
  at these files: where one of its own tests on the public files fails, it does, and they hold for
  that reason. That the tests pass is not shown in this file or beneath it. The companions are
  `tests_zFull`, `tests_zGap` and `tests_zAt` (AtFullSide/Top/ThreeTests.lean, in a side library
  that is built with a larger thread stack): the test of the scope, the test `protocolDataWellFormed`, and of a
  third place the outer match alone. No Lean constant holds a soundness statement and its companion
  together. These three places are settled side by side in ThreeTests.lean; they are not all that
  are known: more have been found, some settled and some not, and no theorem says that any list of
  them is whole. That any proof is accepted is shown nowhere.
* What "meets the policy" says at a policy other than exact match is the definition's
  (Policy/Front/MeetsPolicy.lean). Where theta = C and cap is at least the number of counted tokens,
  it says nothing of the counted tokens. And by Ladder.lean's head, point 6: at every policy with
  257 ≤ theta and 257 ≤ C, that of `zGap` among them, the all-zero weights meet it at every request
  of the right form (`meetsPolicy_zeroWeights`, Policy/Front/TrueUnder.lean). So against a committer
  who commits to such weights the policy form says nothing at these policies, and it means something
  only together with the goals `G9` and `G3'pol`.
* The named files are terms. No Lean ties them to files in a folder of examples or to files that a
  program writes, and the example's weights are synthetic (Ladder/Stored.lean's head).

-/
import Johnson.Goal.Skeleton.SoundOfVerifyAt
import Johnson.Goal.Skeleton.SoundOfVerifyPolicy
import Johnson.Goal.Files.FilesReadProof
import Johnson.Goal.Files.ScopeAtPolicies

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFull.Top
open VerifierAndGoals FlashProve FlashProve VerifierAndGoals.AtTheName

/- The named files stay folded: left to unfold them, Lean compares whole files byte by byte and runs
out of stack (Johnson/Goal/Files/FilesReadProof.lean has the same note). -/
attribute [local irreducible] storedPublicFiles zGap zAt

/-- **The soundness theorem at `storedPublicFiles`**: an instance of `sound_of_verify_at`. -/
theorem sound_zFull :
    ∃ pp, readFiles storedPublicFiles = .ok pp ∧ pp.pol = Inst.Model.AcceptancePolicy.exact ∧
      VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) storedPublicFiles (settingsOfRead pp))
        fun t => VerifierAndGoals.soundnessErrorInQueries t 1 := by
  obtain ⟨hs, pp, hr, he⟩ := filesRead.full
  exact ⟨pp, hr, he, sound_of_verify_at storedPublicFiles pp hs hr he⟩

/-- **Soundness under the files' policy at `storedPublicFiles`**: an instance of
`soundUnderPolicy_of_verify_at`. -/
theorem soundUnderPolicy_zFull :
    ∃ pp, readFiles storedPublicFiles = .ok pp ∧ pp.pol = Inst.Model.AcceptancePolicy.exact ∧
      SoundUnderPolicyAtZ (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries storedPublicFiles pp := by
  obtain ⟨hs, pp, hr, he⟩ := filesRead.full
  exact ⟨pp, hr, he, soundUnderPolicy_of_verify_at storedPublicFiles pp hs hr⟩

/-- **Soundness under the files' policy at `zGap`**: an instance of
`soundUnderPolicy_of_verify_at`. -/
theorem soundUnderPolicy_zGap :
    ∃ pp, readFiles zGap = .ok pp ∧ pp.pol = ⟨25856, 512, 1⟩ ∧
      SoundUnderPolicyAtZ (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries zGap pp := by
  obtain ⟨hs, pp, hr, he⟩ := filesRead.other
  exact ⟨pp, hr, he, soundUnderPolicy_of_verify_at zGap pp hs hr⟩

/-- Within the four bounds the reader returns settings at `zAt C theta cap`, with that policy. -/
theorem read_zAt {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024)
    (h4 : 2 ^ 8 ≤ theta) :
    ∃ pp, readFiles (zAt C theta cap) = .ok pp ∧ pp.pol = ⟨C, theta, cap⟩ := by
  have hZ := inScope_zAt h1 h2 h3 h4
  rw [zAt_form] at hZ
  obtain ⟨-, pp, hR, hv, -⟩ := LPFPol.scope_parts hZ
  refine ⟨pp, ?_, ?_⟩
  · rw [zAt_form]
    exact hR
  · have a : pp.pol.C = C := congrArg FreeLines.C hv
    have b : pp.pol.theta = theta := congrArg FreeLines.theta hv
    have c : pp.pol.cap = cap := congrArg FreeLines.cap hv
    rw [← a, ← b, ← c]

/-- **Soundness under the files' policy at `zAt C theta cap`, for every policy within the four
bounds**: an instance of `soundUnderPolicy_of_verify_at`. -/
theorem soundUnderPolicy_zAt {C theta cap : Nat} (h1 : C < 2 ^ 32) (h2 : theta ≤ C)
    (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    ∃ pp, readFiles (zAt C theta cap) = .ok pp ∧ pp.pol = ⟨C, theta, cap⟩ ∧
      SoundUnderPolicyAtZ (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries (zAt C theta cap) pp := by
  obtain ⟨pp, hr, he⟩ := read_zAt h1 h2 h3 h4
  exact ⟨pp, hr, he,
    soundUnderPolicy_of_verify_at (zAt C theta cap) pp (inScope_zAt h1 h2 h3 h4) hr⟩

end AtFull.Top

#print axioms AtFull.Top.sound_zFull
#print axioms AtFull.Top.soundUnderPolicy_zFull
#print axioms AtFull.Top.soundUnderPolicy_zGap
#print axioms AtFull.Top.read_zAt
#print axioms AtFull.Top.soundUnderPolicy_zAt
