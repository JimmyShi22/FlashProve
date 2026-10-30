-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/StopsShared.lean: no side of the prover's shared list has a test that can
stop it: the field `stops` of `WalkFacts` at the list `sharedWithUO` (K12/AtProof/HalfOAtPure.lean).

  `quiet_test`   the two parts of a test's half are quiet
  `noStop_withUO`   the statement: K14's six, by `six_stops_none` (Honest/K14/StopsNone.lean); the two tests' halves,
                 the second behind its guard, which changes no part's two tests

Limits. The two tests `bad` and `hid` alone. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfOAtPure
import Johnson.Desc.ProofFile.Honest.K14.AtWiderShared
import Johnson.Desc.ProofFile.Honest.K14.StopsNone
import E2E.NoStop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open AtPublicFiles.Stops (NoStop Quiet)
open ProofFile.Honest.K12.AtProof (sharedWithUO halfU halfO)
open ProofFile.Honest.K14 (nowSharedBy_at_head six_stops_none)

/-- **The two parts of a test's half are quiet.** -/
theorem quiet_test {V W X : Type} (J : TestJob W X) :
    ∀ p ∈ (proverSideOfProximityTest J : Placed V W X).parts, Quiet p := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · unfold firstPart
    split <;> exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
    · cases hp

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}

/-- **No side of the list stops.** -/
theorem noStop_withUO (hA : P5J.AtMgA o Z D r Zp Np cF x₀) (I : WiderIn W₀) :
    NoStop (sharedWithUO I Zp) := by
  unfold sharedWithUO
  rw [nowSharedBy_at_head hA (I.weights Zp)]
  intro g hg p hp
  rcases List.mem_append.1 hg with hg | hg
  · rcases List.mem_append.1 hg with hg | hg
    · exact six_stops_none _ _ _ _ g hg p hp
    · obtain ⟨J, -, rfl⟩ := List.mem_map.1 hg
      exact quiet_test J p hp
  · obtain ⟨J, -, rfl⟩ := List.mem_map.1 hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact quiet_test J q hq

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.quiet_test
#print axioms ProofFile.Honest.K12.AtFile.noStop_withUO
