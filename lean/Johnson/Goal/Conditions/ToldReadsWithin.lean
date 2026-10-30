-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/ToldReadsWithin.lean: the two public readings of a description
(`readConfig`, Ladder.lean, then `readMoreAt recordGround`, Ladder/ReadThru.lean) ask at most eight
queries.

Why. The fit of a description to a told record (`ToldAt`, Johnson/PV/Fit.lean) asks, in its field
`hq₀`, a bound on the queries of the description's readings. Ladder/ReadThru.lean gives no bound for
its `askList`; Johnson/PV/Describe.lean proves both bounds for `Fit.askList`, a copy on the library's
`andThen`.

Main names (namespace `VerifierAndGoals.Told`): `queryBound_askListL`; `within8_pub8`: the two readings
chained by the library's `andThen` (the shape of `hq₀`): one query, then at most seven
(`par7_length`, Johnson/Top/KeyTree.lean).

Limits. A bound on the number of queries only; nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Ladder.ReadThru
import Johnson.PV.Fit
import Johnson.Top.KeyTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifierAndGoals.Told
open VerifierAndGoals VerifiableInference VerifiableInference.OnPublicFiles Rom
open OnBytes.K.Arm.Pub OnBytes.Tie

/-- `askList l` asks at most as many queries as l is long. -/
theorem queryBound_askListL : ∀ l : List BitString, (askList l).toRandomized.QueryBound l.length
  | [] => trivial
  | s :: l => fun a => by
      have h := queryBound_andThen (askList l)
        (fun r => (DeterministicAlgorithm.done (a :: r) : DeterministicAlgorithm (List Digest)))
        l.length 0 (queryBound_askListL l) fun _ => trivial
      rw [← Fit.andThen_eq] at h
      simpa using h

/-- The two readings ask at most eight queries. -/
theorem within8_pub8 (Z : PublicFiles) :
    ((readConfig Z).andThen fun c => (readMoreAt recordGround Z c).andThen fun m =>
      (.done (c, m) : DeterministicAlgorithm D8)).toRandomized.QueryBound 8 := by
  refine queryBound_andThen (readConfig Z) _ 1 7 (fun _ => trivial) fun c => ?_
  have hl : (ssOf (par7 recordGround Z.pol Z.KL Z.lay) c).length ≤ 7 := by
    unfold ssOf
    rw [List.length_map]
    exact TypedOracleCompiler.Compile.Batch.Cms.par7_length recordGround Z.pol Z.KL Z.lay _
  have h := queryBound_andThen (readMoreAt recordGround Z c)
    (fun m => (DeterministicAlgorithm.done (c, m) : DeterministicAlgorithm D8))
    7 0 (queryBound_mono_det _ _ _ hl (queryBound_askListL _)) fun _ => trivial
  simpa using h

end VerifierAndGoals.Told

#print axioms VerifierAndGoals.Told.queryBound_askListL
#print axioms VerifierAndGoals.Told.within8_pub8
