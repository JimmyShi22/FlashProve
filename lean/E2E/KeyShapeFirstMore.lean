-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFirstMore.lean: THREE SMALL THINGS ON THE KEY FILE's FIRST CHAIN's LETTERS. Statements
and proofs. Guards on shapes and named tests: NOTHING IS SHOWN OF ANY PROVER.

  **`rng_early`**: a negative test at the ranges' test's guard: one term early (in front of
    "rng.0.rows") it rejects. By Lean's kernel.
  **`enters15`**: under E2E/KeyShapeFullTies.lean's six equations `entersB` accepts `T15`. By Lean's
    kernel.
  `snd_six`, **`vals_off`**: under E2E/KeyShapeFullTies.lean's six equations: the named tests in a
    row, written out; so at every number but 15 and 16 the named test on values asks nothing.
    **`vals_sourced`**: in scope, at the description that the verifier runs.

Limits.
- `rng_early` does not say which clause rejects. By the guard's text it is `entersB`'s third (the
  group holds no row in front of "rng.0.rows"), and `guardK12` behind it is not reached: so it is a
  negative test of `entersB`. `guardK12` is seen to reject at none of the chain's own terms.


-/
import E2E.KeyShapeFirstAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open H2K.Member (nKRFull)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces lookupsOf)

/-- **A negative test at the turned guard**: one term early. -/
theorem rng_early : (gRng QF nKRFull T14).toOption.isSome = false := by decide +kernel

/-- **What the ranges' test's seat asks of the chain's state holds on the term in front of that
test**, under the six equations. By Lean's kernel. -/
theorem enters15 {Q : Pub1} (h : Six Q) : entersB Q T15 = true := by
  have e : entersB Q T15 = entersB QF T15 := by
    have e0 : Q = ⟨Q.one, Q.set⟩ := rfl
    have e1 : entersB ⟨Q.one, Q.set⟩ T15 = entersB ⟨normOne Q.one, Q.set⟩ T15 := rfl
    rw [e0, e1, norm_six h, h.set]
    rfl
  rw [e]
  decide +kernel

/-- Under the six equations: the named tests on values, in a row. -/
theorem snd_six {Q : Pub1} (h : Six Q) (cs : Codes) (D : List Fmt.DeclaredRound)
    (told : List ProofFile.Root) (N : H2U.PlaceNums) (v : Val FirstState) :
    (gvAll₁ Q cs D told N v).map (·.2) =
      List.replicate 15 vT ++ [v, vKeys Q, vT, vT] := by
  have hl : (lookupsOf Q.one).length = 2 := by
    rw [lookups_norm, norm_six h]
    decide +kernel
  unfold gvAll₁
  simp only [List.map_cons, List.map_append, List.map_nil, List.map_flatMap, List.map_map]
  rw [flat_range (fun i => (gLink (Bk := BackSh) Q i).map
    ((fun x : (Sh₁B → Except String Sh₁B) × Val FirstState => x.2) ∘ fun g => (g, vT)))
    (lookupsOf Q.one) 0, hl]
  rfl

/-- **At every number but 15 and 16 the named test asks nothing.** -/
theorem vals_off {Q : Pub1} (h : Six Q) (cs : Codes) (D : List Fmt.DeclaredRound)
    (told : List ProofFile.Root) (N : H2U.PlaceNums) (j : Nat) (h15 : j ≠ 15) (h16 : j ≠ 16)
    (s : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (Z₁A Q cs D told N).vals j s rs gs = true := by
  show vOf ((gvAll₁ Q cs D told N (vRng N)).map (·.2)) j s rs gs = true
  rw [snd_six h]
  unfold vOf
  by_cases hj : j < 19
  · interval_cases j <;> first | rfl | exact absurd rfl h15 | exact absurd rfl h16
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj)]
    rfl

/-- In scope, at the description that the verifier runs. -/
theorem vals_sourced {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) (cs : Codes) (j : Nat)
    (h15 : j ≠ 15) (h16 : j ≠ 16) (s : FirstState) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (Z₁A (pubOf X) cs X.Y.D.1 X.Y.told.1 N).vals j s rs gs = true :=
  vals_off (six_sourced hs scope) cs _ _ N j h15 h16 s rs gs

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.rng_early
#print axioms AtPublicFiles.AtFiles.Full.enters15
#print axioms AtPublicFiles.AtFiles.Full.snd_six
#print axioms AtPublicFiles.AtFiles.Full.vals_off
#print axioms AtPublicFiles.AtFiles.Full.vals_sourced
