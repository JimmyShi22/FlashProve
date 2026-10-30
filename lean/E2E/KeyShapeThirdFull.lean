--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeThirdFull.lean: THE KEY FILE's THIRD CHAIN ON SHAPES, FROM THE SHAPE THAT ITS START
RETURNS AT THE TWO EARLIER CHAINS' LAST TERMS: the run over all four sub-protocols returns, at the
full size's written public values; and in the goals' scope at the description that the verifier
runs. Evaluations in Lean's kernel, and a join. Guards on shapes: NOTHING IS SHOWN OF ANY PROVER.

  `A0`, `x0_some`: the third chain's first shape: what E2E/KeyShapeSharedFull.lean's `X0` holds.
  **`yes₃_full`**: the run of E2E/KeyShapeChain.lean's letters `Z₃`, with E2E/KeyShapeOwn.lean's
    `gOwn` at the written later places' own test, over the four returns from `A0`. By Lean's kernel.
      (E2E/KeyShapeOwn.lean's `yes_four` has the like from a synthetic shape.)
  **`yes₃_sourced`**: in scope, at the letters at the description's own public values.
  **`first₃_shape`**: at two states of the two earlier runs' last shapes, what the description's
    start returns has the shape `A0`.

Limits.
- (B2) at the own proximity test is not served: `gOwn` asks fewer guards than the test.
- What E2E/KeyShapeSharedFull.lean and E2E/KeyShapeThirdStart.lean say under their Limits holds here
  too.


-/
import E2E.KeyShapeThirdStart
import E2E.KeyShapeOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open ProofFile.Honest
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces ownTest)
open _root_.Desc.K14 (St)

/-- The third chain's first shape at the two earlier chains' last terms. -/
def A0 : Sh₃ := X0.getD aF

theorem x0_some : X0 = some A0 := by
  have h : X0.isSome = true := door_full
  unfold A0
  cases e : X0 with
  | none => rw [e] at h; cases h
  | some a => rfl

/-- **The run over the third chain's four sub-protocols returns from that shape.** -/
theorem yes₃_full (v : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    (Z₃ SF (ownTest PF).rounds (gOwn (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ PF.W)) v).yes A0 4 = true := by
  show (Z₃ SF (ownTest PF).rounds (gOwn (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ PF.W))
    fun _ _ _ => true).yes A0 4 = true
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **In scope, at the letters at the description's own public values.** -/
theorem yes₃_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (v : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    (Z₃Own X P v).yes A0 4 = true := by
  obtain ⟨-, -, hlin, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  have hS : X.chains.made.sized.key.once.shape = SF := hlin.symm.trans (six_sourced hs scope).lin
  obtain rfl := later_sourced hs scope
  show (Z₃ X.chains.made.sized.key.once.shape (ownTest PF).rounds
    (gOwn (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ PF.W)) v).yes A0 4 = true
  rw [hS]
  exact yes₃_full v

/-- **What the start returns at two states of the two runs' last shapes has that shape.** -/
theorem first₃_shape (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (v : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (x : (keyFileDescription X N P).XiPub) (e₁ : FirstState) (e₂ : St)
    (h1 : sh₁B (pubOf X) CF e₁ = T19) (h2 : sh₂ e₂ = V12) (s₃ : S₃)
    (h : (keyFileDescription X N P).start₃ x e₁ e₂ = .ok s₃) : (Z₃Own X P v).sh s₃ = A0 := by
  obtain ⟨s, a, b⟩ := start₃_of_shapes hs scope x e₁ e₂ h1 h2
  rw [h] at a
  obtain rfl := Except.ok.inj a
  rw [x0_some] at b
  exact (Option.some.inj b).symm

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.x0_some
#print axioms AtPublicFiles.AtFiles.Full.yes₃_full
#print axioms AtPublicFiles.AtFiles.Full.yes₃_sourced
#print axioms AtPublicFiles.AtFiles.Full.first₃_shape
