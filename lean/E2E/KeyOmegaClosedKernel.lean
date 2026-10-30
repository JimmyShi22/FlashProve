-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyOmegaClosedKernel.lean

Four closed questions at the key file's test on G_omega, BY THE KERNEL's OWN EVALUATION, each with a
control. It imports KeyOmegaClosedGuards.lean, where the evaluator says the same first.

  `place_O`, `place_O_bite`   the place that the chain lays at G_omega is `piKOFull`; not at U's numbers
  `opens_O`, `opens_O_sent`, `opens_O_two`   `opensFitB` at depths [22, 13, 13], sources own 1, own
                  2, own 7, and 7 in front; no at 8 in front; no with the fresh tree left out
  `door_O`, `door_O_g`   `Sh.doorB` at O's place and O's one shape; no at a group that is not there
  `three_O`, `three_O_g`, `three_O_bare`   the three tests at the fall-back; no at claims; no at tidy

Limits. Closed numbers and shapes at the copies of `QK` and `PF`. `opens_O` is `OpensFit`'s
test alone: `OldAt` stays false at O, own 7 not being below 7. `door_O` is one Bool of the door;
`door_of_shape_own` asks the marks, plain rows and `claimsB` beside it. `three_O` is the premise of
`three_doorOmegaF`, at the fall-back; the other premises of that law are not here. Nothing on
completeness, on soundness or on what is hidden.
-/
import E2E.KeyOmegaClosedGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light.KeyOmegaClosed
open H2K.Member (piKUFull piKOFull)
open AtPublicFiles.KeyTreesInFront (PF)
open VerifiableInference.Desc.Ground.Sh (stTidyB)
open ProofFile.Honest.Sh (claimsB)

theorem place_O : pKO = piKOFull := by
  first
    | decide +kernel
    | rfl

theorem place_O_bite : H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ PF.U ≠ piKOFull := by
  intro h
  have e : (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ PF.U).nums.free = piKOFull.nums.free :=
    congrArg (fun q => q.nums.free) h
  exact absurd e (by decide +kernel)

theorem opens_O : opensAt true [22, 13, 13] [.own 1, .own 2, .own 7] 7 = true := by decide +kernel

theorem opens_O_sent : opensAt true [22, 13, 13] [.own 1, .own 2, .own 7] 8 = false := by
  decide +kernel

theorem opens_O_two : opensAt true [22, 13] [.own 1, .own 2] 7 = false := by decide +kernel

theorem door_O : doorAt piKOFull shapeO = true := by decide +kernel

theorem door_O_g : doorAt piKOFull { shapeO with g := 99 } = false := by decide +kernel

theorem three_O : threeL fallO = [true, true, true] := by decide +kernel

theorem three_O_g : claimsB { fallO with g := 99 } = false := by decide +kernel

theorem three_O_bare : stTidyB fallBare.st = false := by decide +kernel

end ProofFile.Honest.K12.Light.KeyOmegaClosed

#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.place_O
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.place_O_bite
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.opens_O
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.opens_O_sent
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.opens_O_two
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.door_O
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.door_O_g
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.three_O
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.three_O_g
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.three_O_bare
