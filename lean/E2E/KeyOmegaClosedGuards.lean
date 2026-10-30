-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyOmegaClosedGuards.lean

Four closed questions at the key file's test on G_omega, by Lean's evaluator, each with a control.
KeyOmegaClosedKernel.lean imports this file, so that the kernel is asked only where the evaluator has
said yes. Each can say no.

  `nO`, `pKO`    the later places' numbers at G_omega, and the place that the chain lays from them
  `sentK`, `shapeO`, `fallO`   at the written value `QK` and the place `piKUFull`: what goes out
                  with o_u, the one shape of the door's state (`shape_doorOmegaF`), the fall-back
  `doorAt`        `Sh.doorB` at a place and a shape, with the batching's round and the codes'
                  numbers of that place
  `opensAt`       `opensFitB` at `piKOFull`, its rounds, and given word, depths, sources and count
  `threeL`        the three tests at a state, as a list, so that a no names its test

Limits. No control bites `stPlainB` alone: a row with a written-out factor is not one line. Evaluations outside the kernel: no theorem. `QK` and `PF` are copies
(KeyTreesInFrontGuards.lean). All of this is of public numbers and shapes; no state of a run. A yes
at `fallO` holds of the fall-back: it is the premise of `three_doorOmegaF`, not a statement on the
verifier's state. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyTreesInFrontGuards
import Johnson.Desc.ProofFile.Honest.K12.DoorsByShape
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.ProofFile.Honest.K12.PlanB
import Johnson.Desc.K12.Law.PlacesKeyFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light.KeyOmegaClosed
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc (Block)
open H2K.JointK (laidOf)
open H2K.Member (piKUFull piKOFull)
open VerifiableInference.Desc.Ground.Sh (stTidyB stPlainB)
open AtPublicFiles.KeyTreesInFront (PF QK)
open ProofFile.Honest.Sh (TestSh doorB claimsB)

/-- The later places' numbers at the test on G_omega. -/
def nO : H2U.PlaceNums := PF.O.getD PF.U

/-- The place that the chain lays from them. -/
def pKO : P12 := H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO

/-- What goes out with o_u at the written value. -/
def sentK : Array OnBytes.OracleNotice := sentOf QK.S

/-- The one shape of doorOmegaF's state at the written value. -/
def shapeO : TestSh := Desc.K14.Shape.doorO (endOmega QK sentK piKUFull)

/-- The fall-back of doorOmegaF at the written value. -/
def fallO : T12 := fallOmega QK sentK piKUFull

/-- `Sh.doorB` at a place and a shape. -/
def doorAt (p : P12) (a : TestSh) : Bool :=
  doorB p (stA p) (stN p) (((laidOf p).take 1).map (·.1)) (lettersOf p (stA p) (stN p)).i
    ((lettersOf p (stA p) (stN p)).n.code, (lettersOf p (stA p) (stN p)).n.maskCode) a

/-- `opensFitB` at the place's stages and rounds. -/
def opensAt (own : Bool) (depths : List ℕ) (src : List Fmt.TreeSource) (sent : ℕ) : Bool :=
  opensFitB own piKOFull.nums.stages (proximityTestKind guardedProximityTestParts piKOFull : Block T12 Unit).rounds depths src sent

/-- The three tests at a state: tidy, plain, claims. -/
def threeL (t : T12) : List Bool := [stTidyB t.st, stPlainB t.st, claimsB t]

/-- The fall-back with no oracle message in its statement. -/
def fallBare : T12 := { fallO with st := { fallO.st with oracles := #[] } }

-- Printed, so that each no shows where it stands.
#eval (PF.O.isSome, pKO.nums.free, pKO.nums.ownMask, pKO.oracles.length, pKO.answers)
#eval (shapeO.g, shapeO.mask)
#eval threeL fallO
#eval threeL { fallO with g := 99 }
#eval threeL fallBare
#eval doorAt piKOFull shapeO
#eval doorAt piKOFull { shapeO with g := 99 }
#eval doorAt piKOFull { shapeO with mask := some 0 }
#eval doorAt piKUFull shapeO
#eval opensAt true [22, 13, 13] [.own 1, .own 2, .own 7] 7

-- THE PLACE, field by field. Foretold: yes. Control: U's numbers at O's address.
#guard PF.O.isSome
#guard pKO.nums.stages == piKOFull.nums.stages && pKO.nums.free == piKOFull.nums.free &&
  pKO.nums.ownMask == piKOFull.nums.ownMask && pKO.idx == piKOFull.idx &&
  pKO.before == piKOFull.before && pKO.answers == piKOFull.answers
#guard (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ PF.U).nums.free != piKOFull.nums.free

-- THE OPENINGS. Foretold: yes at the true arguments. Controls: one tree more in front; another
-- depth; another source; the other word; the fresh tree left out.
#guard opensAt true [22, 13, 13] [.own 1, .own 2, .own 7] 7
#guard !opensAt true [22, 13, 13] [.own 1, .own 2, .own 7] 8
#guard !opensAt true [21, 13, 13] [.own 1, .own 2, .own 7] 7
#guard !opensAt true [22, 13, 13] [.own 0, .own 2, .own 7] 7
#guard !opensAt false [22, 13, 13] [.own 1, .own 2, .own 7] 7
#guard !opensAt true [22, 13] [.own 1, .own 2] 7

-- THE DOOR's BOOL. Foretold: yes at O's shape. Controls: a group that is not there; a mask named;
-- U's place against O's shape.
#guard doorAt piKOFull shapeO
#guard !doorAt piKOFull { shapeO with g := 99 }
#guard !doorAt piKOFull { shapeO with mask := some 0 }
#guard !doorAt piKUFull shapeO

-- THE THREE AT THE FALL-BACK. Foretold: yes. Controls: a group that is not there says no at claims;
-- a statement with no oracle message says no at tidy.
#guard threeL fallO == [true, true, true]
#guard !claimsB { fallO with g := 99 }
#guard !stTidyB fallBare.st

end ProofFile.Honest.K12.Light.KeyOmegaClosed

#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.nO
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.pKO
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.sentK
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.shapeO
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.fallO
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.doorAt
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.opensAt
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.threeL
#print axioms ProofFile.Honest.K12.Light.KeyOmegaClosed.fallBare
