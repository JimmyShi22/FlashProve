-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyDoorUClosedGuards.lean

The closed lines at the key's test on G_u that Accepted at 9 asks, by Lean's evaluator, each with a control.
KeyDoorUClosedKernel.lean imports this file, so that the kernel is asked only where the evaluator has said
yes. Those over doorU (endOf QK sentK) are the ones that the kernel may not bear. Each can say no.

  sentK, shapeU, fallUK   what goes out with o_u at QK, the door's shape, the fall-back
  AQ, bareU      the public data at QK; the job at G_u at arguments that hold nothing
  msU            the shapes of the job's members
  threeL, opensAtU, roomU, hpB   the tests, as Bools

Limits. Evaluations outside the kernel: no theorem. Public numbers and shapes at QK, PF: nothing of a run, no
door's value. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorsByShape
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape
import Johnson.Desc.ProofFile.Honest.K12.ManyFits
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.ProofFile.Honest.K12.TieAtRun
import Johnson.Desc.ProofFile.Honest.K12.TableIsColumn
import Johnson.Desc.ProofFile.Honest.K12.JobShared
import Johnson.Desc.K12.Law.PlacesKeyFull
import E2E.KeyShapeSharedFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light.KeyDoorUClosed
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc (Block)
open H2K.Member (piKUFull piKOFull)
open VerifiableInference.Desc.Ground.Sh (stTidyB stPlainB)
open AtPublicFiles.AtFiles.Full (PF QK)
open ProofFile.Honest.Sh (TestSh claimsB)
open ProofFile.Honest.K14 (SendPub jobU jobOmega sendingsFit)

/-- What goes out with o_u at QK. -/
def sentK : Array OnBytes.OracleNotice := sentOf QK.S

/-- The one shape of the door at G_u at QK. -/
def shapeU : TestSh := Desc.K14.Shape.doorU (endOf QK sentK)

/-- The fall-back. -/
def fallUK : T12 := fallU QK sentK

/-- The public data at QK. -/
def AQ : SendPub := ⟨QK, 0⟩

/-- The job at G_u at arguments that hold nothing. -/
def bareU : ManyJob Unit Unit :=
  jobAtU AQ piKUFull (fun _ _ => noState) (fun _ => ⟨fun _ _ => 0⟩)
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩) none

/-- Its members' shapes. -/
def msU : List MemShape := bareU.mems.map (·.shape)

/-- The three tests at a state. -/
def threeL (t : T12) : List Bool := [stTidyB t.st, stPlainB t.st, claimsB t]

/-- opensFitB at the place's stages and rounds. -/
def opensAtU (own : Bool) (depths : List ℕ) (src : List Fmt.TreeSource) (sent : ℕ) : Bool :=
  opensFitB own piKUFull.nums.stages (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).rounds depths src sent

/-- hroom of tree0_lent_U. -/
def roomU : Bool :=
  decide (2 * (stage₀ piKUFull).k + 1 ≤ (stage₀ piKUFull).h + (stage₀ piKUFull).Z.l)

/-- hp of three_doorUF: the eight are there and each plans. -/
def hpB : Bool := ((Desc.K14.blocks QK).map fun bs => bs.all (·.planOk)).getD false

-- Printed, so that each no shows where it stands.
#eval (decide (shapeU.core.st.codes = QK.codes), shapeU.g, shapeU.mask)
#eval frontFiveB piKUFull QK.codes shapeU
#eval tsLenOf piKUFull (ProofFile.Honest.Sh.thinOf shapeU)
#eval threeL fallUK
#eval manyFitsS piKUFull msU bareU.trees (ProofFile.Honest.Sh.thinOf shapeU)
#eval bareU.trees.map (·.1)
#eval opensAtU false [24, 13] [.own 0, .own 2] 3
#eval ellsB AQ
#eval sendingsFit QK
#eval (widthFits (jobU AQ) 0, widthFits (jobOmega AQ) 1)
#eval ((stage₀ piKUFull).k, (stage₀ piKUFull).h, (stage₀ piKUFull).Z.l, roomU)
#eval hpB

-- THE LINES. Foretold: yes.
#guard frontFiveB piKUFull QK.codes shapeU
#guard manyFitsS piKUFull msU bareU.trees (ProofFile.Honest.Sh.thinOf shapeU)
#guard tsLenOf piKUFull (ProofFile.Honest.Sh.thinOf shapeU) == 2
#guard threeL fallUK == [true, true, true]
#guard opensAtU false [24, 13] [.own 0, .own 2] 3
#guard ellsB AQ
#guard sendingsFit QK
#guard widthFits (jobU AQ) 0 && widthFits (jobOmega AQ) 1
#guard roomU
#guard bareU.trees.map (·.1) == [24, 13]
#guard hpB

-- CONTROLS. Foretold: no.
#guard !frontFiveB piKOFull QK.codes shapeU
#guard !frontFiveB piKUFull QK.codes { shapeU with mask := none }
#guard !manyFitsS piKUFull msU bareU.trees.dropLast (ProofFile.Honest.Sh.thinOf shapeU)
#guard !manyFitsS piKUFull msU.dropLast bareU.trees (ProofFile.Honest.Sh.thinOf shapeU)
#guard tsLenOf piKUFull (ProofFile.Honest.Sh.thinOf { shapeU with g := 99 }) != 2
#guard !claimsB { fallUK with g := 99 }
#guard !stTidyB { fallUK with st := { fallUK.st with oracles := #[] } }.st
#guard !opensAtU false [24, 13] [.own 0, .own 2] 4
#guard !opensAtU false [23, 13] [.own 0, .own 2] 3
#guard !opensAtU false [24, 13] [.own 1, .own 2] 3
#guard !opensAtU true [24, 13] [.own 0, .own 2] 3
#guard !ellsB (planOf ⟨#[], #[]⟩ default)
#guard !sendingsFit { QK with codes := ⟨#[], #[]⟩ }
#guard !widthFits (jobU AQ) 5 && !widthFits (jobOmega AQ) 5
#guard decide (2 * (stage₀ piKUFull).k + 1 > (stage₀ piKUFull).h)
#guard bareU.trees.map (·.1) != [24, 14]
#guard ((Desc.K14.blocks QK).map (·.length)) == some 8

end ProofFile.Honest.K12.Light.KeyDoorUClosed

#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.sentK
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.shapeU
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.fallUK
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.AQ
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.bareU
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.msU
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.threeL
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.opensAtU
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.roomU
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.hpB
