-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyTenLinesGuards.lean

The closed lines at the key's test on G_omega, at the written values, by Lean's evaluator, each with a
control but `planU`, a list of public flags. What they decide: whether the premises of the own twins (K12/Own/) can be had at jobKO at all. Each can
say no. KeyTenLinesKernel.lean imports this file.

  `shapeOm`, `fallOm`   the one shape of the door's state; the fall-back
  `bareO`, `msO`        the job at arguments that hold nothing; its members' shapes
  `doorAt`, `planU`     `Sh.doorB` at a place; the premises of `shape_doorOmegaF`, `three_doorOmegaF` as Bools

NOT HERE: the clause pub of `ShapeAsksO`: it reads the state behind the fold, and no Bool on a shape stands for
that at a first fold that sends its own table: `frontPubB` is false there by its mask.

Limits. Evaluations outside the kernel: no theorem. Public numbers and shapes at `QK`, `PF`, `keyBook`. Nothing on
completeness, on soundness or on what is hidden.
-/
import E2E.KeyDoorUClosedGuards
import E2E.KeyBookHeldK12
import Johnson.Desc.ProofFile.Honest.K12.Sim.KeyPlaceFactsOwn
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light.KeyDoorUClosed
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc (Block)
open H2K.Member (piKUFull piKOFull)
open VerifiableInference.Desc.Ground.Sh (stTidyB)
open AtPublicFiles.AtFiles.Full (PF QK)
open AtPublicFiles.KeyBook (atFull keyBook)
open ProofFile.Honest.Sh (TestSh doorB claimsB)
open ProofFile.Honest.K14 (jobU jobOmega)

/-- The one shape of the door's state at G_omega. -/
def shapeOm : TestSh := Desc.K14.Shape.doorO (endOmega QK sentK piKUFull)

/-- The fall-back. -/
def fallOm : T12 := fallOmega QK sentK piKUFull

/-- The job at G_omega at arguments that hold nothing. -/
def bareO : ManyJob Unit Unit :=
  jobAtOmega AQ piKOFull (fun _ _ => noState) (fun _ => ⟨fun _ _ => 0⟩)
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩) none

/-- Its members' shapes. -/
def msO : List MemShape := bareO.mems.map (·.shape)

/-- `Sh.doorB` at a place and a shape. -/
def doorAt (p : P12) (a : TestSh) : Bool :=
  doorB p (stA p) (stN p) (((H2K.JointK.laidOf p).take 1).map (·.1)) (lettersOf p (stA p) (stN p)).i
    ((lettersOf p (stA p) (stN p)).n.code, (lettersOf p (stA p) (stN p)).n.maskCode) a

/-- The public premises of `shape_doorOmegaF` and `three_doorOmegaF` but the eight's planOk: made, split,
sent, masks ahead, the codes' lengths, the test on G_u's plan. -/
def planU : List Bool :=
  [(Desc.K14.blocks QK).isSome, QK.S.sharedSplitNeeded, (Desc.K14.withU QK.S).isSome, QK.S.masksAhead,
    QK.codes.lengthsOk, (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).planOk]

-- Printed, so that each no shows where it stands.
#eval (shapeOm.g, shapeOm.mask, decide (shapeOm.core.st.codes = QK.codes))
#eval doorAt piKOFull shapeOm
#eval threeL fallOm
#eval planU
#eval tsLenOf piKOFull (ProofFile.Honest.Sh.thinOf shapeOm)
#eval frontPlainB₀ piKOFull (ProofFile.Honest.Sh.thinOf shapeOm)
#eval manyFitsS piKOFull msO bareO.trees (ProofFile.Honest.Sh.thinOf shapeOm)
#eval bareO.trees.map (·.1)
#eval (widthFits (jobOmega AQ) 0, widthFits (jobOmega AQ) 1, colFitsOmega AQ piKOFull, freshFitsOmega piKOFull)
#eval atFull fun K => bookCutsOmega (keyBook K) AQ piKOFull

-- OVER THE SHAPE. Foretold: yes.
#guard decide (shapeOm.core.st.codes = QK.codes)
#guard doorAt piKOFull shapeOm
#guard threeL fallOm == [true, true, true]
#guard planU.all id
#guard tsLenOf piKOFull (ProofFile.Honest.Sh.thinOf shapeOm) == 3
#guard frontPlainB₀ piKOFull (ProofFile.Honest.Sh.thinOf shapeOm)
-- Controls: no.
#guard !decide (shapeOm.core.st.codes = ⟨#[], #[]⟩)
#guard !doorAt piKOFull { shapeOm with g := 99 }
#guard !doorAt piKOFull { shapeOm with mask := some 0 }
#guard !claimsB { fallOm with g := 99 }
#guard tsLenOf piKOFull (ProofFile.Honest.Sh.thinOf { shapeOm with g := 99 }) != 3
#guard !frontPlainB₀ piKOFull (ProofFile.Honest.Sh.thinOf { shapeOm with g := 99 })

-- THE JOB AND THE SENDINGS. Foretold: yes. Controls: no.
#guard bareO.trees.map (·.1) == [22, 13, 13]
#guard bareO.trees.map (·.1) != [22, 13, 14]
#guard widthFits (jobOmega AQ) 0 && widthFits (jobOmega AQ) 1
#guard !widthFits (jobOmega AQ) 5
#guard colFitsOmega AQ piKOFull
#guard !colFitsOmega ⟨{ QK with codes := ⟨#[], #[]⟩ }, 0⟩ piKOFull
#guard freshFitsOmega piKOFull
#guard !freshFitsOmega piKUFull

-- THE BOOK. Foretold: yes. Control: the other test's place.
#guard atFull fun K => bookCutsOmega (keyBook K) AQ piKOFull
#guard atFull fun K => !bookCutsOmega (keyBook K) AQ piKUFull

end ProofFile.Honest.K12.Light.KeyDoorUClosed

#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.shapeOm
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.fallOm
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.bareO
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.msO
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.doorAt
#print axioms ProofFile.Honest.K12.Light.KeyDoorUClosed.planU
