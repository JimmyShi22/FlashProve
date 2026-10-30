-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5WrittenShape.lean: **WHERE THE COMPARISON madeRow ACCEPTS, THE TEST "oneShape" ON THE COMPOSED MEANING's LIST OF MEMBERS (P5J.At.ms, Johnson/P5J/LettersAt.lean) IS A TERM WITHOUT A LETTER.** Kind-free.
The test (oneShapeB, Door/Law/K5MemOfSome.lean: any two members at one seat have one shape) reads of a member its shape and its seat: no radius. plain_membersR (Johnson/P5T/MembersByMake.lean) says that the
list of these pairs is made off the plan's seats alone; these are the written ones (pseats_written, Door/Law/K5Written.lean).
madeRow's accept IS A PREMISE HERE: the verifier's list of entry tests does not ask it in its prefix that Johnson/Desc/Laid/ProofAsksFirstEightTests.lean pins (asksAt1); in its prefix that ProofAsksFirstThirteenTests.lean, beside it, pins (asksAt2) it does.

Main names:
  oneShapeP L: the test on a plain list of pairs (shape, seat). oneShapeB_map: oneShapeB ms is oneShapeP at the members' pairs.
  oneShapeW: the test at the written values. **oneShape_written**: under the head AtMg and madeRow's accept, at every layout file's bytes lay: oneShapeB (At.ms Zp lay) = oneShapeW.
  oneShape_of_written: so oneShapeW = true gives the test's accept at every such head.
IS IT EMPTY HERE? Equations under the head and one Bool. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/); THAT oneShapeW IS true IS NOT SHOWN: IT HAS BEEN EVALUATED NOWHERE.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5Written
import Johnson.Desc.First.Att.Door.Law.K5MemOfSome
import Johnson.P5J.PlanOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (Mem seatOf msOf)
open VerifiableInference.PlanWritten (madeRow)
open OnBytes.Maker (WholeD)
open Johnson.G (proofSendsFull)
open P5J (AtMg TS)

/-- The test on a plain list of pairs (shape, seat): any two at one seat have one shape. -/
def oneShapeP (L : List (OnBytes.OracleShape × (ℕ × ℕ))) : Bool :=
  L.all fun y => L.all fun y' => !decide (y.2 = y'.2) || decide (y.1 = y'.1)

/-- The test reads of a member its shape and its seat alone. -/
theorem oneShapeB_map (ms : List Mem) : oneShapeB ms = oneShapeP (ms.map fun x => ((x.1.l.get x.2).1, seatOf x)) := by
  simp only [oneShapeB, oneShapeP, List.all_map, Function.comp_def]

/-- **The test at the written values.** No letter. -/
def oneShapeW : Bool :=
  oneShapeP ((List.range proofSendsFull.1.sends.length).flatMap fun k => (P5T.mineAt pseatsW k).map fun p => (p.shape, p.seat))

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **THE TEST ON THE COMPOSED MEANING's MEMBERS IS THE TEST AT THE WRITTEN VALUES.** -/
theorem oneShape_written (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true) (lay : ByteArray) :
    oneShapeB (P5J.At.ms Zp lay) = oneShapeW := by
  rw [oneShapeB_map, P5J.At.ms_is]
  unfold P5J.At.members oneShapeW
  rw [P5T.plain_membersR, pseats_written h hm, (made_row_gives hm).2]

/-- So one evaluation serves every head at which the comparison accepts. -/
theorem oneShape_of_written (hW : oneShapeW = true) (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true) (lay : ByteArray) :
    oneShapeB (P5J.At.ms Zp lay) = true :=
  (oneShape_written h hm lay).trans hW

end

end H2K5.Door

#print axioms H2K5.Door.oneShapeB_map
#print axioms H2K5.Door.oneShape_written
#print axioms H2K5.Door.oneShape_of_written
