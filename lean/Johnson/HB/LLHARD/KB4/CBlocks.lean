-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/CBlocks.lean: conjuncts 2, 3, 4 and 15 of the tests on the plan at WK: all
blocks of the three chains pass their own tests and are shaped; the first chain's last block has a
round. By evaluations in Lean's kernel. Of the shared chain's twelve blocks' own tests WK_shared
evaluates ELEVEN: the front block's is the literal true in WK: it is earned elsewhere (front_W,
CFile.lean; front_of, Pins.lean). Negative tests. On a proximity test's own test: two answers to a
sample at the ranges' test's place, at the folded row's test's and at the own test's (one question,
asked at three places). On a sending's own test: the index-mask message under a mask code that is
not there. On what a lookup's own test asks of its numbers: mu := 7. On "shaped": a sending without
the list of its oracle messages; a lookup's block with a round that sends a root and tells no oracle
message. On the seal: the first chain's last block without its round.
Limits. At the closed description WK (WK.lean) and the written declared rounds alone. That a key
file's description passes the test at any public files is another file's, under named equations.
Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.WK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.KB8 (declKeyFull)

set_option maxRecDepth 1000000 in
theorem WK_first : blocksOk WK.first.blocksInOrder = true := by decide +kernel

theorem WK_shared : blocksOk WK.shared.blocksInOrder = true := by decide +kernel

theorem WK_second : blocksOk WK.second.blocksInOrder = true := by decide +kernel

theorem WK_seal : WK.sealLast = true := by decide +kernel

/-- The ranges' test's block at its place's numbers with two answers to a sample. -/
def rngBent : Block FirstState Claim :=
  rangesTest (enterRanges oneFull) leaveRanges { Johnson.KB8.rangesNumsFull with answers := 2 }

theorem rng_bent : blocksOk [rngBent] = false := by decide +kernel

/-- The later places with two answers to a sample at the folded row's test's place. -/
def laterBentU : LaterPlaces :=
  { Johnson.KB8.laterPlacesFull with U := { Johnson.KB8.laterPlacesFull.U with answers := 2 } }

theorem shared_bent : blocksOk
    ((sharedZ Lk6.AtPlan.keyFull true laterBentU).retype : Chain _ Claim).blocksInOrder = false := by
  decide +kernel

/-- The later places with two answers to a sample at the own test's place. -/
def laterBentW : LaterPlaces :=
  { Johnson.KB8.laterPlacesFull with W := { Johnson.KB8.laterPlacesFull.W with answers := 2 } }

theorem third_bent : blocksOk
    ((thirdZ Lk6.AtPlan.keyFull laterBentW).retype : Chain _ Claim).blocksInOrder = false := by
  decide +kernel

/-- The one-time chain's values with the index-mask message under a mask code that is not there. -/
def oneBentIdx : OnBytes.Params.OneTime :=
  oneAt OnBytes.Params.recordSet.samples
    { Lk6.AtPlan.keyFull.once.input with
      shape := { Lk6.AtPlan.keyFull.once.input.shape with maskCode := 99 } }
    Lk6.AtPlan.keyFull.ranges.x Lk6.AtPlan.keyFull.codes Lk6.AtPlan.keyFull.once.shape

theorem send_bent :
    blocksOk [(sendIndexMasks oneBentIdx pieces [[300]] : Block FirstState Claim)] = false := by
  decide +kernel

theorem face_bent : ((lookupsOf oneFull).any fun x =>
    ({ K3.faceOfLkp x with mu := 7 } : K3.Face).ok) = false := by decide +kernel

theorem shaped_send_bent : blocksOk [{ firstW.first with oracles := [] }] = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem shaped_look_bent : ((lookupsOf oneFull).any fun x =>
    blocksOk [lookBlock ({ name := "LKP", roots := 1 } :: lookE x) Lk6.AtPlan.keyFull.set 0 x]) =
      false := by decide +kernel

/-- A description whose first chain's last block has no round. -/
def WKnoSeal : FileDescription (FirstState × _root_.Desc.K14.St) :=
  { WK with first := { firstW with last := { firstW.last with rounds := [] } } }

theorem seal_bent : WKnoSeal.sealLast = false := by decide +kernel

end Johnson.KB4

#print axioms Johnson.KB4.WK_first
#print axioms Johnson.KB4.WK_shared
#print axioms Johnson.KB4.WK_second
#print axioms Johnson.KB4.WK_seal
#print axioms Johnson.KB4.rng_bent
#print axioms Johnson.KB4.shared_bent
#print axioms Johnson.KB4.third_bent
#print axioms Johnson.KB4.send_bent
#print axioms Johnson.KB4.face_bent
#print axioms Johnson.KB4.shaped_send_bent
#print axioms Johnson.KB4.shaped_look_bent
#print axioms Johnson.KB4.seal_bent
