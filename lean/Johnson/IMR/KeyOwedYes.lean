-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeyOwedYes.lean: THE CLOSED FACTS OF r6 BUT ONE, DECIDED BY LEAN's KERNEL. owedAll sent:
fifteen sub-protocols of a key file's description at the typed sizes, as beforesOf sees them (place
· one of its rounds draws · «before»): the two lookups', the ranges' test's, the batching's (sent:
the trees in front of it), the shared chain's eight, and the three later proximity tests'. owedW:
the table «owed» at the typed sizes: ten rows. owed_yes: every row of owedW finds its sub-protocol
in owedAll 5. owed_bent: A NEGATIVE TEST: one more row, which asks the batching to name tree 5, W's
own, finds no sub-protocol. looks_zip_ok: the planner's two tests on the two lookups' numbers, along
the numbered list. No soundness.
-/
import Johnson.IMR.KeyOwed
import Johnson.HB.LLHARD.KB8.PinsMet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Johnson.KB8
open Lk6.AtPlan (keyFull)

/-- Fifteen sub-protocols at the typed sizes, as beforesOf sees them. -/
def owedAll (sent : Nat) : List (Place × Bool × List (Nat × Nat)) :=
  ((Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)).zipIdx.map fun x =>
      ((⟨1, some x.2, 2, .K3⟩ : Place), (lookList keyFull.set x.1).any drawsAny,
        [(1, 0), (1, 1)])) ++
    ([((⟨1, none, 5, .K12⟩ : Place), rsR.any drawsAny, H2U.beforeOf 1 rNums),
      (⟨1, none, 13, .K13⟩, (battRoundsOf keyFull.ranges.x keyFull.once.shape).any drawsAny,
        (List.range sent).map fun n => (1, n))] ++
    ((_root_.Desc.K14.blocksOr
        (par14 keyFull ((H2U.beforeOf 3 wNums).filter fun x => x.1 == 1))).map tripOf ++
    [((⟨2, none, 9, .K12⟩ : Place), rsU.any drawsAny, H2U.beforeOf 2 uNums),
      (⟨2, none, 10, .K12⟩, rsO.any drawsAny, H2U.beforeOf 2 oNums),
      (⟨3, none, 2, .K12⟩, declKeyFull.2.2.any drawsAny, H2U.beforeOf 3 wNums)]))

/-- The table «owed» at the typed sizes. -/
def owedW : List (Place × List (Nat × Nat)) :=
  owedFirst keyMade.oneTime ++ owedShared keyMade.oneTime keyFull.once.shape ++
    owedSecond keyMade.oneTime

/-- Block.lean's test of one row against one sub-protocol. -/
def owedAt (r : Place × List (Nat × Nat)) (b : Place × Bool × List (Nat × Nat)) : Bool :=
  b.1 == r.1 && b.2.1 && r.2.all b.2.2.contains

set_option maxRecDepth 1000000 in
theorem owed_yes : (owedW.all fun r => (owedAll 5).any (owedAt r)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: a row that asks the batching to name W's own tree finds no sub-protocol. -/
theorem owed_bent : ((owedW ++ [((⟨1, none, 13, .K13⟩ : Place), [(1, 5)])]).all fun r =>
    (owedAll 5).any (owedAt r)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem owedAll_len : (owedAll 5).length = 15 ∧ owedW.length = 10 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem looks_zip_ok : ((Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)).zipIdx.all
    fun x => lookOk keyFull.set x.1) = true := by decide +kernel

end IM

#print axioms IM.owed_yes
#print axioms IM.owed_bent
#print axioms IM.owedAll_len
#print axioms IM.looks_zip_ok
