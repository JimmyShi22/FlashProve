-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/Row.lean: a key file's description that is made of the full size's values
declares the written rounds; so `writtenOf` lays its declared rounds as the written dry lists, and
its table's depth is 32. These are the two last premises (r8, r8') of `IM.keyBack_of_rows`
(Johnson/IMR/KeyBackOfRows.lean, which is not imported here), the theorem whose premises together
make `Key.keyDataAndDecisionOfPlannerAnswer` return. They are proved here under named equations on just what these two read
of X, N and P.

Main names.
  `Pins X N P`: what the declared rounds read of X, N and P, as equations with typed and written
    values (`keyFull`, Johnson/Goal/PlanValues/KeySizedReturns.lean; Written.lean in this folder).
  `decl_full`: under them (Key.descriptionFromSource X N P).roundsDeclaredByBlocks = declKeyFull.
  `r8_of_pins`: so writtenOf "key file" (Key.descriptionFromSource X N P).roundsDeclaredByBlocks = .ok dryKeyFull.
  `r8'_of_lin`: (Key.descriptionFromSource X N P).tableDepth = 32, where the shared chain's shape as read is the
    typed one.

Who is to prove each premise (none is proved here).
  set, sized: they follow from `Key.sourceOf m = .ok X` (`sourceOf_parts`: X.set is the sized key's
    setting, Johnson/RunOne/Law/KeyInScope.lean; `sourceOf_chains`: X.chains = m.p.chains,
    Johnson/RunOne/KeyRowsInScope.lean) and "in scope the sized key is keyFull" (`key_in_scope`,
    KeyInScope.lean), with no yes of a test on the plan. These files are not imported here: what is
    said of their theorems rests on a reading of their statements, not on a call.
  ranges, lin, idx, codes, and `r8'_of_lin`'s premise: values as read back from the parameter bytes.
    The two theorems at hand that give them (`five_in_scope`, `shared_lin_in_scope`, same file) take
    (Key.descriptionFromSource X N P).planOk = true. The test planOk reads the declared rounds AND the table's depth
    (`FileDescription.planOkCore`, Johnson/Desc/Block.lean). SO WHOEVER USES `decl_full` OR `r8'_of_lin` TO
    SHOW planOk MUST HAVE THESE FIVE FROM ELSEWHERE: from a law on reading back what was written.
  nC, nN: whoever shows `Key.rangesNumbers m = .ok N`. uC, uN, o, wC, wN: whoever shows
    `Key.laterPlaces m = .ok P`. THESE PREMISES ASK MORE THAN "IT RETURNS": THEY SAY WHICH NUMBERS.
    Whoever proves them needs beside the sized key that the sized setting is the typed one
    (m.p.chains.made.sized.set = recordSet): the work, and a term of the rows, read that setting.

Limits. No theorem in this file or in the files that it imports shows that an X, N, P that comes of
public files meets the premises. What other files show of that, and with what limits, is said under
"Limits" in the head of PinsMet.lean in this folder. Nothing on the tests on
the plan. That `dryKeyFull` is what the program's dry runs state is not said (see the head of
Johnson/G/DryKeyLit.lean). Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB8.AtFull
import Johnson.HB.LLHARD.KB8.WrittenFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.G Johnson.G.OfPlan
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)

/-- **What the declared rounds read of X, N and P, as equations.** -/
structure Pins (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) : Prop where
  /-- the setting -/
  set : X.set = keyFull.set
  /-- of the one-time chain's public values, as read: the item "ranges" -/
  ranges : X.Y.k.oneTime.ranges = keyFull.ranges.x
  /-- as read: the shape of the test on the table -/
  lin : X.Y.k.oneTime.lin = keyFull.once.shape
  /-- as read: the index-mask message -/
  idx : X.Y.k.oneTime.indexMasks = keyFull.once.input
  /-- as read: the codes -/
  codes : X.Y.k.oneTime.codes = keyFull.codes
  /-- the planner's sized key -/
  sized : X.chains.made.sized.key = keyFull
  /-- the ranges' test's place: its chain -/
  nC : N.chain = 1
  /-- the numbers that its rounds are made of -/
  nN : N.nums = rNums
  /-- the folded row's test's place: its chain -/
  uC : P.U.chain = 2
  /-- the numbers that its rounds are made of -/
  uN : P.U.nums = uNums
  /-- Omega's test has a place; its chain; the numbers that its rounds are made of -/
  o : ∃ O, P.O = some O ∧ O.chain = 2 ∧ O.nums = oNums
  /-- the own test's place: its chain -/
  wC : P.W.chain = 3
  /-- the numbers that its rounds are made of -/
  wN : P.W.nums = wNums

/-- **A description that is made of the full size's values declares the written rounds.** -/
theorem decl_full {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : Pins X N P) :
    (descriptionFromSource X N P).roundsDeclaredByBlocks = declKeyFull := by
  obtain ⟨O, hO, hOc, hOn⟩ := h.o
  have kR : (K12.proximityTestKind K12.guardedProximityTestParts (rangesParams N) : Block K12.T12 Claim).rounds = rsR :=
    k12_rounds_at K12.guardedProximityTestParts (place := rangesPlace) (x := N) h.nC.symm
      (by rw [h.nN]; exact some_R)
  have kU : (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) :
      Block K12.T12 Unit).rounds = rsU :=
    k12_rounds_at K12.guardedProximityTestParts h.uC.symm (by rw [h.uN]; exact some_U)
  have kO : (P.O.toList.flatMap fun nO =>
      (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block K12.T12 Unit).rounds) =
      rsO := by
    rw [hO]
    show (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ O) :
      Block K12.T12 Unit).rounds ++ [] = rsO
    rw [List.append_nil]
    exact k12_rounds_at K12.guardedProximityTestParts hOc.symm (by rw [hOn]; exact some_O)
  have kW : (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) :
      Block K12.T12 Unit).rounds = declKeyFull.2.2 :=
    k12_rounds_at K12.guardedProximityTestParts h.wC.symm (by rw [h.wN]; exact third_full)
  rw [decl_eq, kR, kU, kO, kW, h.set, h.ranges, h.lin, h.idx, h.codes, h.sized, first_full,
    shared_full]

/-- **r8**: `writtenOf` lays the description's declared rounds as the written dry lists. -/
theorem r8_of_pins {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : Pins X N P) :
    writtenOf "key file" (descriptionFromSource X N P).roundsDeclaredByBlocks = .ok dryKeyFull := by
  rw [decl_full h]
  exact written_full

/-- **r8'**: the table's depth. -/
theorem r8'_of_lin {X : Source} (N : H2U.PlaceNums) (P : LaterPlaces)
    (h : X.Y.k.shared.lin = keyFull.once.shape) : (descriptionFromSource X N P).tableDepth = 32 := by
  show X.Y.k.shared.lin.fold.index.tree.a = 32
  rw [h]
  exact depth_full

end Johnson.KB8

#print axioms Johnson.KB8.decl_full
#print axioms Johnson.KB8.r8_of_pins
#print axioms Johnson.KB8.r8'_of_lin
