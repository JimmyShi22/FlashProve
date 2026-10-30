-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/LaidWritten.lean: the two lists that the tests on the list of rounds of the
sub-protocols K13 and K1 read under the letters L and M, as closed terms at the written values of
the proof file at the full size: L, the oracle messages' seats (tree, part) with the trees' shapes;
M, the oracle messages' shapes.

Row or tool. Two definitions and closed facts on them. None of the named tests is stated here: this
file gives them two of their arguments. No law on a sub-protocol is named.

The arguments, their written terms and their ties.
  `Z.first.codes`: `Johnson.G.codesFull2` (Johnson/G/PackLit.lean). Tie: `first_in_scope` with
    `codes_written`: through Lean.
  `Z.made.proof.1`, the first chain's list of sendings: `Johnson.G.proofSendsFull.1`
    (Johnson/G/SendsWritten.lean). Tie: the test that holds the made lists to the written ones:
    being typed by its owner
    (Where this and lean/THEOREM.md differ, the page holds.); here a premise of `laid_at`.

What is here.
  `sentFull`: what the 82 written sendings send, in the written order. `LFull`: what `laidOf
    codesFull2 sentFull` (Johnson/Desc/K12/Door/DoorBools.lean) returns, or the empty pair of lists.
    `MFull`: `msgsOf sentFull` (Johnson/Desc/K12/Door/MsgShapes.lean). Both are stated over the
    written list as it stands, so that no evaluation has to unfold a sort.
  `sends_sorted`, `sends_sort`: the written sendings stand in the order of their entries, so sorting
    them leaves them as they stand. `laidOf_written`: the layout is made, so `LFull` is no
    fall-back. `laid_written`, `msgs_written`: `laidAtCodes codesFull2 proofSendsFull.1 = some
    LFull` (Johnson/Desc/K12/Door/LaidAt.lean), and `msgsOfChain proofSendsFull.1 = MFull`.
  `laid_sizes`: 82 sendings; 199 seats; 83 trees; 199 shapes: none of the lists is empty.
  `laid_rejects`: the negative test: with the first sending left out the layout has not the 199
    seats that `laid_sizes` counts. (At an empty table of codes `decide` could not settle the like
    test: the term did not reduce to yes or no: tried once.)
  `laid_at`, `msgs_at`: wherever a public part has the written codes and the written first list of
    sendings, its L is `some LFull` and its M is `MFull`. By rewriting.
By evaluations in Lean's kernel (`decide +kernel`): `sends_sorted`, inside `laidOf_written`,
`laid_sizes`, `laid_rejects`.

Limits. The written list of sendings stands on the prints that its own head names. Nothing on
soundness.


-/
import Johnson.Desc.K12.Door.LaidAt
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.G.SendsWritten
import Johnson.G.PackLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes Johnson.G
open VerifiableInference.Desc.K12.Door (Laid laidOf laidAtCodes msgsOf msgsOfChain)

/-- What the first chain's written sendings send, in the written order. -/
def sentFull : List (List OracleNotice) := proofSendsFull.1.sends.map (·.sent)

/-- **L at the written values**: laid over the written list as it stands. -/
def LFull : Laid := (laidOf codesFull2 sentFull).getD {}

/-- **M at the written values.** -/
def MFull : List OracleShape := msgsOf sentFull

/-- The written sendings stand in the order of their entries. -/
theorem sends_sorted :
    proofSendsFull.1.sends.Pairwise fun a b => decide (a.entry ≤ b.entry) = true := by
  decide +kernel

/-- So sorting them by their entries leaves them as they stand. -/
theorem sends_sort :
    (proofSendsFull.1.sends.mergeSort fun a b => decide (a.entry ≤ b.entry)) =
      proofSendsFull.1.sends :=
  List.mergeSort_of_pairwise sends_sorted

/-- **The layout is made**: `LFull` is no fall-back. -/
theorem laidOf_written : laidOf codesFull2 sentFull = some LFull := by
  have h : (laidOf codesFull2 sentFull).isSome = true := by decide +kernel
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.1 h
  unfold LFull
  rw [hL]
  rfl

/-- **It is what `laidAtCodes` returns at the written codes and sendings.** -/
theorem laid_written : laidAtCodes codesFull2 proofSendsFull.1 = some LFull := by
  unfold laidAtCodes
  rw [sends_sort]
  exact laidOf_written

/-- And `MFull` is what `msgsOfChain` returns there. -/
theorem msgs_written : msgsOfChain proofSendsFull.1 = MFull := by
  unfold msgsOfChain
  rw [sends_sort]
  rfl

/-- 82 sendings; 199 seats; 83 trees; 199 shapes. -/
theorem laid_sizes :
    proofSendsFull.1.sends.length = 82 ∧ LFull.places.length = 199 ∧ LFull.shapes.length = 83 ∧
      MFull.length = 199 := by decide +kernel

/-- **The negative test**: with the first sending left out the layout has not the 199 seats that
`laid_sizes` counts. -/
theorem laid_rejects :
    ((laidOf codesFull2 sentFull.tail).any fun L => L.places.length == 199) = false := by
  decide +kernel

/-- Wherever the codes and the first list of sendings are the written ones, L is `some LFull`. -/
theorem laid_at {cs : Codes} {c : ChainSends} (hc : cs = codesFull2) (hs : c = proofSendsFull.1) :
    laidAtCodes cs c = some LFull := by
  rw [hc, hs]
  exact laid_written

/-- And M is `MFull`. -/
theorem msgs_at {c : ChainSends} (hs : c = proofSendsFull.1) : msgsOfChain c = MFull := by
  rw [hs]
  exact msgs_written

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.sends_sorted
#print axioms VerifiableInference.Desc.K13.Law.sends_sort
#print axioms VerifiableInference.Desc.K13.Law.laidOf_written
#print axioms VerifiableInference.Desc.K13.Law.laid_written
#print axioms VerifiableInference.Desc.K13.Law.msgs_written
#print axioms VerifiableInference.Desc.K13.Law.laid_sizes
#print axioms VerifiableInference.Desc.K13.Law.laid_rejects
#print axioms VerifiableInference.Desc.K13.Law.laid_at
#print axioms VerifiableInference.Desc.K13.Law.msgs_at
