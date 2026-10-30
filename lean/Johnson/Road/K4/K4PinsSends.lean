-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsSends.lean: THE FIRST CHAIN's ORACLE MESSAGES' SHAPES AND SEATS AT THE WRITTEN
SENDINGS, IN A FORM THAT LEAN's KERNEL CAN EVALUATE. `msgsOfChain`
(Johnson/Desc/K12/Door/MsgShapes.lean) and `laidAtCodes` (Johnson/Desc/K12/Door/LaidAt.lean) sort
the sendings by their entries with `List.mergeSort`, which the kernel does not reduce. The written
list (`Johnson.G.proofSendsFull`, Johnson/G/SendsWritten.lean) stands in that order already. Two
definitions and seven theorems: three by the kernel.

  `sends_sorted`: sorting the written first chain's sendings leaves them as they stand: by
    `List.mergeSort_of_pairwise`; that the entries ascend: by the kernel. NEGATIVE:
    `sends_sorted_no`: read backwards they do not.
  `mW`, `laidW?`: the shapes, and the listed seats with the trees' shapes, without the sorting.
  `msgs_sorted`, `laid_sorted`: they are `msgsOfChain` and `laidAtCodes` at the written sendings.
  `msgs_at`, `laid_at`: under `WrittenAt Z` they are the closed parameters' own
    (`(P5J.At.d12 Z L).M`, `P5J.At.laid? Z`, Johnson/P5J/LettersAt2.lean).
  `sends_counts`: BY THE KERNEL: 199 shapes; the seats are listed, 199 of them, in 83 trees.

Limits. K04_law IS NOT PROVED BY THIS. `WrittenAt Z` IS A PREMISE: a condition on the three public
files alone. The written sendings rest on prints of Lean's evaluator (their file's head). The full
size alone.
-/
import Johnson.Road.K4.K4PlanTied
import Johnson.P5J.LettersAt2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.K12.Door (msgsOf msgsOfChain laidOf laidAtCodes)
open Johnson.G (proofSendsFull)

set_option maxRecDepth 1000000 in
/-- Sorting the written sendings by their entries leaves them as they stand. -/
theorem sends_sorted :
    (proofSendsFull.1.sends.mergeSort fun a b => decide (a.entry ≤ b.entry)) =
      proofSendsFull.1.sends :=
  List.mergeSort_of_pairwise (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- A negative test: read backwards the entries do not ascend. -/
theorem sends_sorted_no :
    ¬ proofSendsFull.1.sends.reverse.Pairwise fun a b => decide (a.entry ≤ b.entry) = true := by
  decide +kernel

/-- The written shapes of the first chain's oracle messages, in the order of sending. -/
def mW : List OnBytes.OracleShape := msgsOf (proofSendsFull.1.sends.map (·.sent))

/-- The written list of their seats, with the trees' shapes. -/
def laidW? : Option VerifiableInference.Desc.K12.Door.Laid :=
  laidOf proofSizedFull.codes (proofSendsFull.1.sends.map (·.sent))

theorem msgs_sorted : msgsOfChain proofSendsFull.1 = mW := by
  unfold msgsOfChain mW
  rw [sends_sorted]

theorem laid_sorted : laidAtCodes proofSizedFull.codes proofSendsFull.1 = laidW? := by
  unfold laidAtCodes laidW?
  rw [sends_sorted]

variable {Z : ProofFile.Pub} (W : WrittenAt Z)
include W

/-- Under `WrittenAt Z` the closed parameters' list of shapes is the written one. -/
theorem msgs_at (L : VerifiableInference.Desc.K12.Door.Laid) : (P5J.At.d12 Z L).M = mW := by
  show msgsOfChain Z.made.proof.1 = mW
  rw [W.proof]
  exact msgs_sorted

/-- Under `WrittenAt Z` the closed parameters' reader of the listed seats returns the written
list. -/
theorem laid_at : P5J.At.laid? Z = laidW? := by
  show laidAtCodes Z.made.p.chains.proof.first.codes Z.made.proof.1 = laidW?
  rw [show Z.made.p.chains.proof.first.codes = proofSizedFull.codes from W.codes, W.proof]
  exact laid_sorted

omit W in
set_option maxRecDepth 1000000 in
/-- By the kernel: how many shapes, seats and trees. -/
theorem sends_counts :
    (mW.length, laidW?.map fun L => (L.places.length, L.shapes.length)) =
      (199, some (199, 83)) := by
  decide +kernel

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sends_sorted
#print axioms OnBytes.Road.K4.sends_sorted_no
#print axioms OnBytes.Road.K4.msgs_sorted
#print axioms OnBytes.Road.K4.laid_sorted
#print axioms OnBytes.Road.K4.msgs_at
#print axioms OnBytes.Road.K4.laid_at
#print axioms OnBytes.Road.K4.sends_counts
