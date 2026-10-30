-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/PubKept.lean: SIX PUBLIC TESTS ON THE VERIFIER's STATE RIDE OVER A YES OF
K4's BLOCK: each says at the state behind what it says at the state in front. Statements and proofs.

What K4's yes leaves is Rest s s' (Johnson/Desc/First/K4/ReadsAtS.lean):
seven of the state's nine fields; four readers of a link; a layers' link stays one. WHAT EACH TEST
READS OF THE STATE:
  weightsB (Johnson/Desc/First/Pend/WeightsB.lean): S.rows: WHICH SORT OF PLACE "here" IS, and the
    pile out.pending (at the members' place: the one row off the claim). So Rest alone does not
    carry it: it is asked that the chain stands in a layers' link in front.
  atFirstBook ft (Johnson/Desc/K12/Door/DoorBools.lean): book, roots.
  atFirstSeats L (the same file): book.
  atFirstShapes M (Johnson/Desc/K12/Door/MsgShapes.lean): st.
  indexIsC n (Johnson/Desc/K13/PubK13.lean): out.
  indexThereC (the same file): st, out.
None reads the link's ledger, what was heard, or the debt of rows.

  `weightsB_kept`, `atFirstBook_kept`, `atFirstSeats_kept`, `atFirstShapes_kept`, `indexIsC_kept`,
  `indexThereC_kept`: one a test.
No new argument: each text unfolded, the fields rewritten.
**Limits.** One premise: Rest s s'; for weightsB one more: s.here = .lay a. Both are had behind a
yes of K4's block (heard_reads, ReadsAtS.lean): not called here. EQUATIONS OF Bools: no test is said
to say yes anywhere. Nothing on soundness. K04_law, the law of K4's block itself, IS NOT PROVED. Met
through Lean at no member.


-/
import Johnson.Desc.First.K4.ReadsAtS
import Johnson.Desc.First.Pend.WeightsB
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Desc.K13.PubK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Riders

open OnBytes
open VerifiableInference.Desc.First (S LayOwn weightsB weightsB_same)
open VerifiableInference.Desc.K12.Door (Laid atFirstBook atFirstSeats atFirstShapes)
open VerifiableInference.Desc.K13 (indexIsC indexThereC)

variable {s s' : S}

/-- Every weight vector of every row on the table passes its test: in a layers' link. -/
theorem weightsB_kept {a : LayOwn} (ha : s.here = .lay a) (R : Rest s s') :
    weightsB s' = weightsB s := by
  obtain ⟨a', ha', _⟩ := R.here a ha
  refine weightsB_same ?_
  simp only [S.rows, ha, ha', R.out]

theorem atFirstBook_kept (R : Rest s s') (ft : Nat) : atFirstBook ft s' = atFirstBook ft s := by
  unfold atFirstBook
  rw [R.book, R.roots]

theorem atFirstSeats_kept (R : Rest s s') (L : Laid) : atFirstSeats L s' = atFirstSeats L s := by
  unfold atFirstSeats
  rw [R.book]

theorem atFirstShapes_kept (R : Rest s s') (M : List OracleShape) :
    atFirstShapes M s' = atFirstShapes M s := by
  unfold atFirstShapes
  rw [R.st]

theorem indexIsC_kept (R : Rest s s') (n : Nat) : indexIsC n s' = indexIsC n s := by
  unfold indexIsC
  rw [R.out]

theorem indexThereC_kept (R : Rest s s') : indexThereC s' = indexThereC s := by
  unfold indexThereC
  rw [R.st, R.out]

end OnBytes.Desc.First.K4.Riders

#print axioms OnBytes.Desc.First.K4.Riders.weightsB_kept
#print axioms OnBytes.Desc.First.K4.Riders.atFirstBook_kept
#print axioms OnBytes.Desc.First.K4.Riders.atFirstSeats_kept
#print axioms OnBytes.Desc.First.K4.Riders.atFirstShapes_kept
#print axioms OnBytes.Desc.First.K4.Riders.indexIsC_kept
#print axioms OnBytes.Desc.First.K4.Riders.indexThereC_kept
