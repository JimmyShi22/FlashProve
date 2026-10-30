--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/More/RecAtState.lean: THE OPEN SEGMENT's PART OF THE VERIFIER's STATE READS AS THE
PUBLIC PARAMETERS SAY (`RecIs`, Rec/Whole.lean), FROM SIX TESTS WITH CODE AT THAT STATE, ONE
EQUATION AND TWO COUNTS: NO MEANING, NO PROMISE, NO STRING. One statement with its proof: the calls
of Rec/Proofs.lean's ten proofs, at the tests themselves.

  **`recIs_at_state`**: segAt? s = some A · the tests of "frame.liveIs", linkFresh m,
    "K12.seatsCarried", "K12.msgShapes", "frame.sentIs" m, "ledger.treesAre" m accept at s · the
    statement's codes are the plan's · the book has n places and the statement n messages ⟹ `RecIs A
    R n m`.

WHY. The table's row on the public tests alone (no sentence on a witness or a string) has these
tests in hand, not the promise.

Limits. Every premise stands. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing
on soundness.
-/
import Johnson.Road.K4.Rec.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec

open OnBytes
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillSent (sentIsB treesAreB link_of_sentIs whereIs_of_sentIs
  maskAt_of_sentIs trees_of_treesAre)
open VerifiableInference.Desc.First.RecordPlan (seatAt_is rowBits_is placeBits_is)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K12.Door (atFirstSeats atFirstShapes)

/-- **From the six tests, the codes and the two counts: the open segment's part is the plan's.** -/
theorem recIs_at_state {s : S} {A : Part9} {R : RecPlan} {n m : ℕ} (hp : segAt? s = some A)
    (live : (decide (s.live.frame.shape = R.shape) && decide (s.live.rows.layout = R.layout)) =
      true)
    (fresh : ((s.tl?.bind (·.heard)).isNone && s.link?.any fun L => L.arrayOf == R.arrs m) = true)
    (seats : atFirstSeats R.L s = true) (shapes : atFirstShapes R.M s = true)
    (sent : sentIsB R.d m s = true) (trees : treesAreB R.d m s = true)
    (codes : s.st.codes = R.cs) (z1 : s.book.place.size = n) (z2 : s.st.oracles.size = n) :
    RecIs A R n m := by
  obtain ⟨hL, hF, hst, hbk⟩ := part_fields hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at live
  have e : s.live = A.L.check := by
    unfold S.live
    rw [hL]
  rw [e] at live
  simp only [Bool.and_eq_true] at fresh
  have h2 := fresh.2
  rw [hL] at h2
  exact
    { layout := live.2
      shape := live.1
      arrays := by simpa only [Option.any_some, beq_iff_eq] using h2
      link := link_of_sentIs hL sent
      whereIs := whereIs_of_sentIs hL sent
      mask := maskAt_of_sentIs hL sent live.1
      seat := fun own o => by
        rw [hbk]
        exact seatAt_is seats z1 own o
      rowBits := fun o part => by
        rw [hst]
        exact rowBits_is shapes z2 o part
      placeBits := fun o part => by
        rw [hst]
        exact placeBits_is shapes z2 codes o part
      trees := trees_of_treesAre hF trees }

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.recIs_at_state
