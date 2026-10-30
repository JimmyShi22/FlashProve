-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/GammaHeard.lean: the kind "the code switch" (K2): TOOLS FOR THE
TIE BETWEEN THE CHALLENGES THAT AN HONEST PROVER's CLOSING READS OFF ITS LIST OF CHALLENGES HEARD
(`challengesOr0`, Honest/K2/Closing.lean) AND THE CHALLENGES IN THE VERIFIER's CARRIED ROWS.
Statements with their proofs; no definition. Two of the six are closed facts, by the kernel.

  `challenge_of_round` what `challengesOr0` makes of one round's challenge is `readE (drawnOf r)`:
                    what the verifier's text reads of that round (`drawnOf`,
                    Johnson/Prover/Link/FormFold.lean), read in the field: also where the round drew
                    no element: both sides are then the field's 0 as `zeroG` writes it
  `challenges_range` at the n numbers from a on, where the list of rounds R has so many behind its
                    first a: `challengesOr0 (R.map (·.drawn)) (List.range' a n) = (((R.drop a).take
                    n).map drawnOf).map readE`
  `gammaTie_of` THE TIE FROM THREE FACTS: the numbers are a stretch from a on · g has as many
                    entries · g is what R's rounds from a on drew, cut at g's length ⊢
                    `challengesOr0 (R.map (·.drawn)) numbers = g.map readE`
  `roundsAhead_written` where a list of sub-protocols has the written cut (`cutFirstFull`):
                    `roundsAhead bs k` (Johnson/Desc/K13/Honest/FoldCut.lean) is the library's
                    written number `offW k` (Johnson/LPFE1R/RowsQAt.lean)
  `gammaNumbersW` BY THE KERNEL: at each of the 25 written segments (`segsW`,
                    Law/PlacesWritten.lean) the fold's numbers are `List.range' (offW (ixK10 l) + 2)
                    ‹their count›`: a stretch, from the third round of that segment's closing on
  `gammaNumbersW_can_fail` A NEGATIVE LINE: with + 1 in the stead of + 2 it holds at none of the 25

By, the library's: `readE_ofTriple` (OnBytes/Slice/ProgField.lean) · `roundsLen_cut`
(Johnson/Desc/First/CutAtNumbers.lean): how many rounds each sub-protocol declares is the cut's
third field · `offW`, `lensW`, `ixK10`. NEAR, NOT CALLED: inside the proof of `rows_q_at`
(RowsQAt.lean) stands the equation of `roundsAhead_written`, at the first chain and at `ixK10 l`,
with the sum written out · `offs_written` (the same file): these 25 numbers as numerals ·
`inFront355_of_cut`, `inFront_written` (Johnson/Desc/AtSeats/K13PlanM3At.lean): the like count at
355. · `drawnE` (Johnson/Prover/Link/FoldSay.lean): a round's first drawn element read in the field,
as a function of the challenge alone; `readE_drawnOf` (Johnson/Prover/Link/DrawnLaw.lean): `readE
(drawnOf r) = drawnE r.drawn`: so the right side of `challenge_of_round` is `drawnE r.drawn`;
`drawnE_zero`: it is 0 where nothing was drawn.

Limits. Tools and closed facts: no state, no run and no prover's list is named. The negative line
turns one thing, the offset. `gammaNumbersW` says nothing on how many numbers a segment has. The
full size alone (the two closed facts). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K2.Closing
import Johnson.Desc.K13.Honest.FoldCut
import Johnson.Prover.Link.FormFold
import Johnson.LPFE1R.RowsQAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes.Slice (readE toE readE_ofTriple)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K2.Honest (zeroG)
open VerifiableInference.Desc.K13.Honest (roundsAhead)
open VerifiableInference.Desc.LinkJoin (offW lensW)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.Prover.Link (drawnOf)
open LPFK10 (ixK10)

/-- What `challengesOr0` makes of a round's challenge is what the verifier's text reads of that
round, read in the field: also where the round drew no element. -/
theorem challenge_of_round (r : Fmt.RoundView) (l : List Fmt.Drawn) :
    (match (r.drawn :: l).head?.bind (·.elems.head?) with
      | some x => toE x
      | none => zeroG) = readE (drawnOf r) := by
  unfold drawnOf
  rw [readE_ofTriple]
  cases h : r.drawn.elems with
  | nil => simp [h, zeroG]
  | cons x xs => simp [h]

/-- **At a stretch of n numbers from a on, inside the list**: the challenges heard there are the
elements that these rounds drew. -/
theorem challenges_range (R : List Fmt.RoundView) : ∀ (n a : Nat), ((R.drop a).take n).length = n →
    challengesOr0 (R.map (·.drawn)) (List.range' a n) =
      (((R.drop a).take n).map drawnOf).map readE
  | 0, a, _ => by simp [challengesOr0]
  | n + 1, a, h => by
    have ha : a < R.length := by
      rw [List.length_take, List.length_drop] at h
      omega
    have hd : R.drop a = R[a] :: R.drop (a + 1) := List.drop_eq_getElem_cons ha
    have h' : ((R.drop (a + 1)).take n).length = n := by
      rw [List.length_take, List.length_drop] at h ⊢
      omega
    have ih := challenges_range R n (a + 1) h'
    rw [hd, List.take_succ_cons, List.map_cons, List.map_cons, ← ih, List.range'_succ]
    unfold challengesOr0
    rw [List.map_cons, ← List.map_drop, hd, List.map_cons]
    exact congrArg (· :: _) (challenge_of_round R[a] _)

/-- **The tie on the challenges, from three facts**: the numbers are a stretch from a on; the
carried challenges are as many; and they are what the run's rounds from a on drew. -/
theorem gammaTie_of {R : List Fmt.RoundView} {a : Nat} {numbers : List Nat} {g : List OnBytes.E}
    (hnum : numbers = List.range' a numbers.length) (hlen : g.length = numbers.length)
    (hg : g = ((R.drop a).take g.length).map drawnOf) :
    challengesOr0 (R.map (·.drawn)) numbers = g.map readE := by
  have hl : ((R.drop a).take g.length).length = g.length := by
    have := congrArg List.length hg
    rw [List.length_map] at this
    exact this.symm
  rw [hnum, ← hlen, challenges_range R g.length a hl, ← hg]

/-- Where a list of sub-protocols has the written cut: how many rounds its first k have is the
library's written number. -/
theorem roundsAhead_written {St Cl : Type} {bs : List (Block St Cl)}
    (h : cutOf bs = cutFirstFull) (k : Nat) : roundsAhead bs k = offW k := by
  unfold roundsAhead offW lensW
  rw [← h, ← VerifiableInference.Desc.First.roundsLen_cut, List.length_flatMap, List.map_take]

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL**: at each of the 25 written segments the fold's numbers are a stretch, from the
third round of that segment's closing on. -/
theorem gammaNumbersW : ((List.range 25).all fun l =>
    match segsW[l]? with
    | some Sg => Sg.gamma == List.range' (offW (ixK10 l) + 2) Sg.gamma.length
    | none => false) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A NEGATIVE LINE: from the second round on it holds at none. -/
theorem gammaNumbersW_can_fail : ((List.range 25).any fun l =>
    match segsW[l]? with
    | some Sg => Sg.gamma == List.range' (offW (ixK10 l) + 1) Sg.gamma.length
    | none => false) = false := by
  decide +kernel

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.challenge_of_round
#print axioms ProofFile.Honest.K2.Law.challenges_range
#print axioms ProofFile.Honest.K2.Law.gammaTie_of
#print axioms ProofFile.Honest.K2.Law.roundsAhead_written
#print axioms ProofFile.Honest.K2.Law.gammaNumbersW
#print axioms ProofFile.Honest.K2.Law.gammaNumbersW_can_fail
