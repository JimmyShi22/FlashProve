-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MarkReads.lean: THE MARK AT THE OWN ROUNDS OF AN ATTENTION
SEGMENT (kind K5) FOR THE WEIGHTS OF TWO OF ITS TABLES, AS A TERM OF THE STRUCTURE `Mark`
(Johnson/Desc/ProofFile/Honest/Law/Marks.lean), with what a count takes of it and with what its
silence gives.

The event: at one of 2 lt + ls of the segment's own rounds (`readRounds`,
Johnson/Desc/K5/Honest/Law/ReadRounds.lean) the one element drawn is 0 or 1 (or its words are not
below the prime). The verifier refuses nothing there: each of these rounds may draw 0. Where it does
not happen, the closed list of tables in front of the segment's batching holds, on the matrices NAs
and NAs + 3, one table each no entry of whose weights is the word 0.

Main names:
  `mkReads`: **the mark.** place: the member. test: of the member's own challenges alone; it does
    not read those in front. share: A WRITTEN PAIR OF NUMBERS, NO BOUND: 2 for each listed round,
    over the number of field elements, with the factor that a count at strings of hash blocks bears,
    in the form that such a count is meant to take.
  `mkReads_walk`, `mkReads_drop`: it speaks only where the test on one round says yes at a listed
    round: in the two forms in which two laws on a mark's measure take that sentence. The first at
    this kind's copy of the walk `anyBad` (Johnson/Desc/K5/Honest/Law/MarkForm.lean): that it is the
    other law's constant is owed where both are imported.
  `mkReads_share`: the share with the list's length written out.
  `mkReads_silent`: where it is silent and the list has all listed rounds, `k5Reads` says yes.
  `mkReads_live`: **WHAT ITS SILENCE GIVES, AT THE STATE IN FRONT OF THE BATCHING** (`Live2`,
    Johnson/Desc/K5/Honest/Law/LiveToBatch.lean).

Limits. NO SENTENCE ON A MEASURE STANDS HERE: nothing holds the share against the test. The test on
one round and what it says of a field element: `bad01`, `bad01_elem`
(Johnson/Desc/K5/Honest/Law/MarkTest.lean); the listed rounds' draws: `read_round`, `read_draws`
(ReadEntries.lean, MarkForm.lean). `mkReads_live` is conditional as `live_at_batch`: under the
library's one head on the public input, at the full size alone; two matrices of the segment's.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Law.Marks
import Johnson.Desc.K5.Honest.Law.MarkForm
import Johnson.Desc.K5.Honest.Law.LiveToBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (Geo)
open H2K5.Honest (readRounds readRounds_length k5Reads speaks bad01 anyBad speaks_anyBad speaks_drop
  reads_of_silent Chal Reads Live2 live_at_batch)
open P5J (AtMgA TS)

/-- **The mark.** l: the segment's number in the first chain. x: the plan's numbers of its own
rounds. g: the numbers as the verifier's claims read them. -/
def mkReads (l : ℕ) (x : OnBytes.Params.AttentionRounds) (g : Geo) : Mark where
  place := ⟨1, some l, 3, .K5⟩
  test := fun _ own =>
    if speaks x g own then some "a challenge that two tables' weights are made of is 0 or 1"
    else none
  share := ⟨2 * (readRounds x g).length * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩

/-- The mark's test speaks just where `speaks` says yes. -/
theorem mkReads_test (l : ℕ) (x : OnBytes.Params.AttentionRounds) (g : Geo)
    (fr own : List Fmt.Drawn) : ((mkReads l x g).test fr own).isSome = speaks x g own := by
  show (if speaks x g own then some _ else none : Option String).isSome = _
  cases speaks x g own <;> rfl

/-- **It speaks only where the walk over all the member's challenges meets a listed round at which
the test on one round says yes.** No premise. -/
theorem mkReads_walk (l : ℕ) (x : OnBytes.Params.AttentionRounds) (g : Geo) :
    ∀ fr own, ((mkReads l x g).test fr own).isSome = true →
      anyBad bad01 (fun i => decide (i ∈ readRounds x g)) 0 own = true := by
  intro fr own h
  rw [mkReads_test] at h
  exact speaks_anyBad h

/-- The same by the cut of one entry out of the list. No premise. -/
theorem mkReads_drop (l : ℕ) (x : OnBytes.Params.AttentionRounds) (g : Geo) :
    ∀ fr own, ((mkReads l x g).test fr own).isSome = true →
      ∃ r ∈ readRounds x g, ((own.drop r).take 1).any bad01 = true := by
  intro fr own h
  rw [mkReads_test] at h
  exact speaks_drop h

/-- The share with the list's length written out. -/
theorem mkReads_share (l : ℕ) (x : OnBytes.Params.AttentionRounds) (g : Geo) :
    (mkReads l x g).share =
      ⟨2 * (2 * g.lt + g.ls) * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ := by
  show (⟨2 * (readRounds x g).length * (2 ^ 128 + 1) ^ 3, _⟩ : Odds) = _
  rw [readRounds_length]

/-- Where it is silent, and the list has all the listed rounds, the test on the rounds says yes.
Conditional: hlen; h. -/
theorem mkReads_silent (l : ℕ) {x : OnBytes.Params.AttentionRounds} {g : Geo}
    (zk : Array (Array E)) {fr own : List Fmt.Drawn}
    (hlen : ∀ n ∈ readRounds x g, n < own.length) (h : (mkReads l x g).test fr own = none) :
    k5Reads x g ⟨zk, own⟩ = true := by
  refine reads_of_silent zk hlen ?_
  rw [← mkReads_test l x g fr own, h]
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **WHAT THE MARK's SILENCE GIVES, AT THE STATE IN FRONT OF THE BATCHING.** Conditional: as
`live_at_batch` (the head; hg; ea; which five members; their yes, each at its own rounds); own: the
challenges of the first's rounds: hc: they hold what these rounds drew; hlen: all listed rounds are
among them; hs: the mark is silent at them, whatever stands in front. -/
theorem mkReads_live {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s4 s5 s6 s7 s8 s9 : S}
    {rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d4 : b4.decide s4 rs4 gs4 = .ok s5) (d5 : b5.decide s5 rs5 gs5 = .ok s6)
    (d6 : b6.decide s6 rs6 gs6 = .ok s7) (d7 : b7.decide s7 rs7 gs7 = .ok s8)
    (d8 : b8.decide s8 rs8 gs8 = .ok s9) (zk : Array (Array E)) {fr own : List Fmt.Drawn}
    (hc : Reads ⟨zk, own⟩ rs4)
    (hlen : ∀ n ∈ readRounds a.own (Att.P.parCOf a).geo, n < own.length)
    (hs : (mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo).test fr own = none) :
    Live2 (Att.P.parCOf a).geo s9 :=
  live_at_batch h hg ea f4 f5 f6 f7 f8 d4 d5 d6 d7 d8 ⟨zk, own⟩ hc
    (mkReads_silent (2 * g + 1) zk hlen hs)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.mkReads_test
#print axioms ProofFile.Honest.K5.mkReads_walk
#print axioms ProofFile.Honest.K5.mkReads_drop
#print axioms ProofFile.Honest.K5.mkReads_share
#print axioms ProofFile.Honest.K5.mkReads_silent
#print axioms ProofFile.Honest.K5.mkReads_live
