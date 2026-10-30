-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/StepsAtKey.lean: at the key file's book of coins (`keyBook`,
E2E/KeyBook.lean), at the full size's written sizes, the frame's laying of the steps of the test on
the ranges returns, at all coins of that book, at every job at the written place `piKRFull`
(Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean) that has the members and the word on the fresh table
of the key file's skeleton (`jobRanges`, E2E/KeyTestSizes.lean), at every block that seats the test.
The proof goes through one function to Bool, `laysB` (StepsReturn.lean in this folder, whose head
lists its clauses on the book and the job), which is true there by an evaluation in Lean's kernel
(`decide +kernel`). For what: the frame's `ready` computes the rounds of a run by `chainSteps`, at
each chain's whole list of blocks, and returns an error where `chainSteps` does. The main theorem
holds at every job, block and list of prover's sides that meet its hypotheses, and at all types S,
Cl, V, W and X. One computable definition, three theorems with their proofs, and two evaluations
(`#guard`).

Terms. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean. A book (`ProverCoinCounts`) is public data that
goes with a description: for each chain a table of the parts that have coins of their own, each with
its count (`ProverCoinCounts.rowsOf`: chain number 0 is the first chain, number 1 the shared one); the entries
(`Ahead`); and for each place the cut, that is how many rounds each of its parts has. `Coins B` is
the type of the coins of one run at the book B. The laying of the steps is `chainSteps`: from a
book, a chain's table, that chain's coins by address (`Coins.look`), a list of blocks (`Block`,
Johnson/Desc/Block.lean: a sub-protocol at its place) and a list of prover's sides (`Placed`: a
place with a list of parts, `Part`) it computes the chain's rounds (`Step`), or an error. It returns
where its value is `.ok`. A job (`TestJob`, Test.lean in this folder) is what a caller supplies for
a proximity test. Its field `p` (`P12`, Johnson/Desc/K12/Frame.lean) holds the test's numbers, among
them the list of stages `p.nums.stages` and `p.place` (`Place`, Johnson/Desc/Block.lean: chain,
link, piece and kind); both `p` and `p.place` are called the place. `piKRFull` is a closed term of
the type `P12`, meant to be the place of the key file's proximity test on the ranges at the full
size (see the limits). `members` lists the oracle messages of the test's group (`jobRanges` lists
one); `fresh`, the word on the fresh table, names the sender of the first fold's fresh table, or is
`none`. The half is `proverSideOfProximityTest J` (Parts.lean in this folder): the prover's side at `J.p.place` with
the two parts `firstPart J` and `restPart J`. A block b seats the test where
`SeatOf b J enter leave` holds (SaysYesSeat.lean in this folder): b has the place, the rounds and
the oracle messages of the test's own block `proximityTestKind guardedProximityTestParts J.p`, and its decision is `enter`, then
that block's decision, then `leave`. The written sizes are `keyFull`
(Johnson/Goal/PlanValues/KeySizedReturns.lean). `fullPub` (E2E/KeyBookAtWritten.lean) is what
`KeyPub.of` returns at them, an `Option KeyPub`. `atFull f` (the same file) is f at the value of
`fullPub`, and false where `fullPub` is `none`.

  `full_lays`: `laysB` is true at the book of the written sizes, in the first chain, at `jobKR`. In
    Lean: `atFull (fun K => laysB (keyBook K) 0 jobKR) = true`
  `steps_ranges`: so, at every such job and every block that seats the test, with the half at the
    place: at all coins the row of the two parts is lent its coins and the laying returns the half's
    steps. In Lean, under the hypotheses below, at every `k : Coins (keyBook K)` and `v : Option V`:
    there is a c such that `lendRow` (the frame), at the table `(keyBook K).rowsOf 0`, the coins
    `k.look 0`, the place `J.p.place` and the list `[firstPart J, restPart J]`, is `.ok c`, and
    `chainSteps`, at the same table and coins, v, the list of one block `[b]` and hs, is
    `.ok ((proverSideOfProximityTest J).steps b v c)`
  `laysB_congr`: `laysB B ch J = laysB B ch J'` for two jobs, also of different types, whose fields
    `p`, `members` and `fresh` are equal: of a job `laysB` reads only these three
  `jobKR`: a definition: `jobRanges` with its field `p` replaced by `piKRFull`. Its other three
    fields are constant functions (`skeleton`, E2E/KeyTestSizes.lean)

The two `#guard` lines are negative tests: `laysB` at `jobKR` is false at `keyBook K false` in chain
number 0, and at `keyBook K` in chain number 1.

By what. `steps_ranges` is `lays_of_B` (StepsReturn.lean) at `keyBook K` and chain number 0. Of that
theorem's hypotheses, `laysB (keyBook K) 0 J = true` is rewritten by `laysB_congr` to the same at
`jobKR`, which is `full_lays` unfolded at hK; that the job has two stages or more follows from
`2 ≤ piKRFull.nums.stages.length`, by `decide +kernel`. `full_lays`: `decide +kernel` on closed
terms. `laysB_congr`: by cases on the two jobs and on `fresh`, after which both sides are one term
(`rfl`).

Hypotheses of `steps_ranges`. hK: `fullPub = some K`. hp: `J.p = piKRFull`. hm, hf: the job's
`members` and `fresh` are those of `jobRanges`. hb: `SeatOf b J enter leave`, at any `enter` and
`leave`. hh: the first prover's side in hs whose place is `J.p.place` is `proverSideOfProximityTest J`.

Limits.
- At written values: `piKRFull`, `jobRanges` and `keyFull` are closed terms. By the limits of
  E2E/KeyTestSizes.lean no theorem ties the members, the senders or the counts of `jobRanges` to the
  description.
- Some of `piKRFull`'s numbers are a print's word: for these the print of a run of Lean's evaluator
  is trusted. The limits of Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean name them.
- The book's carried entries are a proposal: see the limits of E2E/KeyBook.lean. In Lean they are
  `K.carried`, which `keyBook K false` leaves out.
- That the part which sends the member message takes the book's row for it, and reads the message at
  that stretch, is not shown here.
- That the key file's description has such a block at that place, with these numbers, is not shown
  here. `seatOf_ranges` (SeatRanges.lean in this folder) has the form:
  `SeatOf` holds of the block `rangesTest laid back N` at every job whose field `p` is
  `rangesParams N`.
- `chainSteps` is taken at the one block b: nothing is stated on a chain's whole list of blocks.
- hh is a hypothesis: no list of prover's sides is built here.
- A `#guard` is an evaluation by Lean's evaluator, outside the kernel: it leaves no theorem.
- By reading, both negative tests leave the tests (1) to (5) of `laysB` true, as the head of
  StepsReturn.lean numbers them. By `full_lays` the five are true at `keyBook K` in chain number 0.
  (1) and (2) read the job only. `keyBook K false` has the tables and the cuts of `keyBook K`, and
  of its entries only `K.spent`. No row of the first or of the shared chain's table has a part's
  number from 2 on. Which of (6) to (8) is false at either test is not evaluated. Negative tests for
  (3), (5) and (8), by reading, lie in StepsToy.lean in this folder, at one small made-up book. (1),
  (2) and (4) have no negative test.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.StepsReturn
import Johnson.Desc.K12.Law.PlaceKeyRangesFull
import E2E.KeyBookHeldK12

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open AtPublicFiles.KeyBook (atFull keyBook fullPub KeyPub)
open AtPublicFiles.KeyTest (jobRanges)
open H2K.Member (piKRFull)

variable {S Cl V W X W' X' : Type}

/-- `jobRanges` (E2E/KeyTestSizes.lean) with its field `p` replaced by `piKRFull`. -/
def jobKR : TestJob Unit Unit := { jobRanges with p := piKRFull }

/-- Of a job `laysB` reads only the fields `p`, `members` and `fresh`: it is equal at two jobs, also
of different types, that agree in these three. -/
theorem laysB_congr (B : ProverCoinCounts) (ch : ℕ) (J : TestJob W X) (J' : TestJob W' X') (hp : J.p = J'.p)
    (hm : J.members = J'.members) (hf : J.fresh = J'.fresh) : laysB B ch J = laysB B ch J' := by
  cases J with
  | mk p ms fresh r ro tr =>
    cases J' with
    | mk p' ms' fresh' r' ro' tr' =>
      obtain rfl : p = p' := hp
      obtain rfl : ms = ms' := hm
      obtain rfl : fresh = fresh' := hf
      cases fresh <;> rfl

set_option maxRecDepth 100000 in
theorem full_lays : atFull (fun K => laysB (keyBook K) 0 jobKR) = true := by decide +kernel

/-- **At the key file's book the laying of the steps of the test on the ranges returns.** In Lean:
`lendRow` at the list of the two parts and `chainSteps` at the one block b (both: the frame) are
`.ok`, at every `k : Coins (keyBook K)`. The head explains the terms and lists the hypotheses. -/
theorem steps_ranges (K : KeyPub) (hK : fullPub = some K) (J : TestJob W X) (hp : J.p = piKRFull)
    (hm : J.members = jobRanges.members) (hf : J.fresh = jobRanges.fresh) (b : Block S Cl)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hb : SeatOf b J enter leave) (hs : List (Placed V W X))
    (hh : (hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)) (k : Coins (keyBook K))
    (v : Option V) :
    ∃ c, lendRow (keyBook K) ((keyBook K).rowsOf 0) (k.look 0) J.p.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c ∧
      chainSteps (keyBook K) ((keyBook K).rowsOf 0) (k.look 0) v [b] hs =
        .ok ((proverSideOfProximityTest J).steps b v c) := by
  have hB : laysB (keyBook K) 0 J = true := by
    rw [laysB_congr (keyBook K) 0 J jobKR hp hm hf]
    have h := full_lays
    unfold atFull at h
    rw [hK] at h
    exact h
  obtain ⟨s, t, rest, hst⟩ : ∃ s t rest, J.p.nums.stages = s :: t :: rest := by
    rw [hp]
    have h2 : 2 ≤ piKRFull.nums.stages.length := by decide +kernel
    cases h : piKRFull.nums.stages with
    | nil =>
      rw [h] at h2
      exact absurd h2 (by decide)
    | cons s l =>
      cases l with
      | nil =>
        rw [h] at h2
        exact absurd h2 (by simp)
      | cons t rest => exact ⟨s, t, rest, rfl⟩
  exact lays_of_B (keyBook K) 0 (Or.inl rfl) J s t rest hst hB b enter leave hb hs hh k v

-- Negative: the book without its carried entries; in the shared chain's table
-- (`laysB` at `jobKR` is false at `keyBook K false`, and at `keyBook K` in chain number 1).
#guard atFull fun K => !laysB (keyBook K false) 0 jobKR
#guard atFull fun K => !laysB (keyBook K) 1 jobKR

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.laysB_congr
#print axioms ProofFile.Honest.K12.full_lays
#print axioms ProofFile.Honest.K12.steps_ranges
#print axioms ProofFile.Honest.K12.jobKR
