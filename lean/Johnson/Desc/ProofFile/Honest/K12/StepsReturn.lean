-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/StepsReturn.lean: the frame's `chainSteps`
(Johnson/Desc/ProofFile/Honest/Frame.lean) returns a list of steps, and not an error, at the list of
one block b that has a proximity test's place, rounds and oracle messages and whose decision is the
test's between two functions `enter` and `leave` (`SeatOf`, SaysYesSeat.lean in this folder), where
the prover's side at that place is `proverSideOfProximityTest J` (Parts.lean in this folder), at all coins of the
book. The hypothesis on the book and the job is one test, `laysB`, a Bool. It reads the book, the
chain's number and, of the job J, the fields `p`, `members` and `fresh` only (`laysB_congr`,
StepsAtKey.lean in this folder). Proved in the first and in the shared chain. Two definitions,
neither marked `noncomputable`, and three theorems.

Why. The conditions `PlaysOn` and `SaysYes` (Johnson/Desc/ProofFile/Honest/Law/ThreadC.lean) have
among their hypotheses that `chainSteps` returns at the list of the one block. Where it returns an
error, both hold vacuously.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean; `chainSteps`, `lendRow`, `dueAt`
and the types that are named here without a file are its own. A block (`Block`,
Johnson/Desc/Block.lean) is a sub-protocol at one place (`Place`) of a description's chain. A part
(`Part`) is the prover's side of consecutive rounds of a sub-protocol, with one move for each round.
It states three things: a count (`takes`) and two lists of names and counts (`spends`, `carries`). A
half (`Placed`) is the prover's side of a sub-protocol: a place and a list of parts. That list is
"the row" in the entry of `chainSteps_one`; everywhere else a row is a row of a table of the book. A
step (`Step`) is one round of a chain as the frame's `play` meets it. "The laying" is the call of
`chainSteps`: from a chain's list of blocks and a list hs of halves it computes the chain's steps,
or an error. At a block with a half it makes five tests and then calls `lendRow`, which returns what
the parts of the list are given (`RowCoins`), or an error. A book (`ProverCoinCounts`) is public data that goes
with a description. It has a table for each chain (`B.rowsOf ch`), whose rows are an address
(`Addr`: a place, and a part's number there, from 0) and a count (`Due`: a number for each of the
two fields); entries (`Ahead`), each with an owner, a spender, a start and a count; and cuts: for a
place, each part's number of rounds. `Coins B` is the type of the coins of one run, and `k.look ch`
is what chain number ch may be given, by address. v (`Option V`) is what a part's second stop may
read. The job J (`TestJob`, Test.lean in this folder) is what a caller supplies for its test. `J.p`
(`P12`, Johnson/Desc/K12/Frame.lean) has the test's parameters, among them its place `J.p.place` and
its stages `J.p.nums.stages`. The test's own block is `proximityTestKind guardedProximityTestParts J.p` (`proximityTestKind`:
Johnson/Desc/K12/Frame.lean; `guardedProximityTestParts`: Johnson/Desc/K12/JoinGuarded.lean), taken here as a
`Block T12 Unit`. `proverSideOfProximityTest J` has the two parts `firstPart J` and `restPart J` at the place
`J.p.place`. A block "seats the test" where `SeatOf` holds of it, and the half "stands at the place"
where the hypothesis hf below holds.

  `lays_of_B`: two stages or more · the chain is the first or the shared one · `laysB` · the block
    seats the test · the half stands at the place ⟹ at all coins and whatever the second stop may
    read, the laying returns. As Lean has it, under the five hypotheses below, at every k of type
    `Coins B` and every v: there is a c such that `lendRow` at B, `B.rowsOf ch`, `k.look ch`, the
    place `J.p.place`, the list of the two parts and the number 0 returns c, and `chainSteps` at B,
    `B.rowsOf ch`, `k.look ch`, v, `[b]` and hs returns `(proverSideOfProximityTest J).steps b v c`
  `chainSteps_one`: general in the kind: at a list of one sub-protocol with a half: the frame's five
    tests pass and the row is lent its coins ⟹ the laying returns the half's steps. As Lean has it,
    at every book B, table rows, function look, v, block b, list hs and half g: if g is the first
    element of hs at the place of b (hf), the five tests of `chainSteps` pass (ho, hr, hc, h1, h2)
    and `lendRow` returns c for the parts of g (hl), then `chainSteps B rows look v [b] hs` returns
    `g.steps b v c`. No parameter is tied to a proximity test
  `laysB B ch J`: a definition: the test on the book and the job, a conjunction of eight tests.
    (1) The test's own block has as many lists of oracle messages as rounds. (2) `firstLen`
    (Parts.lean) plus `restLen` (HalfSteps.lean in this folder) of the stages is that block's number
    of rounds. (3) The book's cut at `J.p.place` is the list of these two numbers. (4) No row of
    `B.rowsOf ch` has an address at that place with a part's number from 2 on. (5) No entry of the
    book has such an address as its spender. (6), (7) Each part states just what the book has for
    it: `(takes, spends, carries)` of `firstPart J` is `hasFor B (B.rowsOf ch)`
    (E2E/KeyBookLends.lean) at the address `⟨J.p.place, 0⟩`, and that of `restPart J` is the same at
    `⟨J.p.place, 1⟩`; both parts are taken at `Unit` for V. (8) Every entry whose spender is at that
    place passes `inB (B.rowsOf ch)`
  `inB T e`: a definition: the entry's stretch lies within its owner's count in a table: in each
    field, `e.start` plus `e.count` is at most `dueAt T e.owner`, which is 0 where T has no row for
    the owner
  `first_states`: what a part states does not hang on the type of what its second stop may read. As
    Lean has it, at every job J and every type V: `(takes, spends, carries)` of `firstPart J` at V
    is that of `firstPart J` at `Unit`

By what. `lays_of_B`: `lendRow_ok` and `look_due` (E2E/KeyBookLends.lean: general in the book) give
the c that `lendRow` returns. Their hypotheses come from (6), (7) and (8) of `laysB`, from
`first_states`, and from the fact that `seen B ch` (E2E/KeyBookLends.lean) is `B.rowsOf ch` where ch
is 0 or 1. `chainSteps_one` then gives the steps. Its five tests come from (1) to (5), from the
fields `place`, `rounds` and `oracles` of `SeatOf`, from `first_moves` and `rest_moves`
(HalfSteps.lean: the two parts' moves, by which they have `firstLen` and `restLen` moves; the second
where there are two stages or more) and from `placed_rounds`
(Johnson/Desc/ProofFile/Honest/Small/SaysYesOf.lean). For `restPart` the equation that
`first_states` has for `firstPart` holds by unfolding and is not stated. `chainSteps_one` unfolds
`chainSteps`. `first_states` unfolds `firstPart` and goes by the two cases of `J.fresh`.

Hypotheses of `lays_of_B`. hch: ch is 0 (the first chain) or 1 (the shared chain). hst: the stages
are s :: t :: rest: two stages or more. hB: `laysB B ch J` is true. hb: `SeatOf b J enter leave`: b
has the place, the rounds and the oracle messages of the test's own block, and its decision is
`enter`, then that block's decision, then `leave`; the proof does not use the field on the decision.
hf: the first element of hs at the place `J.p.place` is `proverSideOfProximityTest J`. All other parameters are free,
among them the types S, Cl, V, W and X.

Limits.
- `laysB` is a hypothesis: it is shown of no book here. It is evaluated in two files of this folder:
  StepsToy.lean, at one small made-up book (`laysB_toy`), and StepsAtKey.lean, at the key file's
  book, at written values (`full_lays`; see the limits there).
- The two negative tests of StepsAtKey.lean leave the tests (1) to (5) of `laysB` true, by reading.
  Negative tests that change the book's cut, for (3), add an entry for a third part, for (5), and
  take one coin from the sender's row, for (8), lie in StepsToy.lean only; which test fails is by
  reading. (1), (2) and (4) have no negative test.
- The last chain, which sees all three tables, is not treated. That chain is the frame's second
  chain, every ch from 2 on: there `seen B ch` is the three tables appended, and not `B.rowsOf ch`.
- `lays_of_B` and `chainSteps_one` are at a list of one block: nothing is stated of a chain's whole
  list.
- `first_states` is stated of `firstPart` only.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.SaysYesSeat
import E2E.KeyBookLends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open AtPublicFiles.KeyBook (hasFor Stated Within lendRow_ok look_due seen)
open ProofFile.Honest.Small (placed_rounds)

variable {S Cl V W X : Type}

/-- `chainSteps` at a list of one sub-protocol b, where g is the first prover's side of hs at the
place of b (hf). If its five tests pass (ho, hr, hc, h1, h2) and `lendRow` returns c for the parts
of g (hl), it returns `g.steps b v c`. -/
theorem chainSteps_one (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (b : Block S Cl) (hs : List (Placed V W X)) (g : Placed V W X)
    (hf : (hs.find? fun h => h.place == b.place) = some g)
    (ho : b.oracles.length = b.rounds.length) (hr : g.rounds = b.rounds.length)
    (hc : B.cuts.lookup b.place = some (g.parts.map (·.moves.length)))
    (h1 : rows.any (fun r => r.1.place == b.place && decide (g.parts.length ≤ r.1.part)) = false)
    (h2 : B.ahead.any (fun e =>
      e.spender.place == b.place && decide (g.parts.length ≤ e.spender.part)) = false)
    (c : RowCoins g.parts) (hl : lendRow B rows look b.place g.parts 0 = .ok c) :
    chainSteps B rows look v [b] hs = .ok (g.steps b v c) := by
  have e1 : (b.oracles.length != b.rounds.length) = false := by simp [ho]
  have e2 : (g.rounds != b.rounds.length) = false := by simp [hr]
  have e3 : (B.cuts.lookup b.place != some (g.parts.map (·.moves.length))) = false := by simp [hc]
  simp only [chainSteps, hf, e1, e2, e3, h1, h2, hl, Bool.false_eq_true, if_false]
  show Except.ok (g.steps b v c ++ []) = _
  rw [List.append_nil]

/-- The entry's stretch lies within its owner's count in a table: in each field, `start` plus
`count` is at most `dueAt T e.owner`. -/
def inB (T : List (Addr × Due)) (e : Ahead) : Bool :=
  decide (e.start.f + e.count.f ≤ (dueAt T e.owner).f) &&
    decide (e.start.e + e.count.e ≤ (dueAt T e.owner).e)

/-- The test on the book and the job: a conjunction of eight tests, which the comment at the top of
the file lists as (1) to (8). ch: the chain's number, from 0. -/
def laysB (B : ProverCoinCounts) (ch : ℕ) (J : TestJob W X) : Bool :=
  decide ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles.length =
    (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length) &&
  decide (firstLen J.p.nums.stages + restLen J.p.nums.stages =
    (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length) &&
  (B.cuts.lookup J.p.place == some [firstLen J.p.nums.stages, restLen J.p.nums.stages]) &&
  !((B.rowsOf ch).any fun r => r.1.place == J.p.place && decide (2 ≤ r.1.part)) &&
  !(B.ahead.any fun e => e.spender.place == J.p.place && decide (2 ≤ e.spender.part)) &&
  decide (((firstPart J : Part Unit W X).takes, (firstPart J : Part Unit W X).spends,
    (firstPart J : Part Unit W X).carries) = hasFor B (B.rowsOf ch) ⟨J.p.place, 0⟩) &&
  decide (((restPart J : Part Unit W X).takes, (restPart J : Part Unit W X).spends,
    (restPart J : Part Unit W X).carries) = hasFor B (B.rowsOf ch) ⟨J.p.place, 1⟩) &&
  B.ahead.all fun e => !(e.spender.place == J.p.place) || inB (B.rowsOf ch) e

/-- What a part states does not hang on the type of what its second stop may read. As Lean has it:
`takes`, `spends` and `carries` of `firstPart J` are at every type V what they are at `Unit`. -/
theorem first_states (J : TestJob W X) :
    ((firstPart J : Part V W X).takes, (firstPart J : Part V W X).spends,
      (firstPart J : Part V W X).carries) =
    ((firstPart J : Part Unit W X).takes, (firstPart J : Part Unit W X).spends,
      (firstPart J : Part Unit W X).carries) := by
  unfold firstPart
  cases J.fresh <;> rfl

/-- **At all coins of the book, `chainSteps` returns** at the list of the one block b. Under hch,
hst, hB, hb and hf (see "Hypotheses" in the comment at the top of the file), at every k and v:
`lendRow` returns some c for the two parts, and `chainSteps` returns `(proverSideOfProximityTest J).steps b v c`. -/
theorem lays_of_B (B : ProverCoinCounts) (ch : ℕ) (hch : ch = 0 ∨ ch = 1) (J : TestJob W X)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hB : laysB B ch J = true) (b : Block S Cl) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (hb : SeatOf b J enter leave)
    (hs : List (Placed V W X))
    (hf : (hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)) (k : Coins B)
    (v : Option V) :
    ∃ c, lendRow B (B.rowsOf ch) (k.look ch) J.p.place [(firstPart J : Part V W X), restPart J]
        0 = .ok c ∧
      chainSteps B (B.rowsOf ch) (k.look ch) v [b] hs = .ok ((proverSideOfProximityTest J).steps b v c) := by
  unfold laysB at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := hB
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  have hseen : seen B ch = B.rowsOf ch := by
    rcases hch with rfl | rfl <;> rfl
  obtain ⟨c, hc⟩ := lendRow_ok B (B.rowsOf ch) (k.look ch) J.p.place
    (fun j => by
      rw [look_due, hseen]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun e he hp => by
      have q := a8 e he
      rw [hp] at q
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, inB, Bool.and_eq_true,
        decide_eq_true_eq] at q
      unfold Within
      rw [look_due, hseen]
      exact q)
    [(firstPart J : Part V W X), restPart J] 0 (fun i p hp => by
      match i, hp with
      | 0, hp =>
        obtain rfl := Option.some.inj hp
        exact (first_states J).trans a6
      | 1, hp =>
        obtain rfl := Option.some.inj hp
        exact a7)
  refine ⟨c, hc, ?_⟩
  have hpl := hb.place
  refine chainSteps_one B _ _ v b hs (proverSideOfProximityTest J) (by rw [hpl]; exact hf) ?_ ?_ ?_ ?_ ?_ c (by
                     rw [hpl]
                     exact hc)
  · rw [hb.oracles, hb.rounds]
    exact a1
  · rw [placed_rounds, hb.rounds, ← a2]
    show (firstPart J : Part V W X).moves.length + ((restPart J : Part V W X).moves.length + 0) = _
    rw [l1, l2, Nat.add_zero]
  · rw [hpl, a3]
    show some [_, _] = some [(firstPart J : Part V W X).moves.length,
      (restPart J : Part V W X).moves.length]
    rw [l1, l2]
  · rw [hpl]
    exact a4
  · rw [hpl]
    exact a5

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.chainSteps_one
#print axioms ProofFile.Honest.K12.first_states
#print axioms ProofFile.Honest.K12.lays_of_B
#print axioms ProofFile.Honest.K12.inB
#print axioms ProofFile.Honest.K12.laysB
