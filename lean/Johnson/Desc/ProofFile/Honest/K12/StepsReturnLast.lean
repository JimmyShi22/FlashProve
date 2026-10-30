-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/StepsReturnLast.lean: THE TWIN OF `laysB` AND `lays_of_B`
(StepsReturn.lean in this folder) AT THE LAST CHAIN, the frame's chain number 2. There `seen B 2` is
the three tables appended (E2E/KeyBookLends.lean), while `B.rowsOf 2` is the last alone: a stretch
that the book carries to a part of the last chain is owned in an earlier chain, so test (8) of
`laysB` cannot pass there at `B.rowsOf 2`, though the frame lends.

  `lookup_none_of`, `due_seen`   where no row of the first or the shared table stands at a place,
                 the count that chain 2 sees at an address of that place is the last table's
  `laysLastB B J`   the test: (1) to (7) of `laysB` at chain 2; (8) at `seen B 2`; and (9), (10):
                 no row of the first table, and no row of the shared table, at the test's place
  `lays_last_of_B`   the twin of `lays_of_B`: under the same hypotheses at all coins the laying
                 returns, at chain 2
  `laysLastB_congr`   the test reads the job's `p`, `members` and `fresh` alone
  `jobKW`, `own_lays`, `own_old_no`, `own_lays_bite`   at the key file's book, at the own test
                 (`jobOwn`, E2E/KeyTestSizes.lean, at `piKWFull`): the test says yes; `laysB` at
                 chain 2 says no there; four controls, one for each new test and one on the entries

Why (9) and (10). `Coins.look 2` takes the first of the three tables that has a row at an address
(`look_due`): a row of an earlier table at the test's place would hide the last table's. `laysB`
needs no such test: in chains 0 and 1 one table is seen.

Limits.
- As in StepsReturn.lean: `laysLastB` is a hypothesis; the list of one block; nothing of a chain's
  whole list.
- `own_lays` is at written values, at the key file's book: the limits of StepsAtKey.lean stand: the
  book's carried entries are a proposal; no theorem ties `jobOwn`'s members to the description. Of
  the proof file's book nothing is evaluated here. Most of what `own_lays` reads the key file's own
  guards and tests have read already (E2E/KeyBookHeldK12.lean, E2E/KeyBookThirdNamed.lean): new are
  (1), (2), (4), (5) at this job: the law `lays_last_of_B` is what this file adds.
- Nothing on completeness, on soundness or on what is hidden.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.StepsReturn
import Johnson.Desc.K12.Law.PlacesKeyFull
import E2E.KeyBookHeldK12

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open AtPublicFiles.KeyBook (hasFor Stated Within lendRow_ok look_due seen atFull keyBook)
open AtPublicFiles.KeyTest (jobOwn)
open H2K.Member (piKWFull)
open ProofFile.Honest.Small (placed_rounds)

variable {S Cl V W X : Type}

/-- No row of a table at an address's place: the table has no row at the address. -/
theorem lookup_none_of (a : Addr) : ∀ l : List (Addr × Due),
    (l.any fun r => r.1.place == a.place) = false → l.lookup a = none
  | [], _ => rfl
  | ⟨x, d⟩ :: l, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have hne : (a == x) = false := beq_eq_false_iff_ne.2 fun e => by
      have k := h.1
      rw [e, beq_self_eq_true] at k
      cases k
    show (match a == x with | true => some d | false => l.lookup a) = none
    rw [hne]
    exact lookup_none_of a l h.2

/-- Where neither earlier table has a row at the place, chain 2 sees the last table's count. -/
theorem due_seen (B : ProverCoinCounts) (a : Addr) (h1 : (B.first.any fun r => r.1.place == a.place) = false)
    (h2 : (B.shared.any fun r => r.1.place == a.place) = false) :
    dueAt (seen B 2) a = dueAt (B.rowsOf 2) a := by
  show ((B.first ++ B.shared ++ B.second).lookup a).getD ⟨0, 0⟩ = (B.second.lookup a).getD ⟨0, 0⟩
  rw [List.lookup_append, List.lookup_append, lookup_none_of a _ h1, lookup_none_of a _ h2]
  rfl

/-- The test on the book and the job at the last chain: (1) to (7) as in `laysB` at chain 2; (8) at
the tables that chain 2 sees; (9), (10): the head. -/
def laysLastB (B : ProverCoinCounts) (J : TestJob W X) : Bool :=
  decide ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles.length =
    (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length) &&
  decide (firstLen J.p.nums.stages + restLen J.p.nums.stages =
    (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length) &&
  (B.cuts.lookup J.p.place == some [firstLen J.p.nums.stages, restLen J.p.nums.stages]) &&
  !((B.rowsOf 2).any fun r => r.1.place == J.p.place && decide (2 ≤ r.1.part)) &&
  !(B.ahead.any fun e => e.spender.place == J.p.place && decide (2 ≤ e.spender.part)) &&
  decide (((firstPart J : Part Unit W X).takes, (firstPart J : Part Unit W X).spends,
    (firstPart J : Part Unit W X).carries) = hasFor B (B.rowsOf 2) ⟨J.p.place, 0⟩) &&
  decide (((restPart J : Part Unit W X).takes, (restPart J : Part Unit W X).spends,
    (restPart J : Part Unit W X).carries) = hasFor B (B.rowsOf 2) ⟨J.p.place, 1⟩) &&
  (B.ahead.all fun e => !(e.spender.place == J.p.place) || inB (seen B 2) e) &&
  !(B.first.any fun r => r.1.place == J.p.place) &&
  !(B.shared.any fun r => r.1.place == J.p.place)

/-- **At all coins of the book, `chainSteps` returns at the last chain** at the list of the one
block b. The twin of `lays_of_B`, at chain 2, under `laysLastB`. -/
theorem lays_last_of_B (B : ProverCoinCounts) (J : TestJob W X)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hB : laysLastB B J = true) (b : Block S Cl) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (hb : SeatOf b J enter leave)
    (hs : List (Placed V W X))
    (hf : (hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)) (k : Coins B)
    (v : Option V) :
    ∃ c, lendRow B (B.rowsOf 2) (k.look 2) J.p.place [(firstPart J : Part V W X), restPart J]
        0 = .ok c ∧
      chainSteps B (B.rowsOf 2) (k.look 2) v [b] hs = .ok ((proverSideOfProximityTest J).steps b v c) := by
  unfold laysLastB at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩ := hB
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  obtain ⟨c, hc⟩ := lendRow_ok B (B.rowsOf 2) (k.look 2) J.p.place
    (fun j => by
      rw [look_due, due_seen B ⟨J.p.place, j⟩ a9 a10]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun e he hp => by
      have q := a8 e he
      rw [hp] at q
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, inB, Bool.and_eq_true,
        decide_eq_true_eq] at q
      unfold Within
      rw [look_due]
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

/-- Of a job `laysLastB` reads only the fields `p`, `members` and `fresh`: it is equal at two jobs,
also of different types, that agree in these three. -/
theorem laysLastB_congr {W' X' : Type} (B : ProverCoinCounts) (J : TestJob W X) (J' : TestJob W' X')
    (hp : J.p = J'.p) (hm : J.members = J'.members) (hf : J.fresh = J'.fresh) :
    laysLastB B J = laysLastB B J' := by
  cases J with
  | mk p ms fresh r ro tr =>
    cases J' with
    | mk p' ms' fresh' r' ro' tr' =>
      obtain rfl : p = p' := hp
      obtain rfl : ms = ms' := hm
      obtain rfl : fresh = fresh' := hf
      cases fresh <;> rfl

/-- `jobOwn` (E2E/KeyTestSizes.lean) with its field `p` replaced by `piKWFull`. -/
def jobKW : TestJob Unit Unit := { jobOwn with p := piKWFull }

set_option maxRecDepth 100000 in
/-- **At the key file's book the test says yes at the own test.** An evaluation in Lean's kernel. -/
theorem own_lays : atFull (fun K => laysLastB (keyBook K) jobKW) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`laysB` at chain 2 says no at the same book and job**: its test (8) reads the last table
alone. -/
theorem own_old_no : atFull (fun K => !laysB (keyBook K) 2 jobKW) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The test can fail. It says no: without the book's carried entries; at (8), without the first
table's rows; at (9), with a row of the first table at the test's place; at (10), with a row of the
shared table there. -/
theorem own_lays_bite : atFull (fun K =>
    !laysLastB (keyBook K false) jobKW &&
    !laysLastB { keyBook K with first := [] } jobKW &&
    !laysLastB { keyBook K with first := (⟨jobKW.p.place, 0⟩, ⟨0, 0⟩) :: (keyBook K).first }
      jobKW &&
    !laysLastB { keyBook K with shared := (⟨jobKW.p.place, 0⟩, ⟨0, 0⟩) :: (keyBook K).shared }
      jobKW) = true := by
  decide +kernel

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.lookup_none_of
#print axioms ProofFile.Honest.K12.due_seen
#print axioms ProofFile.Honest.K12.laysLastB
#print axioms ProofFile.Honest.K12.lays_last_of_B
#print axioms ProofFile.Honest.K12.laysLastB_congr
#print axioms ProofFile.Honest.K12.jobKW
#print axioms ProofFile.Honest.K12.own_lays
#print axioms ProofFile.Honest.K12.own_old_no
#print axioms ProofFile.Honest.K12.own_lays_bite
