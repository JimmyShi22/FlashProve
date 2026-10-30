-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/HalfSteps.lean: the steps that the frame
(Johnson/Desc/ProofFile/Honest/Frame.lean) builds for the two parts of the prover's side of a
proximity test have, one by one, the moves of the test's rounds 0, 1, 2, ... The prover's side
(`proverSideOfProximityTest J`, Parts.lean in this folder) is a list of two parts, `firstPart J` and `restPart J`,
at the test's place `J.p.place`. The second part's moves are written stage by stage; here they are
shown to be those of consecutive rounds. Then the two parts' steps (`rowSteps`, the frame) are read
move by move, in the form of the hypothesis on the steps in `play_test` (PlayLaw.lean), at its
a := 0 and Ks := `coinsAtRound J c`. Stated at every job J; `segs_moves`, `rest_moves` and
`half_steps` where the job has two stages or more. Definitions and theorems.

In the list: a job J (`TestJob`, Test.lean) is what a caller supplies for its test. Its stages
(`Fmt.M1.Stage`, Fmt/M1Types.lean) are the list `J.p.nums.stages`, numbered from 0; k is a stage's
field. A part (`Part`, the frame) is the prover's side of consecutive rounds of a sub-protocol, with
one move (`Move`) for each round. A step (`Step`) is one round as the frame's `play` meets it; its
field `move` is `some` of a move at the type `Unit` in place of coins, or `none`. A part's reader is
the function rd in its moves, from what the part is given (`Part.Coins`) to `TestCoins` (Test.lean):
`firstRd J` in the first part, `restCoins J` (Parts.lean) in the second. `moveAt J rd i`
(Parts.lean) is the move of the test's round number i, and `movesFrom J rd a n` is the list of these
moves for the rounds a, a + 1, ..., a + n - 1. `moveU J K i` (PlayLaw.lean) is `moveAt` at round
number i and at the reader that is constantly K, as a move at `Unit`. `firstLen` is the first part's
number of rounds, and `roundOf stages j` is the number of the first round of stage number j (both
Parts.lean).

  `half_steps`: under the two hypotheses below, at every name, v and c: `rowSteps` at the place
    `J.p.place`, the list of the two parts, the number 0 and the rounds rs returns as many steps as
    rs has entries, and the field `move` of step number i is
    `some (moveU J (coinsAtRound J c i) i)`
  `rest_moves`: two stages or more: the second part's moves are those of the rounds from
    `firstLen` on: `movesFrom J (restCoins J)` at that round and the count `restLen`
  `firstRd`, `first_moves`: what the first part's moves read of its coins; its moves are those of
    the rounds from 0 on. `firstRd J` is a definition by the two cases of `J.fresh`, in each the
    function that `firstPart` has there. It sets the field `rest` to 0 in both cases, and the field
    `tails` to 0 where `J.fresh` is `some _`. `first_moves`, at every job: the moves are
    `movesFrom J (firstRd J) 0 (firstLen J.p.nums.stages)`
  `coinsAtRound`: the coins that round number i's move reads: the first part's reader below
    `firstLen`, the second's from there on. A definition: `firstRd J c.1` or `restCoins J c.2.1`,
    where c (`RowCoins`, the frame) is what the two parts are given
  `steps_at`: for a part p whose moves are `movesFrom J rd a n` and a list rs of n rounds, at every
    name, address, v and c: `p.steps` (`Part.steps`, the frame) returns n steps, and the field
    `move` of step number i is `some (moveU J (rd c) (a + i))`
  `segs_moves`: two stages or more, the first of them s; at every reader rd and every n below the
    number of stages less 1: the moves of the switches out of the stages 0 to n, each but the first
    with its stage's fold before it, are those of the rounds from 2 + s.k up to but not including
    the first round of stage number n + 1
  `restLen stages`: a definition: how many rounds the second part has: the number of the last
    stage's first round, plus 2, less `firstLen stages`. That the part has so many moves follows
    from `rest_moves`, where there are two stages or more
  `movesFrom_append`, `roundOf_succ`: the moves of n rounds from a on, followed by those of the next
    m rounds, are the moves of n + m rounds from a on; for j below the number of stages, the first
    round of stage number j + 1 has the number of that of stage number j, plus k + 3 at stage j

By what. The proofs unfold `movesFrom`, `roundOf`, `firstLen`, `foldMoves`, `switchMoves`,
`baseMoves`, `firstPart` and `restPart` (Parts.lean), `Part.steps` and `rowSteps` (the frame) and
`moveU` (PlayLaw.lean), and use general lemmas on lists and natural numbers. `segs_moves` goes by
induction on n; `first_moves` holds by `rfl` in each case of `J.fresh`. No theorem of another file
of this library is called.

Hypotheses. Of `half_steps`: `hst`: the job's list of stages is `s :: t :: rest`, that is, it has
two stages or more; `hrs`: rs has `firstLen` + `restLen` entries, as many as the two parts have
moves.

Limits. Nothing on what the two readers read of one run's coins. Here c is a free parameter. With
fewer than two stages `segs_moves`, `rest_moves` and `half_steps` do not apply. The list rs
(declared rounds, each with its oracle messages) is a free parameter: that a sub-protocol's declared
rounds are as many as `hrs` asks is not shown here. `half_steps` is stated at `rowSteps`, not at
`Placed.steps` or `chainSteps` (the frame). Of a step, only the field `move` is treated. Nothing on
a decision, on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlayLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc

variable {V W X C : Type}

theorem movesFrom_append (J : TestJob W X) (rd : C → TestCoins) (a n m : ℕ) :
    movesFrom J rd a n ++ movesFrom J rd (a + n) m = movesFrom J rd a (n + m) := by
  unfold movesFrom
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by simp [Nat.add_assoc]

theorem roundOf_succ (stages : List Fmt.M1.Stage) (j : ℕ) (hj : j < stages.length) :
    roundOf stages (j + 1) = roundOf stages j + ((stages.getD j default).k + 3) := by
  unfold roundOf
  rw [List.take_succ, List.map_append, List.sum_append, List.getElem?_eq_getElem hj,
    List.getD_eq_getElem _ _ hj]
  simp
  omega

/-- How many rounds the second part has. -/
def restLen (stages : List Fmt.M1.Stage) : ℕ :=
  roundOf stages (stages.length - 1) + 2 - firstLen stages

/-- The moves of the switches out of the stages 0 to n, each but the first with its stage's fold
before it, are those of consecutive rounds: from round 2 + s.k up to but not including the first
round of stage number n + 1. -/
theorem segs_moves (J : TestJob W X) (rd : C → TestCoins) (s t : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest) :
    ∀ n, n + 1 ≤ rest.length + 1 →
    ((List.range (n + 1)).flatMap fun j =>
      (if j = 0 then [] else foldMoves J rd j) ++ switchMoves J rd j) =
      movesFrom J rd (2 + s.k) (roundOf J.p.nums.stages (n + 1) - (2 + s.k))
  | 0, _ => by
    have e : roundOf J.p.nums.stages (0 + 1) = 1 + (s.k + 3) := by
      rw [hst]
      simp [roundOf]
    rw [e, show 1 + (s.k + 3) - (2 + s.k) = 2 by omega]
    show ([] ++ switchMoves J rd 0) ++ [] = _
    rw [List.nil_append, List.append_nil]
    unfold switchMoves
    have e0 : roundOf J.p.nums.stages 0 + 1 + (J.p.nums.stages.getD 0 default).k = 2 + s.k := by
      rw [hst]
      simp [roundOf]
    rw [e0]
  | n + 1, hn => by
    have ih := segs_moves J rd s t rest hst n (by omega)
    have hlen : n + 1 < J.p.nums.stages.length := by
      rw [hst]
      simp
      omega
    have hge : 2 + s.k ≤ roundOf J.p.nums.stages (n + 1) := by
      have e0 : roundOf J.p.nums.stages (n + 1) =
          1 + ((s.k + 3) + (((t :: rest).take n).map (·.k + 3)).sum) := by
        rw [hst]
        simp [roundOf]
      omega
    rw [List.range_succ, List.flatMap_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.succ_ne_zero, if_false]
    unfold foldMoves switchMoves
    rw [show roundOf J.p.nums.stages (n + 1) + 1 + (J.p.nums.stages.getD (n + 1) default).k =
        roundOf J.p.nums.stages (n + 1) + (1 + (J.p.nums.stages.getD (n + 1) default).k) by omega,
      movesFrom_append]
    obtain ⟨q, hq⟩ : ∃ q, roundOf J.p.nums.stages (n + 1) = 2 + s.k + q :=
      ⟨roundOf J.p.nums.stages (n + 1) - (2 + s.k), by omega⟩
    rw [roundOf_succ _ _ hlen, hq, Nat.add_sub_cancel_left, movesFrom_append]
    congr 1
    omega

/-- **The second part's moves are those of consecutive rounds.** Hypothesis: two stages or more. -/
theorem rest_moves (J : TestJob W X) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) :
    (restPart J : Part V W X).moves =
      movesFrom J (restCoins J) (firstLen J.p.nums.stages) (restLen J.p.nums.stages) := by
  have hl : J.p.nums.stages.length - 1 = rest.length + 1 := by
    rw [hst]
    simp
  have hf : firstLen J.p.nums.stages = 2 + s.k := by
    rw [hst]
    rfl
  have hge : 2 + s.k ≤ roundOf J.p.nums.stages (rest.length + 1) := by
    have e0 : roundOf J.p.nums.stages (rest.length + 1) =
        1 + ((s.k + 3) + (((t :: rest).take rest.length).map (·.k + 3)).sum) := by
      rw [hst]
      simp [roundOf]
    omega
  show ((List.range (J.p.nums.stages.length - 1)).flatMap fun j =>
      (if j = 0 then [] else foldMoves J (restCoins J) j) ++ switchMoves J (restCoins J) j) ++
      baseMoves J (restCoins J) = _
  unfold baseMoves restLen
  rw [hl, hf, segs_moves J (restCoins J) s t rest hst rest.length (le_refl _)]
  obtain ⟨q, hq⟩ : ∃ q, roundOf J.p.nums.stages (rest.length + 1) = 2 + s.k + q :=
    ⟨roundOf J.p.nums.stages (rest.length + 1) - (2 + s.k), by omega⟩
  rw [hq, Nat.add_sub_cancel_left, movesFrom_append]
  congr 1
  omega

/-- What the first part's moves read of its coins. -/
def firstRd : (J : TestJob W X) → (firstPart J : Part V W X).Coins → TestCoins
  | ⟨p, ms, none, r, ro, tr⟩, c =>
    let c' : Handed ⟨0, dueFresh (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩)⟩ []
      (memberRuns (⟨p, ms, none, r, ro, tr⟩ : TestJob W X) ⟨p.place, 0⟩) := c
    ⟨(stretchOf c'.1).e, tailsIn (TestJob.s₀ ⟨p, ms, none, r, ro, tr⟩) (stretchOf c'.1).e,
      stretches _ c'.2.2, fun _ => 0⟩
  | ⟨p, ms, some f, r, ro, tr⟩, c =>
    let c' : Handed ⟨0, 0⟩ [spentRun (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X)]
      (memberRuns (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X) ⟨p.place, 0⟩) := c
    ⟨(stretchOf c'.2.1.1).e, fun _ _ => 0, stretches _ c'.2.2, fun _ => 0⟩

/-- The first part's moves are those of the rounds from 0 on. -/
theorem first_moves : ∀ J : TestJob W X, (firstPart J : Part V W X).moves =
    movesFrom J (firstRd J) 0 (firstLen J.p.nums.stages)
  | ⟨_, _, none, _, _, _⟩ => rfl
  | ⟨_, _, some _, _, _, _⟩ => rfl

/-- The coins that round number i's move reads. -/
def coinsAtRound (J : TestJob W X) (c : RowCoins [(firstPart J : Part V W X), restPart J]) (i : ℕ) :
    TestCoins :=
  if i < firstLen J.p.nums.stages then firstRd J c.1 else restCoins J c.2.1

/-- Where a part's moves are those of the rounds a, a + 1, ..., a + n - 1, and rs has n entries:
`p.steps` returns n steps, and step number i has the move of round number a + i at `rd c`. -/
theorem steps_at (J : TestJob W X) (p : Part V W X) (rd : p.Coins → TestCoins) (a n : ℕ)
    (hp : p.moves = movesFrom J rd a n) (name : String) (ad : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hrs : rs.length = n) (v : Option V) (c : p.Coins) :
    (p.steps name ad rs v c).length = n ∧
      ∀ i (h : i < (p.steps name ad rs v c).length),
        (p.steps name ad rs v c)[i].move = some (moveU J (rd c) (a + i)) := by
  have hl : (p.steps name ad rs v c).length = n := by
    simp [Part.steps, hp, movesFrom, hrs]
  refine ⟨hl, fun i h => ?_⟩
  have hi : i < n := hl ▸ h
  simp only [Part.steps, List.getElem_map, List.getElem_zipIdx, List.getElem_zip]
  have e : p.moves[i]'(by rw [hp]; simpa [movesFrom] using hi) = moveAt J rd (a + i) := by
    simp [hp, movesFrom]
  rw [e]
  rfl

/-- **The steps of the test's two parts have the moves of the rounds 0, 1, 2, ...** Hypotheses: two
stages or more; rs has as many entries as the two parts have moves. -/
theorem half_steps (J : TestJob W X) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (name : String) (v : Option V)
    (rs : List (Fmt.DeclaredRound × List Oracle))
    (hrs : rs.length = firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (c : RowCoins [(firstPart J : Part V W X), restPart J]) :
    (rowSteps name J.p.place v [(firstPart J : Part V W X), restPart J] 0 rs c).length =
        rs.length ∧
      ∀ i (h : i < (rowSteps name J.p.place v [(firstPart J : Part V W X), restPart J] 0 rs
          c).length),
        (rowSteps name J.p.place v [(firstPart J : Part V W X), restPart J] 0 rs c)[i].move =
          some (moveU J (coinsAtRound J c i) i) := by
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves]
    simp [movesFrom]
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  obtain ⟨a1, a2⟩ := steps_at J (firstPart J : Part V W X) (firstRd J) 0 _ (first_moves J) name
    ⟨J.p.place, 0⟩ (rs.take (firstPart J : Part V W X).moves.length)
    (by rw [List.length_take, l1, hrs]; omega) v c.1
  obtain ⟨b1, b2⟩ := steps_at J (restPart J : Part V W X) (restCoins J) _ _
    (rest_moves J s t rest hst) name ⟨J.p.place, 0 + 1⟩
    ((rs.drop (firstPart J : Part V W X).moves.length).take (restPart J : Part V W X).moves.length)
    (by rw [List.length_take, List.length_drop, l1, l2, hrs]; omega) v c.2.1
  have hsplit : rowSteps name J.p.place v [(firstPart J : Part V W X), restPart J] 0 rs c =
      (firstPart J : Part V W X).steps name ⟨J.p.place, 0⟩
        (rs.take (firstPart J : Part V W X).moves.length) v c.1 ++
      (restPart J : Part V W X).steps name ⟨J.p.place, 0 + 1⟩
        ((rs.drop (firstPart J : Part V W X).moves.length).take
          (restPart J : Part V W X).moves.length) v c.2.1 := by
    simp [rowSteps]
  refine ⟨by rw [hsplit, List.length_append, a1, b1, hrs], fun i h => ?_⟩
  simp only [hsplit] at h ⊢
  unfold coinsAtRound
  by_cases ci : i < firstLen J.p.nums.stages
  · rw [List.getElem_append_left (by rw [a1]; exact ci), if_pos ci, a2 i (by rw [a1]; exact ci),
      Nat.zero_add]
  · rw [List.getElem_append_right (by rw [a1]; omega), if_neg ci, b2 _ _, a1]
    congr 3 <;> omega

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.rest_moves
#print axioms ProofFile.Honest.K12.first_moves
#print axioms ProofFile.Honest.K12.steps_at
#print axioms ProofFile.Honest.K12.half_steps
#print axioms ProofFile.Honest.K12.movesFrom_append
#print axioms ProofFile.Honest.K12.roundOf_succ
#print axioms ProofFile.Honest.K12.segs_moves
#print axioms ProofFile.Honest.K12.restLen
#print axioms ProofFile.Honest.K12.firstRd
#print axioms ProofFile.Honest.K12.coinsAtRound
