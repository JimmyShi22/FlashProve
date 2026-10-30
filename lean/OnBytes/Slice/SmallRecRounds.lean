-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecRounds.lean: what the 24 rounds of an entry's chain are, and the trees that
are sent, at the small files of the setting "record with work".

OnBytes/Slice/RoundsOf.lean and RoundsLink.lean derive what a written round sends and draws from one
hypothesis, `IsRd d r`: the written round d has the entry, the kind and the items of the format's
round r. This file proves that hypothesis for all rounds of the description `srD`
(OnBytes/Slice/SmallRecSz.lean), counted from 0: the link's five; the batching; for each of the
first two stages the joining of a hiding sum, the rounds of the fold, the sending of the next tree
and the code switch; and the two rounds of the base case. It also says which rounds send a tree, how
many positions and how many words in a column each of the three trees has, and which rounds ask for
work. Each proof goes from `srRd i` to `srRt i` (`sr_rd`, which rests on one evaluation of the dry
run in Lean's kernel) and evaluates the format's makers of rounds.

Main theorems.
 `sr_rd0` to `sr_rd23`   each round is the format's round of its kind. The round LINK, the two
                         rounds CS and the round BASE are the format's at 32 bits of work. The round
                         BAT is the format's at 107 rows (`sr_rows`).
 `sr_tail`               the list of the nineteen rounds after the fifth, with the rounds of a fold
                         as one round repeated, bracketed as a chain's rounds are.
 `sr_tree_some`, `sr_tree_none`   the rounds 1, 13 and 20 send a tree, the 21 others none.
 `sr_pos1`, `sr_width1`, `sr_pos13`, `sr_width13`, `sr_pos20`, `sr_width20`
                         the three trees' positions and widths; `sr_widths`: 111, 72 and 12 words.
 `sr_rB`                 what the last round sends and draws.
 `sr_work`               the bits of work of each round: 32 at the rounds 3, 14, 21 and 23.

Not claimed. Nothing on any other description. Nothing on the plan's entry RECORD, which is no round
of the chain. That the 107 rows are the rows of OnBytes/Slice/RowsXRec.lean: the number alone is
compared. Nothing on soundness.

-/
import OnBytes.Slice.RoundsOf
import OnBytes.Slice.RoundsLink
import OnBytes.Slice.SmallRecSz

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Run _root_.Run.PQ

/-! ## The link's five rounds -/

/-- The link's point. -/
theorem sr_rd0 : IsRd (srRd 0) (Fmt.M3.rLinkPoint srPar.v) := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The group's tree is sent. -/
theorem sr_rd1 : IsRd (srRd 1) (Fmt.M2.rSeedN (srPar.aR + srPar.aP)) := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The two answers to the seed. -/
theorem sr_rd2 : IsRd (srRd 2) (Fmt.M2.rAnswers 2) := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The link's draws, with 32 bits of work. -/
theorem sr_rd3 : IsRd (srRd 3) (Fmt.M3.rLink srPar.work (srPar.nu0 + srPar.nuj) srPar.T.a) := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The link's second point. -/
theorem sr_rd4 : IsRd (srRd 4) (Fmt.M3.rLinkPhi srPar.aPhi) := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The batching. -/
theorem sr_rd5 : IsRd (srRd 5) (Fmt.M2.rBatN (2 * srPar.s + Fmt.M3.nRows srPar)) := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The batching has 107 rows. -/
theorem sr_rows : 2 * srPar.s + Fmt.M3.nRows srPar = 107 := rfl

/-! ## The first stage -/

/-- The round FOLD epsilon of the first stage's fold. -/
theorem sr_rd6 : IsRd (srRd 6) (Fmt.M1.rEps "FOLD epsilon") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The first of the six rounds named FOLD round of the first stage's fold. -/
theorem sr_rd7 : IsRd (srRd 7) (Fmt.M1.rTwo "FOLD round") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The second of the six rounds named FOLD round of the first stage's fold. -/
theorem sr_rd8 : IsRd (srRd 8) (Fmt.M1.rTwo "FOLD round") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The third of the six rounds named FOLD round of the first stage's fold. -/
theorem sr_rd9 : IsRd (srRd 9) (Fmt.M1.rTwo "FOLD round") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The fourth of the six rounds named FOLD round of the first stage's fold. -/
theorem sr_rd10 : IsRd (srRd 10) (Fmt.M1.rTwo "FOLD round") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The fifth of the six rounds named FOLD round of the first stage's fold. -/
theorem sr_rd11 : IsRd (srRd 11) (Fmt.M1.rTwo "FOLD round") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The sixth of the six rounds named FOLD round of the first stage's fold. -/
theorem sr_rd12 : IsRd (srRd 12) (Fmt.M1.rTwo "FOLD round") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The second stage's tree is sent. -/
theorem sr_rd13 : IsRd (srRd 13) (Fmt.M1.rSeed srSg2.st) := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The code switch from the first stage, with 32 bits of work. -/
theorem sr_rd14 : IsRd (srRd 14) (Fmt.M1.rCs srPar.work srSg1.st 0 (Fmt.M3.width0 srPar)) := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The second stage -/

/-- The round FOLD epsilon of the second stage's fold. -/
theorem sr_rd15 : IsRd (srRd 15) (Fmt.M1.rEps "FOLD epsilon") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The first of the four rounds named FOLD round of the second stage's fold. -/
theorem sr_rd16 : IsRd (srRd 16) (Fmt.M1.rTwo "FOLD round") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The second of the four rounds named FOLD round of the second stage's fold. -/
theorem sr_rd17 : IsRd (srRd 17) (Fmt.M1.rTwo "FOLD round") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The third of the four rounds named FOLD round of the second stage's fold. -/
theorem sr_rd18 : IsRd (srRd 18) (Fmt.M1.rTwo "FOLD round") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The fourth of the four rounds named FOLD round of the second stage's fold. -/
theorem sr_rd19 : IsRd (srRd 19) (Fmt.M1.rTwo "FOLD round") := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The third stage's tree is sent. -/
theorem sr_rd20 : IsRd (srRd 20) (Fmt.M1.rSeed srSg3.st) := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The code switch from the second stage, with 32 bits of work. -/
theorem sr_rd21 : IsRd (srRd 21) (Fmt.M1.rCs srPar.work srSg2.st 1 (Fmt.M1.wMid srSg2.st)) := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The base case -/

/-- The first round of the base case. -/
theorem sr_rd22 : IsRd (srRd 22) Fmt.M1.rLambda := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The last round, the second of the base case, with 32 bits of work. -/
theorem sr_rd23 : IsRd (srRd 23) (Fmt.M1.rBase srPar.work srSg3.st 2) := by
  rw [sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The nineteen rounds after the fifth. The rounds of a fold are one round, repeated. The brackets
are those of `Chain.rds` (OnBytes/Slice/ManyDefs.lean). -/
theorem sr_tail : srD.ds.drop 5 =
    srRd 5 ::
      ((srRd 6 :: List.replicate 6 (srRd 7)) ++ ([srRd 13, srRd 14] ++
        ((srRd 15 :: List.replicate 4 (srRd 16)) ++ ([srRd 20, srRd 21] ++
          [srRd 22, srRd 23])))) := by
  unfold srRd
  rw [sr_ds]
  rfl

/-! ## Which rounds send a tree -/

/-- Three rounds send a tree. -/
theorem sr_tree_some : (srRd 1).tree.isSome = true ∧ (srRd 13).tree.isSome = true ∧
    (srRd 20).tree.isSome = true := by
  rw [sr_rd, sr_rd, sr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The 21 other rounds send none. -/
theorem sr_tree_none :
    ∀ i ∈ [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 21, 22, 23],
      (srRd i).tree.isSome = false := by
  have h : ([0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 21, 22, 23].all
      fun i => !(srRt i).tree.isSome) = true := rfl
  intro i hi
  rw [sr_rd]
  simpa only [Bool.not_eq_true'] using List.all_eq_true.1 h i hi

/-! ## The three trees -/

/-- The group's tree has the positions of the first stage's code. -/
theorem sr_pos1 : PQ.posN (srRd 1).tree = 2 ^ srPar.C.a := by
  rw [sr_rd]
  rfl

/-- A column of the group's tree has the group's width, with one fresh mask row. -/
theorem sr_width1 : PQ.colW (srRd 1).tree = Fmt.M2.widthOf srPar.mems 1 := by
  rw [sr_rd]
  rfl

/-- The second stage's tree has the positions of that stage's main code. -/
theorem sr_pos13 : PQ.posN (srRd 13).tree = 2 ^ srSg2.C.a := by
  rw [sr_rd]
  rfl

/-- The number of words in a column of the second stage's tree. -/
theorem sr_width13 : PQ.colW (srRd 13).tree = Fmt.M1.wMid srSg2.st := by
  rw [sr_rd]
  rfl

/-- The third stage's tree has the positions of that stage's code. -/
theorem sr_pos20 : PQ.posN (srRd 20).tree = 2 ^ srSg3.C.a := by
  rw [sr_rd]
  rfl

/-- The number of words in a column of the third stage's tree. -/
theorem sr_width20 : PQ.colW (srRd 20).tree = Fmt.M1.wLast srSg3.st := by
  rw [sr_rd]
  rfl

/-- The three widths as numbers. -/
theorem sr_widths : PQ.colW (srRd 1).tree = 111 ∧ PQ.colW (srRd 13).tree = 72 ∧
    PQ.colW (srRd 20).tree = 12 := by
  rw [sr_width1, sr_width13, sr_width20]
  decide +kernel

/-- What the last round sends and draws. -/
theorem sr_rB : SendsDraws (srRd 23) (srSg3.C.l + srSg3.Z.l + srSg3.C.r + srSg3.Z.r) 0 srSg3.t
    srSg3.C.a :=
  rBase_sd (s := srSg3.st) sr_rd23 (by decide)

/-! ## Work -/

/-- The bits of work that each round asks for: 32 at the link's draws, at the two code switches and
at the last round; none elsewhere. -/
theorem sr_work : srD.ds.map (·.entry.work) =
    [0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 32, 0, 32] := by
  rw [sr_ds]
  rfl

end OnBytes.Slice
