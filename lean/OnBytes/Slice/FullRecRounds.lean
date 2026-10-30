-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecRounds.lean: what the 41 rounds of an entry's chain are, and the trees that are
sent, at the full-size files of the setting "record with work".

The like of OnBytes/Slice/SmallRecRounds.lean, whose head describes the way, at the full size; its
text was made from that file's by a program that swaps names and numbers and writes five stages for
three. For all rounds of the description `frD` (OnBytes/Slice/FullRecSz.lean), counted from 0, it
proves `IsRd d r`: the written round d has the entry, the kind and the items of the format's round
r. Each proof goes from `frRd i` to `frRt i` (`fr_rd`, which rests on one evaluation of the dry run
in Lean's kernel) and evaluates the format's makers of rounds.

Main theorems.
 `fr_rd0` to `fr_rd40`   each round is the format's round of its kind. The round LINK, the four
                         rounds CS and the round BASE are the format's at 32 bits of work. The round
                         BAT is the format's at 129 rows (`fr_rows`).
 `fr_tail`               the list of the 36 rounds after the fifth, with the rounds of a fold as one
                         round repeated, bracketed as a chain's rounds are.
 `fr_tree_some`, `fr_tree_none`   the rounds 1, 15, 23, 30 and 37 send a tree, the 36 others none.
 `fr_pos1`, `fr_width1` and their like   the five trees' positions and widths; `fr_widths`:
                         645, 120, 72, 72 and 12 words.
 `fr_rB`                 what the last round sends and draws.
 `fr_work`               the bits of work of each round: 32 at the rounds 3, 16, 24, 31, 38 and 40.

Not claimed. Nothing on any other description. Nothing on the plan's entry RECORD, which is no round
of the chain. That the 129 rows are the rows of OnBytes/Slice/RowsXRec.lean: the number alone is
compared. Nothing on soundness.

-/
import OnBytes.Slice.RoundsOf
import OnBytes.Slice.RoundsLink
import OnBytes.Slice.FullRecSz

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Run _root_.Run.PQ

/-! ## The link's five rounds -/

/-- The link's point. -/
theorem fr_rd0 : IsRd (frRd 0) (Fmt.M3.rLinkPoint frPar.v) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The group's tree is sent. -/
theorem fr_rd1 : IsRd (frRd 1) (Fmt.M2.rSeedN (frPar.aR + frPar.aP)) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The two answers to the seed. -/
theorem fr_rd2 : IsRd (frRd 2) (Fmt.M2.rAnswers 2) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The link's draws, with 32 bits of work. -/
theorem fr_rd3 : IsRd (frRd 3) (Fmt.M3.rLink frPar.work (frPar.nu0 + frPar.nuj) frPar.T.a) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The link's second point. -/
theorem fr_rd4 : IsRd (frRd 4) (Fmt.M3.rLinkPhi frPar.aPhi) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The batching. -/
theorem fr_rd5 : IsRd (frRd 5) (Fmt.M2.rBatN (2 * frPar.s + Fmt.M3.nRows frPar)) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The batching has 129 rows. -/
theorem fr_rows : 2 * frPar.s + Fmt.M3.nRows frPar = 129 := rfl

/-! ## The first stage -/

/-- The round FOLD epsilon of the first stage's fold. -/
theorem fr_rd6 : IsRd (frRd 6) (Fmt.M1.rEps "FOLD epsilon") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The first of the eight rounds named FOLD round of the first stage's fold. -/
theorem fr_rd7 : IsRd (frRd 7) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The second of the eight rounds named FOLD round of the first stage's fold. -/
theorem fr_rd8 : IsRd (frRd 8) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The third of the eight rounds named FOLD round of the first stage's fold. -/
theorem fr_rd9 : IsRd (frRd 9) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The fourth of the eight rounds named FOLD round of the first stage's fold. -/
theorem fr_rd10 : IsRd (frRd 10) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The fifth of the eight rounds named FOLD round of the first stage's fold. -/
theorem fr_rd11 : IsRd (frRd 11) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The sixth of the eight rounds named FOLD round of the first stage's fold. -/
theorem fr_rd12 : IsRd (frRd 12) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The seventh of the eight rounds named FOLD round of the first stage's fold. -/
theorem fr_rd13 : IsRd (frRd 13) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The eighth of the eight rounds named FOLD round of the first stage's fold. -/
theorem fr_rd14 : IsRd (frRd 14) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The second stage's tree is sent. -/
theorem fr_rd15 : IsRd (frRd 15) (Fmt.M1.rSeed frSg2.st) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The code switch from the first stage, with 32 bits of work. -/
theorem fr_rd16 : IsRd (frRd 16) (Fmt.M1.rCs frPar.work frSg1.st 0 (Fmt.M3.width0 frPar)) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The second stage -/

/-- The round FOLD epsilon of the second stage's fold. -/
theorem fr_rd17 : IsRd (frRd 17) (Fmt.M1.rEps "FOLD epsilon") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The first of the five rounds named FOLD round of the second stage's fold. -/
theorem fr_rd18 : IsRd (frRd 18) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The second of the five rounds named FOLD round of the second stage's fold. -/
theorem fr_rd19 : IsRd (frRd 19) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The third of the five rounds named FOLD round of the second stage's fold. -/
theorem fr_rd20 : IsRd (frRd 20) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The fourth of the five rounds named FOLD round of the second stage's fold. -/
theorem fr_rd21 : IsRd (frRd 21) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The fifth of the five rounds named FOLD round of the second stage's fold. -/
theorem fr_rd22 : IsRd (frRd 22) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The third stage's tree is sent. -/
theorem fr_rd23 : IsRd (frRd 23) (Fmt.M1.rSeed frSg3.st) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The code switch from the second stage, with 32 bits of work. -/
theorem fr_rd24 : IsRd (frRd 24) (Fmt.M1.rCs frPar.work frSg2.st 1 (Fmt.M1.wMid frSg2.st)) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The third stage -/

/-- The round FOLD epsilon of the third stage's fold. -/
theorem fr_rd25 : IsRd (frRd 25) (Fmt.M1.rEps "FOLD epsilon") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The first of the four rounds named FOLD round of the third stage's fold. -/
theorem fr_rd26 : IsRd (frRd 26) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The second of the four rounds named FOLD round of the third stage's fold. -/
theorem fr_rd27 : IsRd (frRd 27) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The third of the four rounds named FOLD round of the third stage's fold. -/
theorem fr_rd28 : IsRd (frRd 28) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The fourth of the four rounds named FOLD round of the third stage's fold. -/
theorem fr_rd29 : IsRd (frRd 29) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The fourth stage's tree is sent. -/
theorem fr_rd30 : IsRd (frRd 30) (Fmt.M1.rSeed frSg4.st) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The code switch from the third stage, with 32 bits of work. -/
theorem fr_rd31 : IsRd (frRd 31) (Fmt.M1.rCs frPar.work frSg3.st 2 (Fmt.M1.wMid frSg3.st)) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The fourth stage -/

/-- The round FOLD epsilon of the fourth stage's fold. -/
theorem fr_rd32 : IsRd (frRd 32) (Fmt.M1.rEps "FOLD epsilon") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The first of the four rounds named FOLD round of the fourth stage's fold. -/
theorem fr_rd33 : IsRd (frRd 33) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The second of the four rounds named FOLD round of the fourth stage's fold. -/
theorem fr_rd34 : IsRd (frRd 34) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The third of the four rounds named FOLD round of the fourth stage's fold. -/
theorem fr_rd35 : IsRd (frRd 35) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The fourth of the four rounds named FOLD round of the fourth stage's fold. -/
theorem fr_rd36 : IsRd (frRd 36) (Fmt.M1.rTwo "FOLD round") := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The fifth stage's tree is sent. -/
theorem fr_rd37 : IsRd (frRd 37) (Fmt.M1.rSeed frSg5.st) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The code switch from the fourth stage, with 32 bits of work. -/
theorem fr_rd38 : IsRd (frRd 38) (Fmt.M1.rCs frPar.work frSg4.st 3 (Fmt.M1.wMid frSg4.st)) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The base case -/

/-- The first round of the base case. -/
theorem fr_rd39 : IsRd (frRd 39) Fmt.M1.rLambda := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The last round, the second of the base case, with 32 bits of work. -/
theorem fr_rd40 : IsRd (frRd 40) (Fmt.M1.rBase frPar.work frSg5.st 4) := by
  rw [fr_rd]
  exact ⟨rfl, rfl, rfl⟩

/-- The 36 rounds after the fifth. The rounds of a fold are one round, repeated. The brackets are
those of `Chain.rds` (OnBytes/Slice/ManyDefs.lean). -/
theorem fr_tail : frD.ds.drop 5 =
    frRd 5 ::
      ((frRd 6 :: List.replicate 8 (frRd 7)) ++ ([frRd 15, frRd 16] ++
        ((frRd 17 :: List.replicate 5 (frRd 18)) ++ ([frRd 23, frRd 24] ++
          ((frRd 25 :: List.replicate 4 (frRd 26)) ++ ([frRd 30, frRd 31] ++
            ((frRd 32 :: List.replicate 4 (frRd 33)) ++ ([frRd 37, frRd 38] ++
              [frRd 39, frRd 40])))))))) := by
  unfold frRd
  rw [fr_ds]
  rfl

/-! ## Which rounds send a tree -/

/-- Five rounds send a tree. -/
theorem fr_tree_some : ∀ i ∈ [1, 15, 23, 30, 37], (frRd i).tree.isSome = true := by
  have h : ([1, 15, 23, 30, 37].all fun i => (frRt i).tree.isSome) = true := rfl
  intro i hi
  rw [fr_rd]
  exact List.all_eq_true.1 h i hi

/-- The 36 other rounds send none. -/
theorem fr_tree_none :
    ∀ i ∈ [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26,
    27, 28, 29, 31, 32, 33, 34, 35, 36, 38, 39, 40],
      (frRd i).tree.isSome = false := by
  have h : ([0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26,
      27, 28, 29, 31, 32, 33, 34, 35, 36, 38, 39, 40].all
      fun i => !(frRt i).tree.isSome) = true := rfl
  intro i hi
  rw [fr_rd]
  simpa only [Bool.not_eq_true'] using List.all_eq_true.1 h i hi

/-! ## The five trees -/

/-- The group's tree has the positions of the first stage's code. -/
theorem fr_pos1 : PQ.posN (frRd 1).tree = 2 ^ frPar.C.a := by
  rw [fr_rd]
  rfl

/-- A column of the group's tree has the group's width, with one fresh mask row. -/
theorem fr_width1 : PQ.colW (frRd 1).tree = Fmt.M2.widthOf frPar.mems 1 := by
  rw [fr_rd]
  rfl

/-- The second stage's tree has the positions of that stage's main code. -/
theorem fr_pos15 : PQ.posN (frRd 15).tree = 2 ^ frSg2.C.a := by
  rw [fr_rd]
  rfl

/-- The number of words in a column of the second stage's tree. -/
theorem fr_width15 : PQ.colW (frRd 15).tree = Fmt.M1.wMid frSg2.st := by
  rw [fr_rd]
  rfl

/-- The third stage's tree has the positions of that stage's main code. -/
theorem fr_pos23 : PQ.posN (frRd 23).tree = 2 ^ frSg3.C.a := by
  rw [fr_rd]
  rfl

/-- The number of words in a column of the third stage's tree. -/
theorem fr_width23 : PQ.colW (frRd 23).tree = Fmt.M1.wMid frSg3.st := by
  rw [fr_rd]
  rfl

/-- The fourth stage's tree has the positions of that stage's main code. -/
theorem fr_pos30 : PQ.posN (frRd 30).tree = 2 ^ frSg4.C.a := by
  rw [fr_rd]
  rfl

/-- The number of words in a column of the fourth stage's tree. -/
theorem fr_width30 : PQ.colW (frRd 30).tree = Fmt.M1.wMid frSg4.st := by
  rw [fr_rd]
  rfl

/-- The fifth stage's tree has the positions of that stage's main code. -/
theorem fr_pos37 : PQ.posN (frRd 37).tree = 2 ^ frSg5.C.a := by
  rw [fr_rd]
  rfl

/-- The number of words in a column of the fifth stage's tree. -/
theorem fr_width37 : PQ.colW (frRd 37).tree = Fmt.M1.wLast frSg5.st := by
  rw [fr_rd]
  rfl

/-- The five widths as numbers. -/
theorem fr_widths :
    PQ.colW (frRd 1).tree = 645 ∧ PQ.colW (frRd 15).tree = 120 ∧ PQ.colW (frRd 23).tree = 72 ∧
    PQ.colW (frRd 30).tree = 72 ∧ PQ.colW (frRd 37).tree = 12 := by
  rw [fr_width1, fr_width15, fr_width23, fr_width30, fr_width37]
  decide +kernel

/-- What the last round sends and draws. -/
theorem fr_rB : SendsDraws (frRd 40) (frSg5.C.l + frSg5.Z.l + frSg5.C.r + frSg5.Z.r) 0 frSg5.t
    frSg5.C.a :=
  rBase_sd (s := frSg5.st) fr_rd40 (by decide)

/-! ## Work -/

/-- The bits of work that each round asks for: 32 at the link's draws, at the four code switches and
at the last round; none elsewhere. -/
theorem fr_work : frD.ds.map (·.entry.work) =
    [0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0,
    32, 0, 0, 0, 0, 0, 0, 32, 0, 32] := by
  rw [fr_ds]
  rfl

end OnBytes.Slice
