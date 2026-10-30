--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/CountLaws.lean: the proximity test (the kind K12): how many rounds the rounds'
maker gives (Johnson/Desc/K12/TestEntries.lean: `H2U.roundsOfNums`), for all numbers of a place.
Theorems; no code.

  laterRounds_length   the landed `Fmt.M1.laterRounds` gives k + 3 rounds for each stage but the
      last, and 2 for the last.
  layOpens_length      laying the lists of trees in turns no round's number.
  roundsOfNums_length  **wherever the maker gives rounds, they are as many as the frame counts**
      (`roundsIn`: 1, then k + 3 for each stage but the last, then 2).
  rounds_conjunct_idle so the conjunct "as many rounds as the counts add up to" of the block's test
      on the plan can never be the one that fails: no number of a place reaches it.
What it is for: that conjunct has no control, because no input makes it false: here that is a
theorem, not a reading. Nothing on what a round holds. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12
open Fmt.M1 (Stage)

theorem laterRounds_length (work : Nat) (rest : List Stage) :
    ∀ (tree W : Nat) (old : Stage),
      (Fmt.M1.laterRounds work tree W old rest).length =
        ((old :: rest).dropLast.map (·.k + 3)).sum + 2 := by
  induction rest with
  | nil => intro tree W old; simp [Fmt.M1.laterRounds]
  | cons new rest ih =>
    intro tree W old
    simp only [Fmt.M1.laterRounds, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate, ih, List.dropLast_cons₂, List.map_cons, List.sum_cons]
    omega

theorem layOpens_length (own : Bool) (rs : List Fmt.Round) :
    ∀ (seen : Bool) (l : List (List (Fmt.Shape × Fmt.TreeSource))) (ds : List Fmt.DeclaredRound),
      H2U.layOpens own seen rs l = some ds → ds.length = rs.length := by
  induction rs with
  | nil =>
    intro seen l ds h
    cases l with
    | nil => simp [H2U.layOpens] at h; simp [← h]
    | cons x t => simp [H2U.layOpens] at h
  | cons r rs ih =>
    intro seen l ds h
    simp only [H2U.layOpens] at h
    split at h
    · cases hq : H2U.layOpens own (seen || r.entry.name == "FOLD epsilon") rs l with
      | none => simp [hq] at h
      | some a => simp [hq] at h; simp [← h, ih _ _ _ hq]
    · split at h
      · rename_i x t
        split at h
        · simp at h
        · cases hq : H2U.layOpens own (seen || r.entry.name == "FOLD epsilon") rs t with
          | none => simp [hq] at h
          | some a => simp [hq] at h; simp [← h, ih _ _ _ hq]
      · simp at h

/-- **Wherever the maker gives rounds, they are as many as the frame counts.** -/
theorem roundsOfNums_length (N : H2U.TestNums) (ds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some ds) : ds.length = roundsIn N.stages := by
  unfold H2U.roundsOfNums at h
  split at h
  · rename_i s next rest hs
    have := layOpens_length _ _ _ _ _ h
    simp only [this, hs, roundsIn, List.length_cons, laterRounds_length]
    omega
  · simp at h

/-- The conjunct on the number of rounds never fails where the maker gives rounds. -/
theorem rounds_conjunct_idle (p : P12) (ds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums p.nums = some ds) : (ds.length == roundsIn p.nums.stages) = true := by
  simp [roundsOfNums_length _ _ h]

end VerifiableInference.Desc.K12
