-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/ListAtFits.lean: the table `listAt` (ListAt.lean in this folder) FITS THE
WRITTEN CUTS' ROWS, and the three ends of that file in the form that a law on skeletons can spend.
Closed statements by evaluations in Lean's kernel, and calls.

Why. A law (`ProofFile.Sk.lists_are`) lets a block's file show "the block has no round, or
its rounds are the table's list at its name", and then asks for one closed fact: skeleton by
skeleton, nothing where the skeleton counts no round, else the table's list at its name, in a row,
are the written declared rounds. That is `first_lists` only if the table bears the empty list at
every name whose row counts no round.

Main names.
  `len_first`, `len_shared`, `len_second`: at every row of the written cut the table's list at the
    row's name has as many rounds as the row counts. So a row without a round bears the empty list,
    and a row with rounds has its name in the table.
  `listAt_nil`: the first of these two, as a law.
  `lists_if`: for any list ks with names nm and numbers nr that are a written cut's names and
    numbers of rounds: `ks.flatMap fun k => if nr k = 0 then [] else listAt (nm k)` is what the
    cut's names' lists in a row are.
  `first_if`, `shared_if`, `second_if`: **that, at the three cuts: the written declared rounds.**
  `numbers_first`: the same walk as `walk_first` on the records' NUMBERS, not their values: the two
    lists of runs, laid out, are one list of numbers.
  `len_first_bent`: with one row's number of rounds raised by one, the test says no.

Limits. THAT ANY BLOCK's ROUNDS ARE `listAt` OF ITS NAME IS NOT SAID HERE. Written values.
No soundness is claimed.
-/
import Johnson.AtFull.Rounds.ListAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds

open Johnson.G Johnson.G.Runs
open Johnson.AtFull.ProofRows (declProofFull)
open VerifiableInference.Desc (Place Oracle)
open VerifiableInference.PlanWritten (declRecsFull cutFirstFull cutSharedFull cutSecondFull)

/-- A row of a written cut. -/
abbrev CutRow : Type := String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)

/-- At every row: the table's list at the row's name has as many rounds as the row counts. -/
def lenB (cut : List CutRow) : Bool := cut.all fun r => (listAt r.1).length == r.2.2.1

set_option maxRecDepth 1000000 in
theorem len_first : lenB cutFirstFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem len_shared : lenB cutSharedFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem len_second : lenB cutSecondFull = true := by decide +kernel

/-- A row without a round bears the empty list. -/
theorem listAt_nil {cut : List CutRow} (h : lenB cut = true) {r : CutRow} (hr : r ∈ cut)
    (h0 : r.2.2.1 = 0) : listAt r.1 = [] := by
  have e := List.all_eq_true.1 h r hr
  rw [beq_iff_eq, h0] at e
  exact List.eq_nil_of_length_eq_zero e

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp),
      flatMap_congr_mem fun b hb => h b (by simp [hb])]

/-- **The form that a law on skeletons spends.** -/
theorem lists_if {α : Type} {cut : List CutRow} (hl : lenB cut = true) (ks : List α)
    (nm : α → String) (nr : α → Nat)
    (h : ks.map (fun k => (nm k, nr k)) = cut.map fun r => (r.1, r.2.2.1)) :
    (ks.flatMap fun k => if nr k = 0 then [] else listAt (nm k)) =
      (cut.map (·.1)).flatMap listAt := by
  have e₁ : (ks.flatMap fun k => if nr k = 0 then [] else listAt (nm k)) =
      (ks.map fun k => (nm k, nr k)).flatMap fun p : String × Nat =>
        if p.2 = 0 then [] else listAt p.1 := by
    rw [List.flatMap_map]
  rw [e₁, h, List.flatMap_map, List.flatMap_map]
  refine flatMap_congr_mem fun r hr => ?_
  by_cases h0 : r.2.2.1 = 0
  · rw [if_pos h0, listAt_nil hl hr h0]
  · rw [if_neg h0]

theorem first_if {α : Type} (ks : List α) (nm : α → String) (nr : α → Nat)
    (h : ks.map (fun k => (nm k, nr k)) = cutFirstFull.map fun r => (r.1, r.2.2.1)) :
    (ks.flatMap fun k => if nr k = 0 then [] else listAt (nm k)) = declProofFull.1 :=
  (lists_if len_first ks nm nr h).trans first_lists

theorem shared_if {α : Type} (ks : List α) (nm : α → String) (nr : α → Nat)
    (h : ks.map (fun k => (nm k, nr k)) = cutSharedFull.map fun r => (r.1, r.2.2.1)) :
    (ks.flatMap fun k => if nr k = 0 then [] else listAt (nm k)) = declProofFull.2.1 :=
  (lists_if len_shared ks nm nr h).trans shared_lists

theorem second_if {α : Type} (ks : List α) (nm : α → String) (nr : α → Nat)
    (h : ks.map (fun k => (nm k, nr k)) = cutSecondFull.map fun r => (r.1, r.2.2.1)) :
    (ks.flatMap fun k => if nr k = 0 then [] else listAt (nm k)) = declProofFull.2.2 :=
  (lists_if len_second ks nm nr h).trans second_lists

/-! ## On the records' numbers -/

/-- A list of runs laid out as the records' numbers. -/
def numbersOf (runs : List (Nat × Nat)) : List Nat := runs.flatMap fun x => List.replicate x.1 x.2

set_option maxRecDepth 1000000 in
theorem numbers_first :
    (numbersOf ((cutFirstFull.map (·.1)).flatMap runsAt) == numbersOf dryProofRunsFull0) =
      true := by
  decide +kernel

/-! ## The test can fail -/

set_option maxRecDepth 1000000 in
/-- One row's number of rounds raised by one. -/
theorem len_first_bent : lenB (cutFirstFull.map fun r =>
    if r.1 == "A1:1" then (r.1, r.2.1, r.2.2.1 + 1, r.2.2.2) else r) = false := by decide +kernel

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.len_first
#print axioms Johnson.AtFull.Rounds.len_shared
#print axioms Johnson.AtFull.Rounds.len_second
#print axioms Johnson.AtFull.Rounds.listAt_nil
#print axioms Johnson.AtFull.Rounds.lists_if
#print axioms Johnson.AtFull.Rounds.first_if
#print axioms Johnson.AtFull.Rounds.shared_if
#print axioms Johnson.AtFull.Rounds.second_if
#print axioms Johnson.AtFull.Rounds.numbers_first
#print axioms Johnson.AtFull.Rounds.len_first_bent
