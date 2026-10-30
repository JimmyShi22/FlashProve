-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/MemberTeeth.lean: negative tests. Where the tests around the smallness test's
first half (Johnson/Desc/First/K8/Hear.lean) say no; two limits of what these tests can tell; and a
weakened seat at which a row's law fails, at a written round. (A row: a proposition stated by name,
with a theorem of just that type. The state: what the verifier carries along the first chain, which
the docstrings below call the record. Both words: the head of Johnson/Desc/First/K8/Member.lean.)

What it shows. One negative test is on a row's own statement: with the seat's reading of the state's
columns made idle, the law `ConditionAt` is false (`weak_conditionAt`): so that law could fail, and
the columns' half of the kind's test (e) carries weight. The others show that the tests `placeOk`
and `settingB` and the property `Ready`, on which the example in Johnson/Desc/First/K8/Member.lean
is built, can say no.

Statements and proofs.
  The place. `firstSort`: the declared form of the first sort of the written rounds;
    `firstSort_written`: it is that of a round of the written list. `placeOk`
    (Johnson/Desc/First/K8/MemberPlace.lean) at the default setting, that round and a place with
    made-up lists (`madeUpPar 24085`: matrices of 1 and 24,085 columns; the messages 0 and 1):
    `place_yes` (the positive case); `place_tau_no` (127 combinations: the first clause and the
    third say no: it isolates neither), `place_column_no` (one column more), `place_none_no` (no
    matrix: the first clause and the second say no), `place_message_no`, `place_reads_no` (no
    message named): no.
  A limit: `round_half_tau`: the place with 48,172 columns and 64 combinations (`halfPar`) declares
    the same round as the one with 24,086 and 128. `place_half_tau`: at a setting that gives 64
    combinations (target 64, no work), `placeOk` says yes of it, at the written round. So the
    declared round pins the product alone. The planner prices such a round at 2 ^ -combinations
    (`planRng`, OnBytes/Params/Planner.lean): at 64 combinations that is 2 ^ -64, under the very
    round of the written plan; no theorem here is on that price. `place_half_no`: at the default
    setting the third clause of `placeOk` refuses it; it differs from `place_half_tau` in the
    setting alone. `place_work_no`: at the target 128 with 64 bits of work for this round
    (`workSetting`), which also gives 64 combinations (`work_combinations`), the third clause
    refuses it: the planner's entry would bear the work. A second limit: `place_two_yes`: at the
    target 127 with two instances (`twoSetting`), which gives 128 combinations (`two_combinations`),
    `placeOk` says yes of the positive case's place: it does not read the instances.
  The setting. `settingB` (Johnson/Desc/First/K8/MemberPlace.lean): `default_setting`
    (Johnson/Desc/First/K8/Member.lean) is the positive case; `setting_half_no`, `setting_work_no`,
    `setting_two_no`: it refuses the three settings above (at the second, its first clause and its
    second say no). What keeps 128 is the setting, and that the place's number is the setting's: no
    number of the round.
  The state. `not_ready`: a state in which one of seven conditions of `ReadyAt` fails is not ready
    (those of the clauses `closed`, `nothingOwed`, `notDrawn`, which is double, `matrices`, `ks`,
    `tau`; the clauses `ms` and `tabs` are not among them); `not_ready_outside`: nor is one in which
    no link is open; `refused_of_not_ready`: there the step refuses, on whatever rounds and columns.
    The first two take `ReadyAt` apart; the third is the contrapositive of `ready_of_step`. They are
    rules, not tests at a value: the one value at which a state is shown not ready is in
    `true_seat_refuses` (the clause `ks`).
  The view. `two_refused`: a round that shows the matrix entry 2 is refused, whatever the state: by
    the frame's test on the rounds.
  A weakened seat. `weakSeat p`: the seat with the reading of the state's columns made idle. The
    kind's text is untouched: its test (e) runs, and its half on the columns compares the place's
    list with itself. `ks_of_fits`: `Fits` at the library's sizes of a state that has as many
    matrices as it says pins the list of columns. `weak_conditionAt`: at the first sort of the
    written rounds (`tooth_atWritten`): the state has matrices of 1 and 24,085 columns, the place's
    list is [2, 24084] (`toothPar`): the same number of matrices, the same sum, so the same declared
    round (`tooth_round`); `toothRoundAt c` is the round that the law speaks of at c. With the
    weakened seat the law `ConditionAt` (Johnson/Desc/First/K8/LawTeeth.lean: the first half of the
    row `K08ConditionHearing`, of any family of blocks) fails at every written verifier message. The
    kind's own text with its own seat has that law (`hear_conditionAt`, same file), and refuses that
    place at that state (`true_seat_refuses`). So the plan's round pins the sum; it is that half of
    test (e), with the seat's reading, that pins the list.

Limits. The splits, the messages and the states are made up: no plan's, no run's; the matrices have
0 rows, and there are no asks and no tables, with the further limits that the head of
Johnson/Desc/First/K8/Member.lean tells of that state. Of the negative tests one is on a row's
statement (`weak_conditionAt`); those on the place are on `placeOk`, those on the setting on
`settingB`: premises of no row; those on the state are rules (above); the one on the view is the
frame's. No test here is aimed at the matrices' rows, the asks or the tables: so nothing here shows
that the two clauses of `placeOk` on them, or the clauses `ms` and `tabs` of `ReadyAt`, can fail.
The closed tests are by `decide`. Nothing on soundness.
-/
import Johnson.Desc.First.K8.Member

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Member

open VerifiableInference.Number (isSmall)
open VerifiableInference.Number.Written (written_shape exists_written)
open OnBytes.Params (Setting rngCombinations)
open Johnson.G (dryProofFull)
open Iop Prob Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
  OnBytes.Tie.Pv.Row OnBytes.Tie.Pv.Tail KObj VerifiableInference.OnPublicFiles

/-! ## The place -/

/-- The declared form of the first sort of the written rounds. -/
def firstSort : Fmt.DeclaredRound := { entry := { name := "RNG", trits := 3083008 } }

/-- It is the declared form of a round of the written list. -/
theorem firstSort_written :
    ∃ x ∈ dryProofFull.1, isSmall x.1.entry = true ∧
      ({ entry := x.1.entry } : Fmt.DeclaredRound) = firstSort ∧ x.1.opens = [] ∧ x.2 = [] := by
  obtain ⟨x, hx, hs, e⟩ := exists_written (n := 3083008) (by decide)
  obtain ⟨a, _, _, ho, hst, _⟩ := written_shape hx hs
  have he : x.1.entry = { name := "RNG", trits := x.1.entry.trits } := a
  refine ⟨x, hx, hs, ?_, ho, hst⟩
  rw [he, e]
  rfl

theorem place_yes : placeOk {} (madeUpPar 24085) firstSort = true := by decide
theorem place_tau_no : placeOk {} { madeUpPar 24085 with tau := 127 } firstSort = false := by
  decide
theorem place_column_no : placeOk {} (madeUpPar 24086) firstSort = false := by decide
theorem place_none_no : placeOk {} { madeUpPar 24085 with ks := [] } firstSort = false := by
  decide
theorem place_message_no :
    placeOk {} { madeUpPar 24085 with matsIn := [] } firstSort = false := by decide
theorem place_reads_no : placeOk {} { madeUpPar 24085 with readsIn := [] } firstSort = false := by
  decide

/-! ## A limit: the declared round pins the product alone -/

/-- Twice the columns at half the combinations. -/
def halfPar : Par := { madeUpPar 24085 with ks := [48172], ms := [0], tau := 64 }

/-- **It declares the same round.** -/
theorem round_half_tau : round halfPar = round (madeUpPar 24085) := by decide

/-- **A limit**: at a setting whose target is 64 the test on the place says yes of it, at the
written round. -/
theorem place_half_tau : placeOk { target := 64 } halfPar firstSort = true := by decide

/-- At the default setting the clause on the setting refuses it. -/
theorem place_half_no : placeOk {} halfPar firstSort = false := by decide

/-- The target 128 with 64 bits of work for this round: 64 combinations. -/
def workSetting : Setting := { workSmall := ⟨64, 64, 64⟩ }

theorem work_combinations : rngCombinations workSetting .request = 64 := by decide

/-- There the clause on the setting refuses it too: the planner's entry would bear the work. -/
theorem place_work_no : placeOk workSetting halfPar firstSort = false := by decide

/-- The target 127 with two instances: 128 combinations. -/
def twoSetting : Setting := { target := 127, instances := 2 }

theorem two_combinations : rngCombinations twoSetting .request = 128 := by decide

/-- **A second limit**: the test on the place does not read the instances. -/
theorem place_two_yes : placeOk twoSetting (madeUpPar 24085) firstSort = true := by decide

/-! ## The setting -/

theorem setting_half_no : settingB { target := 64 } = false := by decide
theorem setting_work_no : settingB workSetting = false := by decide
theorem setting_two_no : settingB twoSetting = false := by decide

/-! ## The record -/

/-- One of seven conditions fails (the clauses `ms` and `tabs` are not among them). -/
theorem not_ready {p : Par} {st : S} {tl : HTailF2} (ht : st.tl? = some tl)
    (h : tl.funClosed = false ∨ (∃ n, st.rowsOwed = some (n + 1)) ∨ tl.cfF.size ≠ 0 ∨
      tl.foldDrawn ≠ 0 ∨ tl.NM ≠ p.ks.length ∨ tl.mats.toList.map (·.k) ≠ p.ks ∨ tl.tau ≠ p.tau) :
    ¬ Ready p st := by
  rintro ⟨t, R⟩
  obtain rfl : t = tl := Option.some.inj (R.link.symm.trans ht)
  rcases h with h | ⟨n, h⟩ | h | h | h | h | h
  · rw [R.closed] at h
    cases h
  · rcases R.nothingOwed with e | e
    · rw [e] at h
      cases h
    · rw [e] at h
      cases h
  · exact h R.notDrawn.1
  · exact h R.notDrawn.2
  · exact h R.matrices
  · exact h R.ks
  · exact h R.tau

/-- No link is open. -/
theorem not_ready_outside {p : Par} {st : S} (ht : st.tl? = none) : ¬ Ready p st := by
  rintro ⟨t, R⟩
  have e := R.link
  rw [ht] at e
  cases e

/-- **Where the record is not ready the step refuses.** -/
theorem refused_of_not_ready {Cl : Type} {p : Par} {st : S} (h : ¬ Ready p st) (ft : Nat)
    (rs : List Fmt.RoundView) (cols : List Col) (st' : S) (n : Nat) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st rs cols ≠ .ok (st', n) := fun e => h (ready_of_step e)

/-! ## The view -/

/-- **A matrix entry 2 is refused.** -/
theorem two_refused {S' Cl : Type} (seat : Seat S') (p : Par) (ft : Nat) (st st' : S')
    (r : Fmt.RoundView) (cols : List Col) (n : Nat) (h2 : (2 : Int) ∈ r.drawn.trits) :
    (approximateRangeProofDrawKind (Cl := Cl) seat p).step ft st [r] cols ≠ .ok (st', n) := by
  intro e
  obtain ⟨_, r', er, hfit, _⟩ := step_ok seat p ft st st' [r] cols n e
  obtain rfl : r = r' := by simpa using er
  simp only [roundsFit, Bool.and_eq_true, List.all_eq_true] at hfit
  have := hfit.1.1.2 2 h2
  simp at this

/-! ## A weakened seat -/

/-- The seat with the reading of the record's columns made idle. -/
def weakSeat (p : Par) : Seat S := { atS with ks := fun _ => p.ks }

/-- `Fits` at the library's sizes of a record pins the list of columns. -/
theorem ks_of_fits {p : Par} {tl : HTailF2} (hN : tl.NM = tl.mats.size)
    (h : Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl).size) : tl.mats.toList.map (·.k) = p.ks := by
  have g := fits_parOf tl hN p.link p.piece p.matsIn p.readsIn p.asks
  have hl : (tl.mats.toList.map (·.k)).length = p.ks.length := g.nm.symm.trans h.nm
  refine List.ext_getElem hl fun i h1 h2 => ?_
  have a := g.k i h1
  have b := h.k i h2
  have e : (tl.mats.toList.map (·.k)).getD i 0 = p.ks.getD i 0 := a.symm.trans b
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at e
  exact e

/-- The changed place: two matrices, of 2 and 24,084 columns. -/
def toothPar : Par := { madeUpPar 24085 with ks := [2, 24084] }

/-- It fits a written round of the first sort, at the default setting. -/
theorem tooth_atWritten : ∃ x, x.1.entry.trits = 3083008 ∧ AtWritten {} toothPar x := by
  obtain ⟨x, hx, hs, e⟩ := exists_written (n := 3083008) (by decide)
  refine ⟨x, e, hx, hs, default_combinations.symm, (settingB_yes default_setting).2.1, ?_,
    by decide, by decide, rfl, fun _ h => nomatch h⟩
  rw [e]
  decide

/-- It declares the round that the record's own list would declare. -/
theorem tooth_round : round toothPar = round (madeUpPar 24085) := by decide

/-- For comparison: the kind's text with its own seat refuses that place at the record with matrices
of 1 and 24,085 columns, on whatever rounds and columns. -/
theorem true_seat_refuses {Cl : Type} (ft : Nat) (rs : List Fmt.RoundView) (cols : List Col) (st' : S)
    (n : Nat) :
    (approximateRangeProofDrawKind (Cl := Cl) atS toothPar).step ft (toyIn (madeUpTl 24085)) rs cols ≠ .ok (st', n) :=
  refused_of_not_ready
    (not_ready (tl := madeUpTl 24085) rfl
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))))) ft rs cols st' n

/-- The round that the law speaks of at that place, at c. -/
def toothRoundAt (c : (wRound (rd toothPar)).Chal) : Fmt.RoundView := ⟨[], ⟨[], [], kitTrits c, none⟩⟩

/-- **With the weakened seat the law fails**, at every written verifier message of that place: the
record has matrices of 1 and 24,085 columns. -/
theorem weak_conditionAt (c : (wRound (rd toothPar)).Chal) :
    ¬ ConditionAt (fun p => approximateRangeProofDrawKind (Cl := Unit) (weakSeat p) p) toothPar c := fun h => by
  have hf := fits_sizeAt toothPar (OnBytes.Tie.Pv.Tail.sizeOf (madeUpTl 24085)).size
  have hs := (hear_law (Cl := Unit) hf (weakSeat toothPar) c 0 (toyIn (madeUpTl 24085)) _ 0 []
    (toothRoundAt c) rfl rfl rfl rfl).2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have e := ks_of_fits (tl := madeUpTl 24085) rfl
    (h (madeUpTl 24085) 0 _ _ 0 [] (toothRoundAt c) rfl rfl rfl rfl rfl hs)
  exact absurd e (by decide)

end VerifiableInference.Desc.First.K8.Member

#print axioms VerifiableInference.Desc.First.K8.Member.firstSort_written
#print axioms VerifiableInference.Desc.First.K8.Member.place_yes
#print axioms VerifiableInference.Desc.First.K8.Member.place_tau_no
#print axioms VerifiableInference.Desc.First.K8.Member.place_column_no
#print axioms VerifiableInference.Desc.First.K8.Member.place_none_no
#print axioms VerifiableInference.Desc.First.K8.Member.place_message_no
#print axioms VerifiableInference.Desc.First.K8.Member.place_reads_no
#print axioms VerifiableInference.Desc.First.K8.Member.round_half_tau
#print axioms VerifiableInference.Desc.First.K8.Member.place_half_tau
#print axioms VerifiableInference.Desc.First.K8.Member.place_half_no
#print axioms VerifiableInference.Desc.First.K8.Member.work_combinations
#print axioms VerifiableInference.Desc.First.K8.Member.place_work_no
#print axioms VerifiableInference.Desc.First.K8.Member.two_combinations
#print axioms VerifiableInference.Desc.First.K8.Member.place_two_yes
#print axioms VerifiableInference.Desc.First.K8.Member.setting_half_no
#print axioms VerifiableInference.Desc.First.K8.Member.setting_work_no
#print axioms VerifiableInference.Desc.First.K8.Member.setting_two_no
#print axioms VerifiableInference.Desc.First.K8.Member.not_ready
#print axioms VerifiableInference.Desc.First.K8.Member.not_ready_outside
#print axioms VerifiableInference.Desc.First.K8.Member.refused_of_not_ready
#print axioms VerifiableInference.Desc.First.K8.Member.two_refused
#print axioms VerifiableInference.Desc.First.K8.Member.ks_of_fits
#print axioms VerifiableInference.Desc.First.K8.Member.tooth_atWritten
#print axioms VerifiableInference.Desc.First.K8.Member.tooth_round
#print axioms VerifiableInference.Desc.First.K8.Member.true_seat_refuses
#print axioms VerifiableInference.Desc.First.K8.Member.weak_conditionAt
