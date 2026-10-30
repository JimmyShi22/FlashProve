-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Walk/LinkLawProofs.lean: two of the three propositions that Johnson/Desc/LinkLaw.lean
states and does not prove, proved. They speak of Johnson/Desc/Block.lean's own text for a link
(orderOk, claimsIn), of no kind.

  everyRunOnce       EveryRunOnce: a link that passes its test on the plan batches every named run
                     of claims exactly once: the order is a rearrangement of all the runs, and
                     names none twice
  claimsAreTheRuns   ClaimsAreTheRuns: what the batching block is handed is the runs' own lists of
                     claims, one after the other, in the order that the link states; the record
                     goes from each run to the next; each run is told how many claims stand before
                     it; where a run refuses or is not there, both sides have nothing
  namesOk_spec, foldl_runs   what the two rest on
  yesToAll_fails, alwaysRefuse_fails, alwaysEmpty_fails   the two statements tried against silly
                     members: a test that says yes to all, a gatherer that always refuses, one that
                     always hands on nothing: none meets its statement

Limits.
The text that they speak of has run in a toy alone: no run of claims is called in the fold over
blocks yet.
A test on the plan that says no to all meets EveryRunOnce emptily: the statement is an implication
from the test's yes: it says nothing of completeness.
ClaimsAreTheRuns compares .toOption: it says nothing of the words of a refusal.
The third proposition, LinkLaw, is not touched.

-/
import Johnson.Desc.LinkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

theorem namesOk_spec {all order : List (ℕ × String)} (h : namesOk all order = true) :
    order.Perm all ∧ order.Nodup := by
  unfold namesOk at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have g1 : ∀ r ∈ all, all.count r = 1 ∧ order.count r = 1 := by
    intro r hr
    have := h1 r hr
    rw [Bool.and_eq_true] at this
    exact ⟨by simpa using this.1, by simpa using this.2⟩
  have g2 : ∀ o ∈ order, o ∈ all := by
    intro o ho
    simpa using h2 o ho
  have hn : order.Nodup := by
    rw [List.nodup_iff_count_le_one]
    intro a
    by_cases ha : a ∈ order
    · exact le_of_eq (g1 a (g2 a ha)).2
    · rw [List.count_eq_zero_of_not_mem ha]
      exact Nat.zero_le 1
  refine ⟨List.perm_iff_count.mpr fun a => ?_, hn⟩
  by_cases ha : a ∈ all
  · rw [(g1 a ha).1, (g1 a ha).2]
  · have hb : a ∉ order := fun hh => ha (g2 a hh)
    rw [List.count_eq_zero_of_not_mem ha, List.count_eq_zero_of_not_mem hb]

/-- **EveryRunOnce.** -/
theorem everyRunOnce : EveryRunOnce := by
  intro S Cl bs order h
  exact namesOk_spec h

/-- One step of claimsIn's fold: Block.lean's own text. -/
def claimsStep {S Cl : Type} (bs : List (Block S Cl)) (acc : Except String (List Cl × S)) (o : ℕ ×
    String) :
    Except String (List Cl × S) :=
  acc.bind fun x =>
    (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.claims.lookup o.2)).bind fun run =>
      match run x.1.length x.2 with
      | .ok y => .ok (x.1 ++ y.1, y.2)
      | .error e => .error (o.2 ++ ": " ++ e)

theorem claimsIn_eq {S Cl : Type} (bs : List (Block S Cl)) (order : List (ℕ × String)) (s : S) :
    claimsIn bs order s = order.foldl (claimsStep bs) (.ok ([], s)) := rfl

theorem foldl_error {S Cl : Type} (bs : List (Block S Cl)) :
    ∀ (os : List (ℕ × String)) (e : String), os.foldl (claimsStep bs) (.error e) = .error e
  | [], _ => rfl
  | _ :: os, e => foldl_error bs os e

theorem foldl_runs {S Cl : Type} (bs : List (Block S Cl)) :
    ∀ (os : List (ℕ × String)) (pre : List Cl) (s : S),
      (os.foldl (claimsStep bs) (.ok (pre, s))).toOption =
        (runsOneByOne bs os pre.length s).map fun x => (pre ++ x.1.flatten, x.2)
  | [], pre, s => by
    simp [runsOneByOne, Except.toOption]
  | o :: os, pre, s => by
    rw [List.foldl_cons]
    cases hl : ((bs[o.1]?).bind fun b => b.claims.lookup o.2) with
    | none =>
      have h1 : claimsStep bs (.ok (pre, s)) o = .error (o.2 ++ ": no such run") := by
        simp [claimsStep, hl, named, Except.bind]
      rw [h1, foldl_error]
      simp [runsOneByOne, hl, Except.toOption]
    | some run =>
      cases hr : run pre.length s with
      | error e =>
        have h1 : claimsStep bs (.ok (pre, s)) o = .error (o.2 ++ ": " ++ e) := by
          simp [claimsStep, hl, named, Except.bind, hr]
        rw [h1, foldl_error]
        simp [runsOneByOne, hl, hr, Except.toOption]
      | ok y =>
        have h1 : claimsStep bs (.ok (pre, s)) o = .ok (pre ++ y.1, y.2) := by
          simp [claimsStep, hl, named, Except.bind, hr]
        rw [h1, foldl_runs bs os (pre ++ y.1) y.2]
        simp [runsOneByOne, hl, hr, Except.toOption, Option.map_map, Function.comp_def,
            List.append_assoc]

/-- **ClaimsAreTheRuns.** -/
theorem claimsAreTheRuns : ClaimsAreTheRuns := by
  intro S Cl bs order s
  rw [claimsIn_eq, foldl_runs bs order [] s]
  simp

/-! ### the two statements tried against silly members -/

/-- A test on the plan that says yes to all does not meet EveryRunOnce: at a link without a run and
  an order that names one. (A test that says no to all meets it emptily: it is an implication from
  the test's yes.) -/
theorem yesToAll_fails :
    ¬ ∀ (order : List (ℕ × String)), order.Perm (allRuns ([] : List (Block Unit Unit))) ∧
        order.Nodup := by
  intro h
  have := (h [(0, "x")]).1
  simp [allRuns] at this

/-- A gatherer that always refuses does not meet ClaimsAreTheRuns: at the empty order the runs one
  by one give the empty list and the record. -/
theorem alwaysRefuse_fails :
    (none : Option (List Unit × Unit)) ≠ (runsOneByOne ([] : List (Block Unit Unit)) [] 0 ()).map
        fun x => (x.1.flatten, x.2) := by
  simp [runsOneByOne]

/-- A block with one run, which states one claim. -/
def oneRun : Block Unit Unit := { (roundlessBlock "toy" 1 none 0 .ok : Block Unit Unit) with claims :=
    [("r", fun _ s => .ok ([()], s))] }

/-- A gatherer that always hands on no claim does not meet ClaimsAreTheRuns: at one run that states
  one claim. -/
theorem alwaysEmpty_fails :
    (some (([] : List Unit), ())) ≠ (runsOneByOne [oneRun] [(0, "r")] 0 ()).map fun x =>
        (x.1.flatten, x.2) := by
  simp [runsOneByOne, oneRun, Except.toOption]

#print axioms namesOk_spec
#print axioms foldl_error
#print axioms foldl_runs
#print axioms yesToAll_fails
#print axioms alwaysRefuse_fails
#print axioms alwaysEmpty_fails
#print axioms everyRunOnce
#print axioms claimsAreTheRuns

end VerifiableInference.Desc
