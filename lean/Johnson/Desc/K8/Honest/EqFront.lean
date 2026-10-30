-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqFront.lean: THE SMALLNESS TEST: WHAT A YES OF ITS RUN "K8.equations" SAYS
OF THE STATE AT WHICH IT RAN: the list of tables is still the list that was closed, and the lookup
on the digits has been heard: OF THE COUNTS THAT THE BLOCK BEHIND THE BATCHING ASKS BESIDE THE
NUMBER OF CLAIMS: AT THE OUTPUT HEAD TWO OF THE THREE; AT THE TWO OTHER SORTS OF SEGMENT THE ONE
THAT THERE IS (`K9.countsAt`, Johnson/Desc/First/Batch/TestsAtS.lean). From the run's yes alone.
Lemmas on the verifier's own text; none of the library's goals.

  `held_of_yes`   where the run's text says yes, its second test has passed: `funsHeld`
  `closed_is_held`   the later block's test `K9.closedList` is `funsHeld`, word for word: rfl
  `parts_of`   the three pieces of the kind's part of a state
  **`tables_of_run`**   AT THE RUN THAT THE KIND's BLOCK STATES: K9.tablesHeld s = true at the state
                   s in front of it
  **`heard_of_run`**   and the count "two lookups" there
  **`counts_of_run`**   SO THE COUNTS BUT THE FIRST, AT THAT STATE: at a layers' and at an attention
                   segment outright; at the output head UNDER ONE PREMISE: the matrix is counted as
                   drawn once
Limits. AT THE STATE AT WHICH THE RUN RAN: inside the gatherer: not at the state in front of the
batching's draw: that what these counts read is the same at the two is not shown here. "THE MATRIX
IS DRAWN ONCE" IS TESTED BY NO LINE OF THE RUN: it stays a premise at the head.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Batch.Law.K8Four
import Johnson.Desc.First.TailClaims.K8Sits
import Johnson.Desc.First.Batch.TestsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open VerifiableInference.Desc.K9L (take_four)

/-- Where the run's text says yes, its second test has passed. -/
theorem held_of_yes {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    tl.funsHeld funs = true := by
  unfold equations at h
  cases e : eqAll tl funs front (F, #[]) with
  | error x => rw [e] at h; cases h
  | ok x =>
    rw [eqAll_split] at e
    obtain ⟨u1, s1, -, k1⟩ := (eq_bind_ok _ _ _ _ _).1 e
    obtain ⟨u2, s2, h2, -⟩ := (eq_bind_ok _ _ _ _ _).1 k1
    exact (eq_must_ok h2).1

/-- The later block's test is the same test, word for word. -/
theorem closed_is_held (tl : HTailF2) (funs : Array HFun) :
    K9.closedList tl funs = tl.funsHeld funs := rfl

/-- The three pieces of the kind's part of a state. -/
theorem parts_of {u : S} {q : K8Part} (h : partOf u = some q) :
    u.tl? = some q.tl ∧ S.funs? u = some q.funs ∧ u.fork? = some q.F := by
  unfold partOf k8PartP at h
  obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨fs, hfs, rfl⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨t, ht, h3⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.1 h3
  exact ⟨ht, hfs, hF⟩

section
variable (p : ParW) (run : Nat → S → Except String (List Claim × S))
  (h : ("K8.equations", run) ∈ (whole p).claims) (front : Nat) (s s' : S) (cls : List Claim)
  (hy : run front s = .ok (cls, s'))
include h hy

/-- **The list of tables is still the list that was closed.** -/
theorem tables_of_run : K9.tablesHeld s = true := by
  obtain ⟨q, tl', F1, hq, he, -⟩ := (sits_equations p run h front s s' cls).1 hy
  obtain ⟨ht, hf, -⟩ := parts_of hq
  unfold K9.tablesHeld
  rw [ht, hf]
  exact (closed_is_held q.tl q.funs).trans (held_of_yes he)

/-- **The lookup on the digits has been heard.** -/
theorem heard_of_run : (s.tl?.map (1 + ·.groupsRun == 2)).getD false = true := by
  obtain ⟨q, tl', F1, hq, he, -⟩ := (sits_equations p run h front s s' cls).1 hy
  obtain ⟨ht, -, -⟩ := parts_of hq
  obtain ⟨g, Fa, hg, -⟩ := take_four he
  rw [ht]
  simp [groupsRun, hg]

/-- **The counts but the first, at the state at which the run ran.** -/
theorem counts_of_run (k : K9.SegSort) (n : Nat)
    (hd : k = .head → (s.tl?.map (·.foldDrawn == 1)).getD false = true) :
    ((K9.countsAt k n).tail.all fun q => q.2 s) = true := by
  have hT := tables_of_run p run h front s s' cls hy
  have hH := heard_of_run p run h front s s' cls hy
  cases k with
  | layers =>
    simp only [K9.countsAt, List.tail_cons, List.all_cons, List.all_nil, Bool.and_true]
    exact hT
  | attention =>
    simp only [K9.countsAt, List.tail_cons, List.all_cons, List.all_nil, Bool.and_true]
    exact hT
  | head =>
    simp only [K9.countsAt, List.tail_cons, List.all_cons, List.all_nil, Bool.and_true]
    rw [hd rfl, hH, hT]
    rfl

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.held_of_yes
#print axioms VerifiableInference.Desc.First.K8.Honest.closed_is_held
#print axioms VerifiableInference.Desc.First.K8.Honest.parts_of
#print axioms VerifiableInference.Desc.First.K8.Honest.tables_of_run
#print axioms VerifiableInference.Desc.First.K8.Honest.heard_of_run
#print axioms VerifiableInference.Desc.First.K8.Honest.counts_of_run
