-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FixedLaw.lean: what the test on the plan `fixedOk` of a proximity test (the
kind K12) says, as propositions.

No Mathlib beneath. Where `fixedOk` (Johnson/Desc/K12/FixedBefore.lean) says yes, every tree that a
stage's switch opens is fixed in front of the first draw of that stage's fold, and every tree that
the base case opens is fixed in front of the base case's first round, in the sense of `Fixed`. A law
on a fold with a mask asks that the mask's word is fixed before the fold's first draw; these
theorems are the kind's share of that premise.
Main names:
  `Fixed chain before N rds start o`: the opened tree `o` is fixed in front of round number `start`.
    An own tree that was sent in front of the test, or a tree of another chain, is named in
    `before`; an own tree that the test itself sends has a number below the count of the chain's own
    trees sent in front of round `start`.
  `foldStart i l j`: the number of the first round of stage j's fold, by the frame's own arithmetic:
    k + 3 rounds a stage.
  `fixed_switch`: at every stage but the last, every tree that the switch's two rounds open is
    `Fixed` at the round behind the first round of that stage's fold: it was sent in a round before
    the fold, or in the fold's first round, whose message stands in front of its draw.
  `fixed_base`: every tree that the base case's two rounds open is `Fixed` at the base case's first
    round.
Limits: That what `before` names was sent in time is not said here; that is `beforeAt` of
Johnson/Desc/Block.lean. That a tree holds the mask's word is not said here. `fixedOk` reads the
count of the chain's trees in front of the test (`free`) off the same numbers of which the declared
rounds are made: for the trees that the test itself sends a wrong `free` shifts both sides alike, so
this test does not catch it. That `free` is the record's count of roots is asked at a run by the
block's own guard at its front (Johnson/Desc/K12/JoinGuarded.lean). `fixedFrom` also tests each fold's
slice, and `fixedOk` the batching's round; no theorem here reads these two, which are idle where a
fold and the batching open nothing. Nothing is said on an error or on soundness.

-/
import Johnson.Desc.K12.FixedBefore

set_option autoImplicit false
namespace H2K.FixedBefore
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- A tree that is opened is fixed in front of the round number `start`. -/
def Fixed (chain : Nat) (before : List (Nat × Nat)) (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (start : Nat) (o : Fmt.Shape × Fmt.TreeSource) : Prop :=
  match o.2 with
  | .own n => (n < N.free ∧ (chain, n) ∈ before) ∨ (N.free ≤ n ∧ n < sentIn N rds start)
  | .taken c n => (c + 1, n) ∈ before

/-- What a yes of `fixedAt` says. -/
theorem fixed_of_at (chain : Nat) (before : List (Nat × Nat)) (N : H2U.TestNums)
    (rds : List Fmt.DeclaredRound) (start : Nat) (o : Fmt.Shape × Fmt.TreeSource)
    (h : fixedAt chain before N rds start o = true) : Fixed chain before N rds start o := by
  unfold fixedAt at h
  unfold Fixed
  split at h
  · rename_i n hn
    simp only [hn]
    split at h
    · rename_i hlt
      exact Or.inl ⟨hlt, by simpa using h⟩
    · rename_i hge
      exact Or.inr ⟨Nat.le_of_not_lt hge, by simpa using h⟩
  · rename_i c n hn
    simp only [hn]
    simpa using h

/-- What a yes of `sliceOk` says. -/
theorem fixed_of_slice (chain : Nat) (before : List (Nat × Nat)) (N : H2U.TestNums)
    (rds : List Fmt.DeclaredRound) (start len fix : Nat)
    (h : sliceOk chain before N rds start len fix = true) :
    ∀ r ∈ (rds.drop start).take len, ∀ o ∈ r.opens, Fixed chain before N rds fix o := by
  intro r hr o ho
  unfold sliceOk at h
  rw [List.all_eq_true] at h
  have h1 := h r hr
  rw [List.all_eq_true] at h1
  exact fixed_of_at _ _ _ _ _ _ (h1 o ho)

/-- The first round of stage number j's fold, from the first round i of the stages l. -/
def foldStart (i : Nat) (l : List Fmt.M1.Stage) (j : Nat) : Nat :=
  i + ((l.take j).map (·.k + 3)).sum

/-- The switches: stage number j of `cur :: rest`, a stage but the last. -/
theorem slice_switch (chain : Nat) (before : List (Nat × Nat)) (N : H2U.TestNums)
    (rds : List Fmt.DeclaredRound) : ∀ (rest : List Fmt.M1.Stage) (i : Nat) (cur : Fmt.M1.Stage),
    fixedFrom chain before N rds i cur rest = true → ∀ (j : Nat) (s : Fmt.M1.Stage),
    j < rest.length →
    (cur :: rest)[j]? = some s →
    sliceOk chain before N rds (foldStart i (cur :: rest) j + 1 + s.k) 2
      (foldStart i (cur :: rest) j + 1) = true := by
  intro rest
  induction rest with
  | nil => intro i cur _ j s hj; simp at hj
  | cons next rest ih =>
    intro i cur h j s hj hs
    simp only [fixedFrom, Bool.and_eq_true] at h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      simpa [foldStart] using h.1.2
    | succ j =>
      have hj' : j < rest.length := by simpa using hj
      have hs' : (next :: rest)[j]? = some s := by simpa using hs
      have := ih (i + cur.k + 3) next h.2 j s hj' hs'
      have e : foldStart i (cur :: next :: rest) (j + 1) =
          foldStart (i + cur.k + 3) (next :: rest) j := by
        simp only [foldStart, List.take_succ_cons, List.map_cons, List.sum_cons]
        omega
      rw [e]
      exact this

/-- The base case. -/
theorem slice_base (chain : Nat) (before : List (Nat × Nat)) (N : H2U.TestNums)
    (rds : List Fmt.DeclaredRound) : ∀ (rest : List Fmt.M1.Stage) (i : Nat) (cur : Fmt.M1.Stage),
    fixedFrom chain before N rds i cur rest = true →
    sliceOk chain before N rds (foldStart i (cur :: rest) rest.length) 2
      (foldStart i (cur :: rest) rest.length) = true := by
  intro rest
  induction rest with
  | nil => intro i cur h; simpa [fixedFrom, foldStart] using h
  | cons next rest ih =>
    intro i cur h
    simp only [fixedFrom, Bool.and_eq_true] at h
    have := ih (i + cur.k + 3) next h.2
    have e : foldStart i (cur :: next :: rest) (next :: rest).length =
        foldStart (i + cur.k + 3) (next :: rest) rest.length := by
      simp only [foldStart, List.length_cons, List.take_succ_cons, List.map_cons, List.sum_cons]
      omega
    rw [e]
    exact this

/-- What a yes of `fixedOk` holds. -/
theorem fixedOk_gives (p : P12) (h : fixedOk p = true) :
    ∃ (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (rds : List Fmt.DeclaredRound),
      p.nums.stages = first :: rest ∧ H2U.roundsOfNums p.nums = some rds ∧
      fixedFrom p.place.chain p.before p.nums rds 1 first rest = true := by
  unfold fixedOk at h
  split at h
  · rename_i first rest rds h1 h2
    simp only [Bool.and_eq_true] at h
    exact ⟨first, rest, rds, h1, h2, h.2⟩
  · cases h

/-- At every switch of the test. j is the stage's number, from 0; s is that stage. -/
theorem fixed_switch (p : P12) (h : fixedOk p = true) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds) (j : Nat) (s : Fmt.M1.Stage)
    (hj : j + 1 < p.nums.stages.length) (hs : p.nums.stages[j]? = some s) :
    ∀ r ∈ (rds.drop (foldStart 1 p.nums.stages j + 1 + s.k)).take 2, ∀ o ∈ r.opens,
      Fixed p.place.chain p.before p.nums rds (foldStart 1 p.nums.stages j + 1) o := by
  obtain ⟨first, rest, rds', h1, h2, h3⟩ := fixedOk_gives p h
  have e : rds' = rds := by rw [h2] at hr; exact Option.some.inj hr
  subst e
  rw [h1] at hj hs ⊢
  exact fixed_of_slice _ _ _ _ _ _ _
    (slice_switch _ _ _ _ rest 1 first h3 j s (by simpa using hj) hs)

/-- At the base case. -/
theorem fixed_base (p : P12) (h : fixedOk p = true) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds) :
    ∀ r ∈ (rds.drop (foldStart 1 p.nums.stages (p.nums.stages.length - 1))).take 2, ∀ o ∈ r.opens,
      Fixed p.place.chain p.before p.nums rds
        (foldStart 1 p.nums.stages (p.nums.stages.length - 1)) o := by
  obtain ⟨first, rest, rds', h1, h2, h3⟩ := fixedOk_gives p h
  have e : rds' = rds := by rw [h2] at hr; exact Option.some.inj hr
  subst e
  rw [h1]
  simp only [List.length_cons, Nat.add_sub_cancel]
  exact fixed_of_slice _ _ _ _ _ _ _ (slice_base _ _ _ _ rest 1 first h3)

end H2K.FixedBefore
