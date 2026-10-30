-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/MadeRounds.lean: the declared rounds of a proximity test, as `H2U.roundsOfNums`
makes them of the place's numbers, written out stage by stage.

`H2U.roundsOfNums` (Johnson/Desc/K12/TestEntries.lean) makes the declared rounds: a plan chooses the
numbers (the stages, ownMask, first, free, firstTree, rows, work), never what a later switch or the
base case opens. So what several tests on the plan ask of these rounds are theorems (DealMade.lean,
EntriesMade.lean, TieOkMade.lean). Statements and proofs.
Main names:
  `lay_quiet`, `lay_opens`, `lay_rep`, `lay_eps`: `H2U.layOpens` on one round, or on a run of like
    rounds.
  `epsE own seen`: the entry of a "FOLD epsilon": the first one has 32 bytes and a root more where
    the first fold sends its own mask. `epsE_name`, `epsE_roots`: that entry's name and its number
    of roots.
  `lay_stage`: a stage but the last is laid as "FOLD epsilon", k times "FOLD round", "SEND seed",
    then "CS" with the next list of trees, which is not empty; none of the others opens anything.
  `lay_base`: the base case is laid as "BASE lambda", then "BASE" with the one list that is left.
  `told N`: the trees that the test sends, as they are told: number i has the source "own", number
    free + i. `told_at`, `told_drop`: its member number n.
  `rounds_top`: the declared rounds are "BAT", which opens nothing, and then the stages; the first
    list is N.first and then the own mask's tree where there is one; each later list is one told
    tree.
  `rounds_head`: the declared rounds written out down to the first switch's second round.
Limits: nothing is said of a view, a record or a transcript. That the block's rounds are these is
`k12_rounds` (StepGroups.lean). No soundness is claimed, and nothing is said on hiding.

-/
import Johnson.Desc.K12.Law.DealOk

set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (rEps rTwo rSeed rCs rLambda rBase laterRounds wMid)

abbrev Op : Type := Fmt.Shape × Fmt.TreeSource

/-- A round that opens nothing, behind a "FOLD epsilon": laid with its own entry. -/
theorem lay_quiet (own : Bool) (r : Fmt.Round) (rs : List Fmt.Round) (l : List (List Op))
    (h : r.opens = []) :
    H2U.layOpens own true (r :: rs) l =
      (H2U.layOpens own true rs l).map (⟨r.entry, [], []⟩ :: ·) := by
  rw [H2U.layOpens.eq_def]
  simp [h]

/-- A round that opens a tree, behind a "FOLD epsilon". -/
theorem lay_opens (own : Bool) (r : Fmt.Round) (rs : List Fmt.Round) (l : List (List Op))
    (R : List Fmt.DeclaredRound) (h : r.opens ≠ [])
    (hR : H2U.layOpens own true (r :: rs) l = some R) :
    ∃ x t R', l = x :: t ∧ x ≠ [] ∧ H2U.layOpens own true rs t = some R' ∧
      R = ⟨r.entry, [], x⟩ :: R' := by
  rw [H2U.layOpens.eq_def] at hR
  simp only [List.isEmpty_iff, h, if_false] at hR
  cases l with
  | nil => simp at hR
  | cons x t =>
    simp only at hR
    split at hR
    · cases hR
    · rename_i hx
      obtain ⟨R', h1, rfl⟩ := Option.map_eq_some_iff.1 hR
      refine ⟨x, t, R', rfl, hx, ?_, ?_⟩
      · simpa using h1
      · simp

theorem lay_rep (own : Bool) (r : Fmt.Round) (h : r.opens = []) (rs : List Fmt.Round)
    (l : List (List Op)) : ∀ k : Nat,
    H2U.layOpens own true (List.replicate k r ++ rs) l =
      (H2U.layOpens own true rs l).map (List.replicate k (⟨r.entry, [], []⟩ : Fmt.DeclaredRound) ++ ·)
  | 0 => by simp
  | k + 1 => by
    rw [List.replicate_succ, List.cons_append, lay_quiet own r _ l h, lay_rep own r h rs l k,
      Option.map_map]
    rfl

/-- The entry of a "FOLD epsilon": the first one has a root more where the first fold sends its own
mask. -/
def epsE (own seen : Bool) : Fmt.Entry :=
  if own && !seen then
    { (rEps "FOLD epsilon").entry with msg := 32 + (rEps "FOLD epsilon").entry.msg, roots := 1 }
  else (rEps "FOLD epsilon").entry

theorem lay_eps (own seen : Bool) (rs : List Fmt.Round) (l : List (List Op)) :
    H2U.layOpens own seen (rEps "FOLD epsilon" :: rs) l =
      (H2U.layOpens own true rs l).map (⟨epsE own seen, [], []⟩ :: ·) := by
  rw [H2U.layOpens.eq_def]
  simp [rEps, epsE]

/-- A stage but the last, as it is laid. -/
theorem lay_stage (own seen : Bool) (work tree W : Nat) (old new : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (ls : List (List Op)) (R : List Fmt.DeclaredRound)
    (h : H2U.layOpens own seen (laterRounds work tree W old (new :: rest)) ls = some R) :
    ∃ x t R', ls = x :: t ∧ x ≠ [] ∧
      H2U.layOpens own true (laterRounds work (tree + 1) (wMid new) new rest) t = some R' ∧
      R = (⟨epsE own seen, [], []⟩ ::
          List.replicate old.k (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
        (⟨(rSeed new).entry, [], []⟩ :: ⟨(rCs work old tree W).entry, [], x⟩ :: R') := by
  have e : laterRounds work tree W old (new :: rest) = rEps "FOLD epsilon" ::
      (List.replicate old.k (rTwo "FOLD round") ++ (rSeed new :: rCs work old tree W ::
        laterRounds work (tree + 1) (wMid new) new rest)) := by
    simp [laterRounds]
  rw [e, lay_eps, lay_rep own _ rfl, lay_quiet own (rSeed new) _ _ rfl] at h
  obtain ⟨R1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨R2, h2, rfl⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨R3, h3, rfl⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨x, t, R', rfl, hx, h4, rfl⟩ := lay_opens own _ _ _ _ (by simp [rCs]) h3
  exact ⟨x, t, R', rfl, hx, h4, by simp⟩

/-- The base case, as it is laid. -/
theorem lay_base (own : Bool) (work tree W : Nat) (old : Fmt.M1.Stage) (ls : List (List Op))
    (R : List Fmt.DeclaredRound)
    (h : H2U.layOpens own true (laterRounds work tree W old []) ls = some R) :
    ∃ x, ls = [x] ∧ x ≠ [] ∧
      R = [⟨rLambda.entry, [], []⟩, ⟨(rBase work old tree).entry, [], x⟩] := by
  have e : laterRounds work tree W old [] = [rLambda, rBase work old tree] := by
    simp [laterRounds]
  rw [e, lay_quiet own rLambda _ _ rfl] at h
  obtain ⟨R1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨x, t, R', rfl, hx, h4, rfl⟩ := lay_opens own _ _ _ _ (by simp [rBase]) h1
  cases t with
  | nil =>
    rw [H2U.layOpens.eq_def] at h4
    cases h4
    exact ⟨x, rfl, hx, rfl⟩
  | cons y t =>
    rw [H2U.layOpens.eq_def] at h4
    cases h4

/-- The trees that the test sends, as they are told: number i is the chain's own number free + i. -/
def told (N : H2U.TestNums) : List Op :=
  N.sent.zipIdx.map fun t => N.own t.1.1 t.1.2 (N.free + t.2)

theorem told_at (N : H2U.TestNums) (n : Nat) :
    (told N)[n]? = (N.sent[n]?).map fun t => N.own t.1 t.2 (N.free + n) := by
  unfold told
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases N.sent[n]? <;> simp

theorem told_drop (N : H2U.TestNums) (n : Nat) (x : List Op) (t : List (List Op))
    (h : ((told N).drop n).map ([·]) = x :: t) :
    ∃ a W, N.sent[n]? = some (a, W) ∧ x = [N.own a W (N.free + n)] ∧
      t = ((told N).drop (n + 1)).map ([·]) := by
  cases hd : (told N).drop n with
  | nil => rw [hd] at h; cases h
  | cons y ys =>
    rw [hd] at h
    have h0 : (told N)[n]? = some y := by
      have := congrArg (·[0]?) hd
      simpa [List.getElem?_drop] using this
    have h1 : (told N).drop (n + 1) = ys := by
      have := congrArg (List.drop 1) hd
      simpa [List.drop_drop, Nat.add_comm] using this
    rw [told_at] at h0
    cases hs : N.sent[n]? with
    | none => rw [hs] at h0; cases h0
    | some aw =>
      rw [hs] at h0
      obtain ⟨a, W⟩ := aw
      obtain rfl := Option.some.inj h0
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact ⟨a, W, rfl, rfl, by rw [h1]⟩

/-- The declared rounds, at the top. -/
theorem rounds_top (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some rds) :
    ∃ s next rest R, N.stages = s :: next :: rest ∧
      H2U.layOpens N.ownMask false (laterRounds N.work 0 0 s (next :: rest))
        ((N.first ++ (if N.ownMask then (told N).take 1 else [])) ::
          (if N.ownMask then (told N).drop 1 else told N).map ([·])) = some R ∧
      rds = ⟨{ Fmt.M1.rBat.entry with rows := N.rows }, [], []⟩ :: R := by
  unfold H2U.roundsOfNums at h
  split at h
  · rename_i s next rest hs
    dsimp only at h
    rw [H2U.layOpens.eq_def] at h
    simp only [Fmt.M1.rBat, List.isEmpty_nil, if_true] at h
    have hn : ("BAT" == "FOLD epsilon") = false := by decide
    simp only [hn, Bool.and_false, Bool.or_false, Bool.false_eq_true, if_false] at h
    obtain ⟨R, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨s, next, rest, R, hs, h1, rfl⟩
  · cases h

theorem epsE_name (own seen : Bool) : (epsE own seen).name = "FOLD epsilon" := by
  unfold epsE
  split <;> rfl

/-- The first "FOLD epsilon" sends a root where the first fold sends its own mask; no other does. -/
theorem epsE_roots (own seen : Bool) : (epsE own seen).roots = if own && !seen then 1 else 0 := by
  unfold epsE
  split <;> rfl

/-- The declared rounds, down to the first switch. -/
theorem rounds_head (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some rds) :
    ∃ s next rest R', N.stages = s :: next :: rest ∧
      H2U.layOpens N.ownMask true (laterRounds N.work (0 + 1) (wMid next) next rest)
        ((if N.ownMask then (told N).drop 1 else told N).map ([·])) = some R' ∧
      rds = ⟨{ Fmt.M1.rBat.entry with rows := N.rows }, [], []⟩ ::
        ((⟨epsE N.ownMask false, [], []⟩ ::
          List.replicate s.k (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
        (⟨(rSeed next).entry, [], []⟩ :: ⟨(rCs N.work s 0 0).entry, [],
          N.first ++ (if N.ownMask then (told N).take 1 else [])⟩ :: R')) := by
  obtain ⟨s, next, rest, R, hs, hR, rfl⟩ := rounds_top N rds h
  obtain ⟨x, t, R', hx, _, h', rfl⟩ := lay_stage _ _ _ _ _ _ _ _ _ R hR
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  exact ⟨s, next, rest, R', hs, h', rfl⟩

end H2K.Made
