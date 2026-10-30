-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Laws.lean: small facts on the reading of parameter bytes and on descriptions.

A proof that ties a chain's description to the library's theorems needs to know what a description
that `Given.describe` returns consists of, and that it meets the strict reader's conditions. The
facts here say so. They are proved by unfolding the definitions.

Main statements: `Given.read_bytes`, `Given.read_plan_ok`, `Given.describe_eq`,
`Given.describe_ok`, `Given.describe_rounds`, `round_kind`.
What is not claimed: anything on how parameter bytes are made, or on what their numbers are worth.
-/
import OnBytes.Params.Given

namespace OnBytes.Params

/-- What was read holds the bytes from which it was read. -/
theorem Given.read_bytes {b : ByteArray} {g : Given} (h : Given.read b = some g) : g.bytes = b := by
  unfold Given.read at h
  cases hp : paramsReadT b with
  | none => simp [hp] at h
  | some p =>
    simp only [hp, Option.bind_some] at h
    split at h
    · cases h; rfl
    · cases h

/-- The plan that was read is in order, and all its names are names of the format. -/
theorem Given.read_plan_ok {b : ByteArray} {g : Given} (h : Given.read b = some g) :
    g.plan.ok = true ∧ namesKnown g.plan = true := by
  unfold Given.read at h
  cases hp : paramsReadT b with
  | none => simp [hp] at h
  | some p =>
    simp only [hp, Option.bind_some] at h
    split at h
    · rename_i hok
      cases h
      simpa using hok
    · cases h

/-- A description that is returned consists of the given bytes, plan and digest and of the
arguments, and nothing else. -/
theorem Given.describe_eq {g : Given} {label : Nat} {statement : ByteArray} {rand : Fmt.Rand}
    {rounds : List Fmt.Round} {stored : List (List Fmt.Stored)} {firstTree : Nat} {S : Fmt.SpecX}
    (h : g.describe label statement rand rounds stored firstTree = some S) :
    S = { base := { label := label, plan := g.plan, params := g.bytes, statement := statement,
                    rand := rand, firstTree := firstTree, cfg := g.cfg, rounds := rounds },
          stored := stored } := by
  unfold Given.describe at h
  simp only at h
  split at h
  · cases h; rfl
  · cases h

/-- A description that is returned meets the strict reader's conditions. -/
theorem Given.describe_ok {g : Given} {label : Nat} {statement : ByteArray} {rand : Fmt.Rand}
    {rounds : List Fmt.Round} {stored : List (List Fmt.Stored)} {firstTree : Nat} {S : Fmt.SpecX}
    (h : g.describe label statement rand rounds stored firstTree = some S) : S.ok = true := by
  unfold Given.describe at h
  simp only at h
  split at h
  · rename_i hok
    cases h
    rw [← specXOk_eq]
    exact hok
  · cases h

/-- The rounds and the stored openings of a description that is returned are those that were stated,
and its parameter bytes are the given bytes. -/
theorem Given.describe_rounds {g : Given} {label : Nat} {statement : ByteArray} {rand : Fmt.Rand}
    {rounds : List Fmt.Round} {stored : List (List Fmt.Stored)} {firstTree : Nat} {S : Fmt.SpecX}
    (h : g.describe label statement rand rounds stored firstTree = some S) :
    S.base.rounds = rounds ∧ S.stored = stored ∧ S.base.params = g.bytes := by
  rw [Given.describe_eq h]
  exact ⟨rfl, rfl, rfl⟩

/-- A round that `round` makes has its entry, and the kind of its entry's name. -/
theorem round_kind {e : Fmt.Entry} {items : List Fmt.Item} {opens : List (Fmt.Shape × Fmt.Src)}
    {r : Fmt.Round} (h : round e items opens = some r) :
    r.entry = e ∧ kindOf e.name = some r.kind := by
  unfold round at h
  cases hk : kindOf e.name with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.map_some] at h
    cases h
    exact ⟨rfl, rfl⟩

end OnBytes.Params
