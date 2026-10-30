-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ReadData.lean: the rounds of the plain data of a file's three chains (`Three.Whole`,
OnBytes/Three/Data.lean) have the entries, kinds and items of the rounds from which they were made;
and a chain that was read under a description with random bytes has a run's value.

Statements and proofs. OnBytes/Maker/ReadSpecs.lean has the like for the stored tables.

Main names:
  `rdsFromL_map`: a field of the data's rounds that is read off the round alone.
  `entries_ds₁`, `kinds_ds₁`, `items_ds₁` and the like at the second and the third chain.
  `length_ds₁` and the like: the data have as many rounds.
  `describeWith_rand`: the random bytes of a description that is returned are the argument's.
  `described_run`: a chain that the program's reader has read under a description made with random
    bytes, in the file or given, has a run's value.
Limits: the data's third list of rounds is made at made-up names of the trees that the third chain
takes over; these laws speak of the list from which the data were made, whichever it is. Nothing on
the trees that a round opens. Nothing on soundness.


-/
import OnBytes.Maker.ReadSpecs
import OnBytes.Maker.ReadTrace

set_option autoImplicit false

namespace OnBytes.Maker

/-- A field of the data's rounds that is read off the round alone. -/
theorem zipWith_map {β : Type} (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)
    (p : Three.RDL → β) (q : Fmt.Round × List Fmt.Stored → β)
    (hpq : ∀ r n, p (Three.rdOf all t₁ t₂ here base first r n) = q r) :
    ∀ (R : Params.Rounds) (L : List ℕ), L.length = R.length →
    (List.zipWith (Three.rdOf all t₁ t₂ here base first) R L).map p = R.map q
  | [], _, _ => by simp
  | _ :: _, [], e => by cases e
  | r :: R, n :: L, e => by
    rw [List.zipWith_cons_cons, List.map_cons, List.map_cons, hpq,
      zipWith_map all t₁ t₂ here base first p q hpq R L (Nat.succ.inj e)]

theorem rdsFromL_map {β : Type} (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)
    (p : Three.RDL → β) (q : Fmt.Round × List Fmt.Stored → β)
    (hpq : ∀ r n, p (Three.rdOf all t₁ t₂ here base first r n) = q r) (R : Params.Rounds) :
    (Three.rdsFromL all t₁ t₂ here base first R).map p = R.map q :=
  zipWith_map all t₁ t₂ here base first p q hpq R _ (sentBefore_length R)

section
variable (R₁ R₂ R₃ : Params.Rounds)

theorem entries_ds₁ : (Three.Whole.of R₁ R₂ R₃).ds₁.map (·.entry) = R₁.map (·.1.entry) :=
  rdsFromL_map _ _ _ _ _ _ _ _ (fun _ _ => rfl) R₁
theorem entries_ds₂ : (Three.Whole.of R₁ R₂ R₃).ds₂.map (·.entry) = R₂.map (·.1.entry) :=
  rdsFromL_map _ _ _ _ _ _ _ _ (fun _ _ => rfl) R₂
theorem entries_ds₃ : (Three.Whole.of R₁ R₂ R₃).ds₃.map (·.entry) = R₃.map (·.1.entry) :=
  rdsFromL_map _ _ _ _ _ _ _ _ (fun _ _ => rfl) R₃

theorem kinds_ds₁ : (Three.Whole.of R₁ R₂ R₃).ds₁.map (·.kind) = R₁.map (·.1.kind) :=
  rdsFromL_map _ _ _ _ _ _ _ _ (fun _ _ => rfl) R₁
theorem kinds_ds₂ : (Three.Whole.of R₁ R₂ R₃).ds₂.map (·.kind) = R₂.map (·.1.kind) :=
  rdsFromL_map _ _ _ _ _ _ _ _ (fun _ _ => rfl) R₂
theorem kinds_ds₃ : (Three.Whole.of R₁ R₂ R₃).ds₃.map (·.kind) = R₃.map (·.1.kind) :=
  rdsFromL_map _ _ _ _ _ _ _ _ (fun _ _ => rfl) R₃

theorem items_ds₁ : (Three.Whole.of R₁ R₂ R₃).ds₁.map (·.items) = R₁.map (·.1.items) :=
  rdsFromL_map _ _ _ _ _ _ _ _ (fun _ _ => rfl) R₁
theorem items_ds₂ : (Three.Whole.of R₁ R₂ R₃).ds₂.map (·.items) = R₂.map (·.1.items) :=
  rdsFromL_map _ _ _ _ _ _ _ _ (fun _ _ => rfl) R₂
theorem items_ds₃ : (Three.Whole.of R₁ R₂ R₃).ds₃.map (·.items) = R₃.map (·.1.items) :=
  rdsFromL_map _ _ _ _ _ _ _ _ (fun _ _ => rfl) R₃

theorem length_ds₁ : (Three.Whole.of R₁ R₂ R₃).ds₁.length = R₁.length := by
  have h := congrArg List.length (items_ds₁ R₁ R₂ R₃)
  rwa [List.length_map, List.length_map] at h
theorem length_ds₂ : (Three.Whole.of R₁ R₂ R₃).ds₂.length = R₂.length := by
  have h := congrArg List.length (items_ds₂ R₁ R₂ R₃)
  rwa [List.length_map, List.length_map] at h
theorem length_ds₃ : (Three.Whole.of R₁ R₂ R₃).ds₃.length = R₃.length := by
  have h := congrArg List.length (items_ds₃ R₁ R₂ R₃)
  rwa [List.length_map, List.length_map] at h

end

/-- The random bytes of a description that is returned are the argument's. -/
theorem describeWith_rand {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Params.Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (h : Params.describeWith g label st rand R ft = some S) : S.base.rand = rand := by
  unfold Params.describeWith at h
  rw [Params.Given.describe_eq h]

/-- **A chain that the program's reader has read under a description made with random bytes, in the
file or given, has a run's value.** -/
theorem described_run {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Params.Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (hS : Params.describeWith g label st rand R ft = some S) (hr : rand ≠ .none) (seen : Fmt.Seen)
    (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j)) :
    ∃ run, o.run = some run :=
  readChain_run S seen b i o j e (by rw [describeWith_rand hS]; exact hr)

end OnBytes.Maker
