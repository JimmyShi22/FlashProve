-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/EntriesPlan.lean: where a chain's description is returned, the entries of the rounds
from which it was made are the rounds of the plan in the chain's parameter bytes, each entry has its
kind's draws, and the configuration's digest has 32 bytes; so the entries of the plain data's rounds
(`Three.Whole.of`) are the three plans' rounds.

Statements and proofs. `Params.describeWith` returns a description only if it meets the strict
reader's conditions (`Params.Given.describe_ok`, OnBytes/Params/Laws.lean). Among the fourteen
clauses of `Fmt.Spec.ok` (Fmt/Rules8.lean; one by one in Fmt/Rules8Ok.lean) are: the rounds' entries
are `plan.rounds`; each entry fits its round's kind; the digest has 32 bytes. The plain data's
rounds have the entries, kinds and items of the lists of which they are made
(OnBytes/Maker/ReadData.lean).

Main names:
  `described_entries`: `R.map (·.1.entry) = g.plan.rounds`.
  `described_fits`: each round's entry fits its kind, at the plan's number of samples.
  `described_cfg32`: `g.cfg.size = 32`.
  `ds₁_entries`, `ds₂_entries`, `ds₃_entries`: the data's rounds' entries are the plans' rounds.
No letter stands under "there is".
Limits: the premise is that a description IS returned at these rounds: it holds at a file that the
program's reader has read (OnBytes/Maker/ThreeRead.lean holds the three equations), and is not shown
of a dry run by itself. The third chain's data are made of rounds at made-up names: `ds₃_entries`
asks that their entries are those of the rounds under which the chain was read. Nothing is said of
which items a round has at a place of the plan, nor of a round's kind beyond `Fmt.Entry.fits`.
Nothing on soundness.


-/
import OnBytes.Maker.ReadData
import Fmt.Rules8Ok

set_option autoImplicit false

namespace OnBytes.Maker

section
variable {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand} {R : Params.Rounds}
  {ft : ℕ} {S : Fmt.SpecX} (h : Params.describeWith g label st rand R ft = some S)
include h

/-- The base of a description that is returned meets the strict reader's conditions. -/
theorem described_ok : S.base.ok = true := by
  have hk : S.ok = true := Params.Given.describe_ok h
  unfold Fmt.SpecX.ok at hk
  rw [Bool.and_eq_true, Bool.and_eq_true] at hk
  exact hk.1.1

/-- **The rounds' entries are the plan's rounds.** -/
theorem described_entries : R.map (·.1.entry) = g.plan.rounds := by
  have e := eq_of_beq (Fmt.ok_entries (described_ok h))
  unfold Params.describeWith at h
  rw [Params.Given.describe_eq h] at e
  have e' : (R.map (·.1)).map (·.entry) = g.plan.rounds := e
  rw [List.map_map] at e'
  exact e'

/-- Each round's entry has its kind's draws and no others. -/
theorem described_fits : ∀ x ∈ R, x.1.entry.fits x.1.kind g.plan.samples = true := by
  have e := Fmt.ok_fits (described_ok h)
  unfold Params.describeWith at h
  rw [Params.Given.describe_eq h] at e
  have e' : ((R.map (·.1)).all fun r => r.entry.fits r.kind g.plan.samples) = true := e
  intro x hx
  exact List.all_eq_true.1 e' x.1 (List.mem_map_of_mem hx)

/-- The configuration's digest has 32 bytes. -/
theorem described_cfg32 : g.cfg.size = 32 := by
  have e := eq_of_beq (Fmt.ok_cfg (described_ok h))
  unfold Params.describeWith at h
  rw [Params.Given.describe_eq h] at e
  exact e

end

section
variable {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand} {ft : ℕ}
  {S : Fmt.SpecX} (R₁ R₂ R₃ : Params.Rounds)

/-- **The entries of the first chain's data are its plan's rounds.** -/
theorem ds₁_entries (h : Params.describeWith g label st rand R₁ ft = some S) :
    (Three.Whole.of R₁ R₂ R₃).ds₁.map (·.entry) = g.plan.rounds :=
  (entries_ds₁ R₁ R₂ R₃).trans (described_entries h)

/-- The second chain's. -/
theorem ds₂_entries (h : Params.describeWith g label st rand R₂ ft = some S) :
    (Three.Whole.of R₁ R₂ R₃).ds₂.map (·.entry) = g.plan.rounds :=
  (entries_ds₂ R₁ R₂ R₃).trans (described_entries h)

/-- The third chain's. R₃': the rounds under which the chain was read. -/
theorem ds₃_entries {R₃' : Params.Rounds}
    (h : Params.describeWith g label st rand R₃' ft = some S)
    (he : R₃'.map (·.1.entry) = R₃.map (·.1.entry)) :
    (Three.Whole.of R₁ R₂ R₃).ds₃.map (·.entry) = g.plan.rounds :=
  (entries_ds₃ R₁ R₂ R₃).trans (he.symm.trans (described_entries h))

end

end OnBytes.Maker
