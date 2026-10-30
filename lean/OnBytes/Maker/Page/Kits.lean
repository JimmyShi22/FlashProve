-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Kits.lean: the kit of verifier messages as hash blocks fits the fields of the
three descriptions under which the program has read a key file or a proof file.

OnBytes/Maker/Page/Runs.lean and Accept.lean ask `KitFits` at the fields
of the three descriptions. A description holds the plan of its chain's parameter bytes. The three
chains of one file hold one setting, if `Params.KeyChains.read` or `Params.ProofChains.read` has
returned them (OnBytes/TieK/ChainsRead.lean), and the program's checks refuse a first chain whose
field is not the field in which the program computes.

Main theorems.
  `describeWith_plan`: the plan of a description that is returned is that of the parameter bytes.
  `fields_of_read`: the three descriptions' fields, from `ThreeRead`.
  `kits_of_read`: `KitFits` three times, at `ckP f` and `chalP f K`, if the three chains' parameter
    bytes hold the field f.
  `kits_key`, `kits_proof`: at the field `.two`, from the test on the first chain's field and
    `SameSetting` twice.
No letter stands under "there is" in these statements.
No other file calls `kits_of_read`, `kits_key` or `kits_proof`: where the library needs `KitFits` it
goes by `fields_of_read` and `kit_at`.

What is not claimed. That the chains were read by `Params.KeyChains.read` or
`Params.ProofChains.read`. Nothing on soundness.


-/
import OnBytes.Maker.Page.RunsTools
import OnBytes.TieK.ChainsRead

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ
open OnBytes.Params (Rounds)
open OnBytes.Proof (TailPublic FirstEnd SharedEnd TailRead)
open OnBytes.TieK (SameSetting)

/-- The plan of a description that is returned is that of the parameter bytes. -/
theorem describeWith_plan {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (h : Params.describeWith g label st rand R ft = some S) : S.base.plan = g.plan := by
  unfold Params.describeWith at h
  rw [Params.Given.describe_eq h]

variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- The three descriptions' fields. -/
theorem fields_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) :
    S₁.base.plan.field = g₁.plan.field ∧ S₂.base.plan.field = p.shared.given.plan.field ∧
      S₃.base.plan.field = p.second.given.plan.field :=
  ⟨congrArg (·.field) (describeWith_plan hS₁),
    congrArg (·.field) (describeWith_plan (g := p.shared.given) T.shared_spec),
    congrArg (·.field) (describeWith_plan (g := p.second.given) T.second_spec)⟩

/-- **The kit fits the three descriptions' fields**, if the three chains' parameter bytes hold the
field f. -/
theorem kits_of_read (f : Fmt.Fld) (K : ℕ)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (h₁ : g₁.plan.field = f)
    (h₂ : p.shared.given.plan.field = f) (h₃ : p.second.given.plan.field = f) :
    TypedOracleCompiler.Run.PQ.KitFits S₁.base.plan.field (ckP f) K (chalP f K) ∧
      TypedOracleCompiler.Run.PQ.KitFits S₂.base.plan.field (ckP f) K (chalP f K) ∧
      TypedOracleCompiler.Run.PQ.KitFits S₃.base.plan.field (ckP f) K (chalP f K) := by
  obtain ⟨e₁, e₂, e₃⟩ := fields_of_read T hS₁
  exact ⟨kit_at f K S₁ (e₁.trans h₁), kit_at f K S₂ (e₂.trans h₂), kit_at f K S₃ (e₃.trans h₃)⟩

/-- **A key file.** -/
theorem kits_key (K : ℕ) (k : Params.KeyChains) (table : Params.TableName)
    (T : ThreeRead (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file i
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : k.oneTime.describe table R₁ = some S₁)
    (hf : (k.oneTime.given.plan.field != .two) = false)
    (s₂ : SameSetting k.oneTime.given k.shared.given)
    (s₃ : SameSetting k.oneTime.given k.second.given) :
    TypedOracleCompiler.Run.PQ.KitFits S₁.base.plan.field (ckP .two) K (chalP .two K) ∧
      TypedOracleCompiler.Run.PQ.KitFits S₂.base.plan.field (ckP .two) K (chalP .two K) ∧
      TypedOracleCompiler.Run.PQ.KitFits S₃.base.plan.field (ckP .two) K (chalP .two K) := by
  have h₁ : k.oneTime.given.plan.field = .two := by
    simpa using hf
  exact kits_of_read .two K T hS₁ h₁ (s₂.field.symm.trans h₁) (s₃.field.symm.trans h₁)

/-- **A proof file.** -/
theorem kits_proof (K : ℕ) (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd)
    (T : ThreeRead (Proof.tailPublic c table) block (Proof.firstStart c.first) file i R₁ dry S₁ r
      seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : c.first.describe table copy request words R₁ = some S₁)
    (hf : (c.first.given.plan.field != .two || c.first.given.cfg == Fmt.zero32) = false)
    (s₂ : SameSetting c.first.given c.shared.given)
    (s₃ : SameSetting c.first.given c.second.given) :
    TypedOracleCompiler.Run.PQ.KitFits S₁.base.plan.field (ckP .two) K (chalP .two K) ∧
      TypedOracleCompiler.Run.PQ.KitFits S₂.base.plan.field (ckP .two) K (chalP .two K) ∧
      TypedOracleCompiler.Run.PQ.KitFits S₃.base.plan.field (ckP .two) K (chalP .two K) := by
  have h₁ : c.first.given.plan.field = .two := by
    rw [Bool.or_eq_false_iff] at hf
    simpa using hf.1
  exact kits_of_read .two K T hS₁ h₁ (s₂.field.symm.trans h₁) (s₃.field.symm.trans h₁)

end OnBytes.Maker.Page
