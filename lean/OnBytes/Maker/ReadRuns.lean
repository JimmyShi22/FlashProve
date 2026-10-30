-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ReadRuns.lean: each of the three chains of a key file or a proof file that the
program's reader has read under the program's own descriptions has a run's value.

Statements and proofs. The program's four makers of a description (OnBytes/Params/Chains.lean) give
a chain random bytes: a key's one-time chain, a proof's first chain and a second chain have them in
the file; a shared chain takes the binding tree's root in their place.

Main names:
  `oneTime_rand`, `first_rand`, `shared_rand`, `second_rand`: the descriptions have random bytes.
  `runsThere_of`: `RunsThere r` (OnBytes/Maker/TablesReturn.lean) at three chains that were read
    under descriptions with random bytes.
  `runsThere_key`, `runsThere_proof`: at the descriptions of a key file and of a proof file.
Limits: the three equations of the reading are premises. Nothing is said of what a run's value is.
The labels of the shared and the second chain are letters here, any numbers, also in `runsThere_key`
and `runsThere_proof`, which no file calls. Nothing on soundness.


-/
import OnBytes.Maker.ReadData
import OnBytes.Maker.TablesReturn

set_option autoImplicit false

namespace OnBytes.Maker

theorem oneTime_rand {p : Params.OneTime} {table : Params.TableName} {R : Params.Rounds}
    {S : Fmt.SpecX} (h : p.describe table R = some S) : S.base.rand ≠ .none := by
  rw [describeWith_rand h]
  exact fun e => by cases e

theorem first_rand {p : Params.First} {table : Params.TableName} {copy : ℕ} {request words :
    ByteArray}
    {R : Params.Rounds} {S : Fmt.SpecX} (h : p.describe table copy request words R = some S) :
    S.base.rand ≠ .none := by
  rw [describeWith_rand h]
  exact fun e => by cases e

theorem shared_rand {p : Params.Shared} {label : ℕ} {table : Params.TableName} {root : ByteArray}
    {R : Params.Rounds} {S : Fmt.SpecX} (h : p.describe label table root R = some S) :
    S.base.rand ≠ .none := by
  rw [describeWith_rand h]
  exact fun e => by cases e

theorem second_rand {p : Params.Second} {label : ℕ} {own shared : ByteArray} {R : Params.Rounds}
    {ft : ℕ} {S : Fmt.SpecX} (h : p.describe label own shared R ft = some S) :
    S.base.rand ≠ .none := by
  rw [describeWith_rand h]
  exact fun e => by cases e

/-- **Three chains that were read under descriptions with random bytes have a run's value each.** -/
theorem runsThere_of (S₁ S₂ S₃ : Fmt.SpecX) (r : Proof.TailRead) (b : ByteArray)
    (n₁ n₂ n₃ : Fmt.Seen) (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ)
    (e₁ : readChain S₁ n₁ b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ n₃ b i₃ = some (r.second.out, j₃)) (h₁ : S₁.base.rand ≠ .none)
    (h₂ : S₂.base.rand ≠ .none) (h₃ : S₃.base.rand ≠ .none) : RunsThere r :=
  ⟨readChain_run S₁ n₁ b i₁ _ j₁ e₁ h₁, readChain_run S₂ n₂ b i₂ _ j₂ e₂ h₂,
    readChain_run S₃ n₃ b i₃ _ j₃ e₃ h₃⟩

/-- At the descriptions of a key file. -/
theorem runsThere_key {p₁ : Params.OneTime} {p₂ : Params.Shared} {p₃ : Params.Second}
    {l₂ l₃ : ℕ} {t₁ t₂ : Params.TableName} {root own shared : ByteArray}
    {R₁ R₂ R₃ : Params.Rounds} {ft : ℕ}
    {S₁ S₂ S₃ : Fmt.SpecX} (d₁ : p₁.describe t₁ R₁ = some S₁)
    (d₂ : p₂.describe l₂ t₂ root R₂ = some S₂) (d₃ : p₃.describe l₃ own shared R₃ ft = some S₃)
    (r : Proof.TailRead) (b : ByteArray) (n₁ n₂ n₃ : Fmt.Seen) (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ)
    (e₁ : readChain S₁ n₁ b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ n₃ b i₃ = some (r.second.out, j₃)) : RunsThere r :=
  runsThere_of S₁ S₂ S₃ r b n₁ n₂ n₃ i₁ i₂ i₃ j₁ j₂ j₃ e₁ e₂ e₃ (oneTime_rand d₁) (shared_rand d₂)
    (second_rand d₃)

/-- At the descriptions of a proof file. -/
theorem runsThere_proof {p₁ : Params.First} {p₂ : Params.Shared} {p₃ : Params.Second}
    {l₂ l₃ : ℕ} {t₁ t₂ : Params.TableName} {copy : ℕ} {request words root own shared : ByteArray}
    {R₁ R₂ R₃ : Params.Rounds} {ft : ℕ} {S₁ S₂ S₃ : Fmt.SpecX}
    (d₁ : p₁.describe t₁ copy request words R₁ = some S₁)
    (d₂ : p₂.describe l₂ t₂ root R₂ = some S₂) (d₃ : p₃.describe l₃ own shared R₃ ft = some S₃)
    (r : Proof.TailRead) (b : ByteArray) (n₁ n₂ n₃ : Fmt.Seen) (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ)
    (e₁ : readChain S₁ n₁ b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ n₃ b i₃ = some (r.second.out, j₃)) : RunsThere r :=
  runsThere_of S₁ S₂ S₃ r b n₁ n₂ n₃ i₁ i₂ i₃ j₁ j₂ j₃ e₁ e₂ e₃ (first_rand d₁) (shared_rand d₂)
    (second_rand d₃)

end OnBytes.Maker
