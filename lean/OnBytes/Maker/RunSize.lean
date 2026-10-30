-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/RunSize.lean: the run's value of a chain that the verifier program's reader has read
has 32 bytes; so has the start that OnBytes/Maker/Tables.lean lays before a leaf's typed salt.

Statements and proofs. A chain's head is made by `Fmt.startChainW` (OnBytes/Maker/ReadTrace.lean);
the library says that a run's value that it makes has 32 bytes, at a hash whose answers have the
format's lengths (`Run.startChainW_run`).

Main names:
  `readChain_run32`: one chain.
  `runOfTree_32`: `runOfTree W r j = some run → run.size = 32`, at three chains as read.
No letter stands under "there is".
Limits: nothing is said of what a run's value is. Nothing on soundness.


-/
import OnBytes.Maker.ReadTrace
import OnBytes.Maker.Tables
import OnBytes.Tie.StoredDom

set_option autoImplicit false

namespace OnBytes.Maker

/-- **The run's value of a chain as read has 32 bytes.** -/
theorem readChain_run32 (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j)) :
    ∀ x, o.run = some x → x.size = 32 := by
  obtain ⟨x, i0, -, h2, -⟩ := readChain_trace S seen b i o j e
  exact _root_.Run.startChainW_run Fmt.formatHash (fun n t i s b => Fmt.size_H n t i s b) _ _ _ _
    ⟨o.run, o.rho0⟩ h2

/-- **The start that the tables lay has 32 bytes.** -/
theorem runOfTree_32 (W : Three.Whole) (S₁ S₂ S₃ : Fmt.SpecX) (r : Proof.TailRead) (b : ByteArray)
    (n₁ n₂ n₃ : Fmt.Seen) (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ)
    (e₁ : readChain S₁ n₁ b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ n₃ b i₃ = some (r.second.out, j₃)) :
    ∀ (j : ℕ) (run : ByteArray), runOfTree W r j = some run → run.size = 32 := by
  intro j run h
  unfold runOfTree at h
  cases ht : W.table[j]? with
  | none => rw [ht] at h; cases h
  | some t =>
    rw [ht] at h
    have h' : (chainOf r t.chain).run = some run := h
    rcases hc : t.chain with _ | _ | c
    · rw [hc] at h'
      exact readChain_run32 S₁ n₁ b i₁ _ j₁ e₁ run h'
    · rw [hc] at h'
      exact readChain_run32 S₂ n₂ b i₂ _ j₂ e₂ run h'
    · rw [hc] at h'
      exact readChain_run32 S₃ n₃ b i₃ _ j₃ e₃ run h'

end OnBytes.Maker
