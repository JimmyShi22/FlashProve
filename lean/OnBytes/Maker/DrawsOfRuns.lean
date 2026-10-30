-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/DrawsOfRuns.lean: what OnBytes/Maker/AcceptAtA.lean asks of the verifier's messages
(`DrawsHeldA`), at the messages that three chains' runs have yielded, laid in a row, from what each
run's own messages give.

The verifier of a file runs its three chains one after the other, and lays what they have yielded in
a row (`glue`, OnBytes/TypedOracleCompiler/Joined/Verifier.lean). A chain's value begins with the verifier's message
of its first round, a silent round, and goes on with those of its stretch.

Main theorems.
  `rho₁_glue`, `rho₂_glue`, `rho₃_glue`: the three stretches' parts of the messages in a row are the
    three values' own, each without its first.
  `drawsHeldA_of_runs`: `DrawsHeldA` at the messages in a row, from six hypotheses on the three
    values: each stretch's draws are those read, but for the digests, and its proofs of work pass.

What is not claimed. None of the six hypotheses. Nothing on soundness.


-/
import OnBytes.Maker.AcceptAtA

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open OnBytes.TwoLaws (LAlike DrawnAlike)

section
variable {lam : ℕ} {G : Chains} (a : Out lam G.c₁) (b : Out lam G.c₂) (e : Out lam G.c₃)

/-- The first stretch's part of the messages in a row. -/
theorem rho₁_glue : G.rho₁ (glue a b e).1 = a.1.2 := by
  obtain ⟨⟨cF, ρ₁⟩, _⟩ := a
  exact Rho.fst_app _ _

/-- From the joining round on. -/
theorem rhoJ_glue : G.rhoJ (glue a b e).1 = Rho.app (s := G.c₂) (t := G.c₃) b.1 e.1 := by
  obtain ⟨⟨cF, ρ₁⟩, _⟩ := a
  exact Rho.snd_app _ _

/-- The second stretch's part. -/
theorem rho₂_glue : G.rho₂ (glue a b e).1 = b.1.2 := by
  unfold Chains.rho₂
  rw [rhoJ_glue]
  obtain ⟨⟨cJ, ρ₂⟩, _⟩ := b
  exact Rho.fst_app _ _

/-- The third stretch's part. -/
theorem rho₃_glue : G.rho₃ (glue a b e).1 = e.1.2 := by
  unfold Chains.rho₃
  rw [rhoJ_glue]
  obtain ⟨⟨cJ, ρ₂⟩, _⟩ := b
  exact congrArg Prod.snd (Rho.snd_app (s := G.s₂) (t := G.c₃) ρ₂ e.1)

end

/-- **What is asked of the verifier's messages, at what three runs have yielded.** -/
theorem drawsHeldA_of_runs (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
    (r : Proof.TailRead) (a : Out 256 (chainsOf C D tF tJ t3).c₁)
    (b : Out 256 (chainsOf C D tF tJ t3).c₂) (e : Out 256 (chainsOf C D tF tJ t3).c₃)
    (d₁ : LAlike DrawnAlike (r.first.out.rounds.toList.dropLast.map (·.drawn))
      (drawnT C D.ds₁ a.1.2))
    (d₂ : LAlike DrawnAlike (r.shared.out.rounds.toList.map (·.drawn)) (drawnT C D.ds₂ b.1.2))
    (d₃ : LAlike DrawnAlike (r.second.out.rounds.toList.map (·.drawn)) (drawnT C D.ds₃ e.1.2))
    (w₁ : passT C D.ds₁ a.1.2 = true) (w₂ : passT C D.ds₂ b.1.2 = true)
    (w₃ : passT C D.ds₃ e.1.2 = true) : DrawsHeldA C D tF tJ t3 r (glue a b e).1 where
  d₁ := by rw [rho₁_glue]; exact d₁
  d₂ := by rw [rho₂_glue]; exact d₂
  d₃ := by rw [rho₃_glue]; exact d₃
  w₁ := by rw [rho₁_glue]; exact w₁
  w₂ := by rw [rho₂_glue]; exact w₂
  w₃ := by rw [rho₃_glue]; exact w₃

end OnBytes.Maker
