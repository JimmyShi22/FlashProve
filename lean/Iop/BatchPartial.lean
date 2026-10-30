-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchPartial.lean: what the compiler (Compile/Batch/Joint.lean) takes from `JointLaw`, the last
clause of `BatchInteractiveOracleProof.SndB` (Snd-B) and of its late form `SndBL`: the condition on challenges at a
prefix of a transcript. (Words of this library: lean/GLOSSARY.md.)
Iop/Batch.lean states that condition as a recursion on the rounds (`JointLaw`). Here it is read off
at a prefix of one slot's transcript (a Fiat-Shamir query of one slot; also valid in a shared
round): `JointLaw.at_slot`.
Limits: this file does not read it off at a prefix of a transcript of the whole batch before a
shared challenge (a shared query); that is the clause of `JointLaw` for a shared round, the joint
error.
-/
import Iop.Batch

namespace Iop
open Prob

variable {N : ℕ}

/-- The error at a query of one slot (the clause of `JointLaw` for a local round; in a shared round
it follows from the joint error): under `JointLaw`, at every prefix of the transcript of a non-empty
slot in state 0, at most as many values of the challenge as the round's error count turn the state
to 1. -/
theorem JointLaw.at_slot :
    ∀ {s : Shape} {A : RoundSplits s} {ε : Err s} {St : Fin N → Option (PTr s → Bool)},
      JointLaw N s A ε St →
      ∀ (j : Fin N) (S : PTr s → Bool), St j = some S →
        ∀ τ : AtV s,
          S (.atV τ) = false → cnt (fun c : τ.round.Chal => S (τ.snoc c) = true) ≤ τ.err ε
  | r :: s, (a, _), (e, _), St, h, j, S, hS, .inl m, h0 => by
      have hj : a.join (a.split m).1 (a.split m).2 = m := a.split.symm_apply_apply m
      have h1 := (h (a.split m).1 (fun _ => (a.split m).2)).1
      cases hk : a.kind with
      | lo =>
        simp only [hk] at h1
        have h2 := h1 j S hS
        rw [hj] at h2
        exact h2 h0
      | sh =>
        simp only [hk] at h1
        refine le_trans (cnt_mono ?_) h1
        intro c hc
        exact ⟨j, S, hS, by rw [hj]; exact h0, by rw [hj]; exact hc⟩
  | r :: s, (a, _), (_, _), St, h, j, S, hS, .inr (m, c, τ), h0 => by
      have hj : a.join (a.split m).1 (a.split m).2 = m := a.split.symm_apply_apply m
      obtain ⟨v, hv⟩ : ∃ v : a.kind.All N r.Chal, a.kind.slot v j = c := by
        cases a.kind with
        | sh => exact ⟨c, rfl⟩
        | lo => exact ⟨fun _ => c, rfl⟩
      have h1 := JointLaw.at_slot ((h (a.split m).1 (fun _ => (a.split m).2)).2 v) j
        (fun t => S (PTr.cons (a.join (a.split m).1 (a.split m).2) (a.kind.slot v j) t))
        (by rw [hS]; rfl) τ
      rw [hj, hv] at h1
      exact h1 h0

end Iop
