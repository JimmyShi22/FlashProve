-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByTop.lean: `runBy_of`: `Spec.stagesBy_eq` (RunBySpec.lean) and
the three statements `Spec.own_col`, `Spec.ties_of` and `Spec.first_tab` of RunBySpecTop.lean imply
`Spec.runBy_eq`: `runBy` gives the rounds, trees and opened columns of `testAll`. The four are
hypotheses here; RunByEq.lean supplies their proofs. `top_shape`: both definitions put the same
first round and first tree before the stages' output.

By what. `runBy` and `testAll` are unfolded, and `top_shape` joins the pieces.

Limits. Where the stages pass `StagesOk`, at `Seams.lib` and the input `RunIn.ofTest`. The warnings
(`RunOut.no`) are left out. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunBySpecTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Johnson.Prover.Link (BOut)

/-- If the stages' outputs are equal, so are the whole outputs. -/
theorem top_shape (d : Fmt.Drawn) (c : Bool) (f f' : ℕ → List UInt64) (hf : f = f') (b : RunOut)
    (a : BOut) (h : b.toB = a) :
    (⟨⟨[], d⟩ :: b.rs, (fun _ => []) :: (if c then b.tr.set 0 f else b.tr), b.gs⟩ : BOut) =
      ⟨⟨[], d⟩ :: a.rs, (fun _ => []) :: (if c then a.tr.set 0 f' else a.tr), a.gs⟩ := by
  subst h hf
  rfl

theorem runBy_of (hS : Spec.stagesBy_eq) (hO : Spec.own_col) (hT : Spec.ties_of)
    (hF : Spec.first_tab) : Spec.runBy_eq := by
  intro W X J w fr C D ok
  rcases h : J.p.nums.stages with _ | ⟨s, _ | ⟨n, rest⟩⟩
  · rw [h] at ok
    exact absurd ok (by simp [StagesOk])
  · rw [h] at ok
    exact absurd ok (by simp [StagesOk])
  · rw [h] at ok
    have ok' : okFrom s (n :: rest) = true := ok
    have T := hF W X J w fr C s (n :: rest) h (by simp) ok'
    obtain ⟨ties, hide⟩ := hT s (n :: rest) C ok'
    have E := hS J.p (sortedOf (s :: n :: rest) C) (coinsOf (s :: n :: rest) C.hide C.rest)
      (n :: rest) 0 s (J.laid.drop 1) 1 (J.recB w fr (D 0)) (J.first w fr C) _
      (J.trees₀ w fr C.mem (J.first w fr C)) D ok' ties hide T
    have O := hO s (J.first w fr C) _ T
    have R := top_shape (D 0) J.fresh.isNone _ _ O _ _ E
    unfold runBy testAll
    simp only [RunIn.ofTest, TestJob.s₀, h, List.headD_cons, keep_fst, RunOut.toB]
    exact R

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.top_shape
#print axioms ProofFile.Honest.K12.Light.runBy_of
