-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/CompilerComplete.lean: THE COMPILER THEOREM ON COMPLETENESS, proved, in its two forms.

1.  WHAT IS CLAIMED: Spec.compiled_complete and Spec.compiled_complete_atEveryCoin hold: for any protocol, layout of hash queries, three provers and
    settings, completeness as interactive oracle proofs, with the lengths and the public conditions, gives the library's completeness
    of compileOverTypedOracles at the error completenessError. Completeness as interactive oracle proofs is a premise: this file proves
    neither completeness nor zero knowledge of the protocol.
2.  OVER COINS AND CHALLENGES TOGETHER: complete_of_parts (Johnson/CompletenessAndZeroKnowledge/CompleteJointOfParts.lean), at the compiler's own honest side.
3.  AT EVERY COIN: partsGiveCompilerPremise gives AccLaws at rejectingFalls: outside the failures the verifier accepts, and the failures
    are the measure that the premise bounds. complete_argW (Johnson/WholeKey/Complete.lean) concludes; StopsIn is stopsIn_ofRecs.
-/
import VerifiableInference.Final.CompilerTheorems
import Johnson.CompletenessAndZeroKnowledge.CompleteJointOfParts

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {L : HolographicProtocol I X} {offlineRoundMarks : RoundSplits L.offline.shape} {linkRoundMarks : RoundSplits L.link.shape}

/-- **COMPLETENESS OF THE COMPILED SCHEME, PROVED, from the form at every coin.** -/
theorem compiled_complete_atEveryCoin_holds : Spec.compiled_complete_atEveryCoin := by
  intro I X L offlineRoundMarks linkRoundMarks w provers s Served E t2 everyCoin hF pub
  exact complete_argW w.queryLayout w.seedQueries w.answerCode w.fixedSample w.compilerParameters
    (honestSide w provers s).side Served
    (badsOf (toRecs provers) (rejectingFalls provers w.work) fun _ _ => ∅)
    pub.searches pub.layout hF
    (partsGiveCompilerPremise provers w.queryLayout w.seedQueries Served E.offline E.link E.online t2
      everyCoin)
    (stopsIn_ofRecs (toRecs provers) _ _ fun _ _ => ∅)

/-- **COMPLETENESS OF THE COMPILED SCHEME, PROVED, from completeness over the provers' coins and the challenges together.** The three
enumerations of coins that complete_of_parts asks are free at honestSide. -/
theorem compiled_complete_holds : Spec.compiled_complete := by
  intro I X L offlineRoundMarks linkRoundMarks w provers s Served E t2 hF pub
  exact complete_of_parts w.queryLayout w.seedQueries w.answerCode w.fixedSample w.compilerParameters
    (honestSide w provers s).side provers (honestSide w provers s).dc rfl t2
    pub.searches pub.layout hF (AtPublicFiles.Bridge.pickAll_ok provers.offlineProver.Coin)
    (AtPublicFiles.Bridge.pickAll_ok provers.linkProver.Coin) (AtPublicFiles.Bridge.pickAll_ok provers.onlineProver.Coin)

/-! ## A test that can fail: the premise on the provers has teeth -/

/-- A transcript is itself but for nonces. -/
theorem puts_refl {lam K : ℕ} : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s), Puts s A W τ τ
  | [], _, _, _ => trivial
  | _ :: s, (_, A), (_, W), (_, _, τ) => ⟨rfl, rfl, Or.inl rfl, puts_refl s A W τ⟩

/-- **A verifier that accepts nothing cannot meet the premise below error 1**, at a served index: the premise
says something of the verifier, whatever the provers. The same holds of the link and the online proof. -/
theorem one_le_offline_of_no_acceptance {w : HashLayout L offlineRoundMarks linkRoundMarks} {provers : HonestProvers L}
    {Served : I → X → Prop} {E : CompletenessErrors}
    (t2 : CompleteBeforeHashingAt w provers Served E)
    (noAcceptance : ∀ x y τ, L.offline.accept x y τ = false) {i : I} {x : X} {r : L.EncodingRandomness} {e : L.OutOfDomainSeed}
    (hS : Served i x) : 1 ≤ E.offline := by
  refine le_trans (le_of_eq (pr_univ _).symm) (le_trans (pr_mono _ fun d _ => ?_)
    (t2.offlineAccepted i x r e hS))
  exact Or.inr ⟨_, puts_refl _ _ _ _, noAcceptance _ _ _⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.compiled_complete_atEveryCoin_holds
#print axioms VerifiableInference.Compilation.compiled_complete_holds
#print axioms VerifiableInference.Compilation.puts_refl
#print axioms VerifiableInference.Compilation.one_le_offline_of_no_acceptance
