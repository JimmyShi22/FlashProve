-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/ZeroKnowledgeOn.lean: lemmas on `ZeroKnowledgeOn`
(VerifiableInference/MoreStatements.lean), the form of `ZeroKnowledge` for requests in a stated set.
`ZeroKnowledgeOn.mono`: a smaller domain asks less.
`zeroKnowledgeOn_of_privacy`: it follows from the library's `HasStrongIndexPrivacyWith`
(ZKCP/Defs.lean) for the relation "the request meets the domain and the output is the model's".
`domain` may depend on the weights. Then whether a request meets it is not hidden: the chooser
(`chooser`: `realSteps`, VerifiableInference/Statements.lean), which knows the weights, is the same
in both experiments. Outside `domain` nothing is said about what the honest prover's output shows.
-/
import VerifiableInference.MoreStatements
import VerifiableInference.AgreementZeroKnowledge

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-- A smaller domain asks less. -/
theorem ZeroKnowledgeOn.mono {system : ArgumentSystem} {domain domain' : system.Weights → List Token
    → List Token → Prop} {ζ : ℕ → ℕ → ℝ≥0∞}
    (h : ZeroKnowledgeOn system domain ζ) (hd : ∀ weights prompt output, domain' weights prompt
        output → domain weights prompt output) : ZeroKnowledgeOn system domain' ζ := by
  obtain ⟨simulator, hs⟩ := h
  exact ⟨simulator, fun weights chooser hChooser => hs weights chooser fun view prompt output hc =>
      ⟨hd _ _ _ (hChooser view prompt output hc).1, (hChooser view prompt output hc).2⟩⟩

variable (system : ArgumentSystem)

/-- The relation "the request meets the domain and the output tokens are the model's", in the form
of ZKCP/Defs.lean. -/
def ArgumentSystem.uploadRelationOn (domain : system.Weights → List Token → List Token → Prop) :
    ZKCP.IndexedRelation system.Weights (List Token × List Token) Unit system.PublicParameters where
  rel weights x _ := domain weights x.1 x.2 ∧ system.IsModelOutput weights x.1 x.2
  pp := system.publicParameters

/-- The two quantities of the statement, in the library's terms. -/
theorem zeroKnowledge_quantities (simulator : Simulator system.PublicParameters system.Proof)
    (verifier : Commitment → MaliciousVerifier system.Proof)
    (chooser : View system.Proof → Option (List Token × List Token)) (weights : system.Weights)
        (proofCount : ℕ) :
    statisticalDistance (Prob (realExperiment system verifier chooser weights proofCount))
        (eventProbability (simulatedExperiment system simulator verifier chooser weights
            proofCount))
      = ZKCP.SD
          (fun T => ZKCP.Pr (ZKCP.realExp system.uploadArgument
              (fun commitment => (verifier commitment).toUpload)
            (chooserToUpload chooser) weights proofCount) (fun _ => T))
          (fun T => ZKCP.prob (ZKCP.idealExp system.uploadRelation simulator.toUpload
              (fun commitment => (verifier commitment).toUpload)
            (chooserToUpload chooser) weights proofCount) T)
    ∧ eventProbability (simulatedExperiment system simulator verifier chooser weights proofCount)
        {view | ¬ view.queryLog.Consistent}
      = ZKCP.prob (ZKCP.idealExp system.uploadRelation simulator.toUpload
          (fun commitment => (verifier commitment).toUpload)
            (chooserToUpload chooser) weights proofCount)
                {view | ¬ ZKCP.Trace.Consistent view.trace} := by
  constructor
  · rw [← statisticalDistance_views]
    congr 1
    · funext event
      exact Prob_realExperiment system verifier chooser weights proofCount event
    · funext event
      rw [simulatedExperiment_eq]
      exact prob_bind_pure_map _ _ _
  · rw [simulatedExperiment_eq]
    exact prob_bind_pure_map _ _ _

/-- Strong index privacy for the relation with the domain gives zero-knowledge on the domain. -/
theorem zeroKnowledgeOn_of_privacy (domain : system.Weights → List Token → List Token → Prop)
    (ζ : ℕ → ℕ → ℝ≥0∞)
    (S : ZKCP.Simulator 256 system.PublicParameters Commitment (List Token × List Token)
        system.Proof)
    (h : ZKCP.HasStrongIndexPrivacyWith (system.uploadRelationOn domain) system.uploadArgument S ζ)
        : ZeroKnowledgeOn system domain ζ := by
  refine ⟨Simulator.ofUpload S, fun weights chooser hChooser queries verifier proofCount hV => ?_⟩
  have hValid : ZKCP.ViewEnv.IsValid (system.uploadRelationOn domain) (chooserToUpload chooser)
      weights := by
    intro view x w hChoice
    have hChoice' : (chooser (View.ofUpload view)).map (fun request => (request, ())) = some (x, w)
        := hChoice
    cases hValue : chooser (View.ofUpload view) with
    | none => rw [hValue] at hChoice'; cases hChoice'
    | some request =>
        rw [hValue] at hChoice'
        have hx : request = x := congrArg Prod.fst (Option.some.inj hChoice')
        rw [hx] at hValue
        exact hChooser (View.ofUpload view) x.1 x.2 hValue
  have h' := h weights (chooserToUpload chooser) hValid queries
      (fun commitment => (verifier commitment).toUpload) proofCount
    (fun commitment => (MaliciousVerifier.queryBound_toUpload _ queries).mpr (hV commitment))
  have k := zeroKnowledge_quantities system (Simulator.ofUpload S) verifier chooser weights
      proofCount
  rw [k.1, k.2]
  exact h'

end VerifiableInference

#print axioms VerifiableInference.zeroKnowledgeOn_of_privacy
#print axioms VerifiableInference.ZeroKnowledgeOn.mono
#print axioms VerifiableInference.zeroKnowledge_quantities
