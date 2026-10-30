-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/AtEveryRequestGuards.lean: beside the statements of
VerifiableInference/AtEveryRequest.lean: how each stands to its form on a domain, and what a served
request is for the integer model. Each `def … : Prop` here is a proposition, as a definition; only
what stands as a `theorem` is proved.
-/
import VerifiableInference.RequestOutcome
import VerifiableInference.Labelled
import VerifiableInference.LabelledZeroKnowledge
import VerifiableInference.MoreStatements
import VerifiableInference.Bridge
import IntegerModel.Arrays.RequestResultLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.AtEveryRequest

open scoped ENNReal

/-! ## 1. Completeness and its form on a domain -/

/-- **`ProofAcceptedWhere` is `CompleteOn`**, where a request meets the hypothesis and has its
claimed output as its result exactly if it lies in the domain and its output tokens are the
model's. -/
theorem proofAcceptedWhere_iff_completeOn (system : ArgumentSystem) (hypothesis : Request → Prop)
    (result : system.Weights → Request → Option (List Token))
    (domain : system.Weights → List Token → List Token → Prop)
    (agree : ∀ weights prompt output,
      (hypothesis (prompt, output) ∧ result weights (prompt, output) = some output) ↔
        (domain weights prompt output ∧ system.IsModelOutput weights prompt output))
    (error : ℝ≥0∞) :
    ProofAcceptedWhere system hypothesis result error ↔ CompleteOn system domain error := by
  constructor
  · intro accepted weights prompt output inDomain isOutput
    have both := (agree weights prompt output).2 ⟨inDomain, isOutput⟩
    exact accepted weights (prompt, output) both.1 both.2
  · intro complete weights request holds isResult
    have both := (agree weights request.1 request.2).1 ⟨holds, isResult⟩
    exact complete weights request.1 request.2 both.1 both.2

/-! ## 2. Zero knowledge -/

/-- The requests whose outcome is served, in the form that `CompleteOn` and `ZeroKnowledgeOn`
take. -/
def servedRequests {Weights : Type} (outcome : Weights → Request → Outcome) :
    Weights → List Token → List Token → Prop :=
  fun weights prompt output => outcome weights (prompt, output) = .served

/-- The output tokens of a served request are the model's. -/
def ServedIsModelOutput (system : ArgumentSystem)
    (outcome : system.Weights → Request → Outcome) : Prop :=
  ∀ (weights : system.Weights) (request : Request), outcome weights request = .served →
    system.IsModelOutput weights request.1 request.2

/-- At the requests that `unserved` names the system's prover hands out no proof: all that it can
return meets `isNoProof`. -/
def HandsOutNoProof (system : ArgumentSystem) (unserved : system.Weights → Request → Prop)
    (isNoProof : system.Proof → Prop) : Prop :=
  ∀ (weights : system.Weights) (randomness : system.CommitmentRandomness) (request : Request)
    (hash : Hash) (form : system.Proof),
    unserved weights request →
      (system.prove weights randomness request.1 request.2).run hash form ≠ 0 → isNoProof form

/-- Zero knowledge on the served requests gives zero knowledge at every request, told the outcome,
at the same error, where the prover's answer at a refused request is one fixed value: the simulator,
told the outcome, makes it. -/
def ZeroKnowledgeFollowsFromOn (system : ArgumentSystem)
    (outcome : system.Weights → Request → Outcome) (noProof : system.Proof) : Prop :=
  ServedIsModelOutput system outcome →
  HandsOutNoProof system (fun weights request => outcome weights request = .refused)
    (· = noProof) →
  ∀ error : ℕ → ℕ → ℝ≥0∞,
    ZeroKnowledgeOn system (servedRequests outcome) error →
      ZeroKnowledgeWhere system (fun _ => True) outcome error

/-- The converse: zero knowledge at every request, told the outcome, asks no less than zero
knowledge on the served requests. -/
def ZeroKnowledgeGivesOn (system : ArgumentSystem)
    (outcome : system.Weights → Request → Outcome) : Prop :=
  ∀ error : ℕ → ℕ → ℝ≥0∞, ZeroKnowledgeWhere system (fun _ => True) outcome error →
    ZeroKnowledgeOn system (servedRequests outcome) error

/-- A system whose proof tells two weights apart, at one request, where what the simulator is told
and the public parameters agree, meets zero knowledge at no bar below one half, at one proof and no
query. So the line can fail for a leak. -/
def LeakIsCaught {Told : Type} (system : ArgumentSystem)
    (told : system.Weights → Request → Told) : Prop :=
  ∀ (first second : system.Weights) (request : Request) (reads : system.Proof → Bool),
    system.publicParameters first = system.publicParameters second →
    (∀ other, told first other = told second other) →
    (∀ randomness hash form,
      (system.prove first randomness request.1 request.2).run hash form ≠ 0 →
        reads form = true) →
    (∀ randomness hash form,
      (system.prove second randomness request.1 request.2).run hash form ≠ 0 →
        reads form = false) →
    ∀ bar : ℝ≥0∞, bar < 2⁻¹ →
      ¬ ZeroKnowledgeBelowWhere system (fun _ => True) told 0 1 bar

/-- Example: all the strength of `ZeroKnowledgeShownWhere` lies in which function is told. A system
that is zero knowledge told nothing meets it with the weights themselves told, and so shown beside
each proof. So a line that uses it must name a closed term of a small type. -/
theorem toldWeightsSaysNothing (system : ArgumentSystem) (hypothesis : Request → Prop)
    (error : ℕ → ℕ → ℝ≥0∞)
    (zeroKnowledge : ZeroKnowledgeWhere system hypothesis (fun _ _ => ()) error) :
    ZeroKnowledgeShownWhere system hypothesis (fun weights _ => weights) error :=
  zeroKnowledgeShown_of_told system (fun weights _ => weights) (fun _ _ => ()) (fun _ => ())
    (fun _ _ => rfl) hypothesis error zeroKnowledge

/-- `ZeroKnowledgeShownBelowWhere` at a hypothesis gives it at a narrower one. -/
theorem ZeroKnowledgeShownBelowWhere.narrow {Told : Type} {system : ArgumentSystem}
    {wide narrow : Request → Prop} {told : system.Weights → Request → Told}
    {queries proofs : ℕ} {bar : ℝ≥0∞} (inside : ∀ request, narrow request → wide request)
    (below : ZeroKnowledgeShownBelowWhere system wide told queries proofs bar) :
    ZeroKnowledgeShownBelowWhere system narrow told queries proofs bar :=
  ZeroKnowledgeBelowWhere.narrow inside below

/-! ## 3. The integer model -/

/-- At valid settings a request is served exactly if `CanServe` holds of it and its output tokens
are the model's. -/
theorem served_iff_canServe {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (weights : ModelWeights settings)
    (request : Request) :
    requestOutcome settings weights request = .served ↔
      (CanServe settings weights request.1 request.2 ∧
        ∀ position (inOutput : position < request.2.length),
          modelNextToken settings weights (request.1 ++ request.2.take position) =
            some request.2[position]) :=
  (requestOutcome_eq_served_iff settings weights request).trans
    (canServe_and_modelOutput_iff valid weights request.1 request.2).symm

/-- At these settings some request is served at some weights. -/
def SomeRequestIsServed (settings : IntegerTransformer.Settings) : Prop :=
  ∃ (weights : ModelWeights settings) (request : Request),
    requestOutcome settings weights request = .served

end VerifiableInference.AtEveryRequest

#print axioms VerifiableInference.AtEveryRequest.proofAcceptedWhere_iff_completeOn
#print axioms VerifiableInference.AtEveryRequest.served_iff_canServe
#print axioms VerifiableInference.AtEveryRequest.toldWeightsSaysNothing
