-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/LabelledZeroKnowledgeTools.lean

General tools for carrying zero knowledge (VerifiableInference/Statements.lean)
from an argument system to the same system with something laid beside each proof. No argument system is
named: everything stands at letters. It imports VerifiableInference/Statements.lean alone.

1  Distance and probability under a map: "statisticalDistance_preimage_le", "eventProbability_map",
   "Prob_mapResult", "statisticalDistance_images_le".
2  Trees: "RandomizedAlgorithm.mapResult" with its laws against "bind" and "run".
3  Views and verifiers: "View.mapProofs" lays f request proof in the place of each proof;
   "MaliciousVerifier.comapProofs" is the verifier that does so itself before it goes on.
4  The real steps at a prover as a letter ("stepsWith"), which "realSteps" is ("realSteps_eq_stepsWith"),
   and the first induction, "stepsWith_mapProofs".
5  The simulated steps at two functions as letters ("simulatedStepsWith"), which "simulatedSteps" is
   ("simulatedSteps_eq_simulatedStepsWith"), and the second induction, "simulatedStepsWith_mapProofs".

Limits. Equations of definitions and one inequality. Nothing on any protocol, prover or simulator.
-/
import VerifiableInference.Statements

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference

/- A request: a prompt and output tokens. A notation of this file alone: the name lies in
VerifiableInference/AtEveryRequest.lean. -/
local notation "Request" => (List Token × List Token)

variable {α β γ : Type}

/-! ## 1 Distance and probability under a map -/

/-- **The distance does not grow under a map**: the events of the image are among the events. -/
theorem statisticalDistance_preimage_le (f : α → β) (first second : Set α → ℝ≥0∞) :
    statisticalDistance (fun event => first (f ⁻¹' event)) (fun event => second (f ⁻¹' event))
      ≤ statisticalDistance first second :=
  iSup_le fun event =>
    le_iSup (fun e : Set α => max (first e - second e) (second e - first e)) (f ⁻¹' event)

/-- The probability of an event under the image of a distribution. -/
theorem eventProbability_map (distribution : PMF α) (f : α → β) (event : Set β) :
    eventProbability (distribution.map f) event = eventProbability distribution (f ⁻¹' event) :=
  PMF.toOuterMeasure_map_apply f distribution event

/-! ## 2 Trees -/

namespace RandomizedAlgorithm

/-- The same algorithm, with f laid on its result. -/
def mapResult (f : α → β) (algorithm : RandomizedAlgorithm α) : RandomizedAlgorithm β :=
  algorithm.bind fun result => .done (f result)

theorem bind_assoc : ∀ (first : RandomizedAlgorithm α) (second : α → RandomizedAlgorithm β)
    (third : β → RandomizedAlgorithm γ),
    (first.bind second).bind third = first.bind fun result => (second result).bind third
  | .done _, _, _ => rfl
  | .query input next, second, third =>
      congrArg (RandomizedAlgorithm.query input)
        (funext fun answer => bind_assoc (next answer) second third)
  | .sample bound next, second, third =>
      congrArg (RandomizedAlgorithm.sample bound)
        (funext fun draw => bind_assoc (next draw) second third)

theorem mapResult_done (f : α → β) (result : α) :
    (RandomizedAlgorithm.done result).mapResult f = .done (f result) := rfl

theorem mapResult_query (f : α → β) (input : BitString) (next : Digest → RandomizedAlgorithm α) :
    (RandomizedAlgorithm.query input next).mapResult f
      = .query input fun answer => (next answer).mapResult f := rfl

theorem mapResult_sample (f : α → β) (bound : ℕ) (next : Fin (bound + 1) → RandomizedAlgorithm α) :
    (RandomizedAlgorithm.sample bound next).mapResult f
      = .sample bound fun draw => (next draw).mapResult f := rfl

/-- A step behind a map reads the mapped result. -/
theorem bind_mapResult (f : α → β) (first : RandomizedAlgorithm α)
    (rest : β → RandomizedAlgorithm γ) :
    (first.mapResult f).bind rest = first.bind fun result => rest (f result) :=
  bind_assoc first _ rest

/-- A map behind two steps is a map behind the second. -/
theorem mapResult_bind (f : β → γ) (first : RandomizedAlgorithm α)
    (rest : α → RandomizedAlgorithm β) :
    (first.bind rest).mapResult f = first.bind fun result => (rest result).mapResult f :=
  bind_assoc first rest _

/-- Under each hash function the distribution of the mapped result is the image. -/
theorem run_mapResult (hash : Hash) (f : α → β) :
    ∀ algorithm : RandomizedAlgorithm α, (algorithm.mapResult f).run hash = (algorithm.run hash).map f
  | .done result => (PMF.pure_map f result).symm
  | .query input next => run_mapResult hash f (next (hash input))
  | .sample bound next => by
      show (PMF.uniformOfFintype (Fin (bound + 1))).bind
          (fun draw => ((next draw).mapResult f).run hash)
        = ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw => (next draw).run hash).map f
      rw [PMF.map_bind]
      exact congrArg _ (funext fun draw => run_mapResult hash f (next draw))

end RandomizedAlgorithm

/-- The probability of an event at the mapped result. -/
theorem Prob_mapResult (experiment : RandomizedAlgorithm α) (f : α → β) (event : Set β) :
    Prob (experiment.mapResult f) event = Prob experiment (f ⁻¹' event) := by
  unfold Prob
  refine MeasureTheory.lintegral_congr fun hash => ?_
  rw [RandomizedAlgorithm.run_mapResult, eventProbability_map]

/-- **The distance between an experiment and a distribution does not grow when one map is laid on both.** -/
theorem statisticalDistance_images_le (experiment : RandomizedAlgorithm α) (distribution : PMF α)
    (f : α → β) :
    statisticalDistance (Prob (experiment.mapResult f)) (eventProbability (distribution.map f))
      ≤ statisticalDistance (Prob experiment) (eventProbability distribution) := by
  have real : Prob (experiment.mapResult f) = fun event => Prob experiment (f ⁻¹' event) :=
    funext (Prob_mapResult experiment f)
  have simulated : eventProbability (distribution.map f)
      = fun event => eventProbability distribution (f ⁻¹' event) :=
    funext (eventProbability_map distribution f)
  rw [real, simulated]
  exact statisticalDistance_preimage_le f _ _

/-! ## 3 Views and verifiers -/

variable {P P' : Type}

/-- The view with f request proof in the place of each proof. The commitment, the query log and the
random draws stay. -/
def View.mapProofs (f : Request → P → P') (view : View P) : View P' :=
  ⟨view.commitment, view.proofs.map fun entry => (entry.1, f entry.1 entry.2), view.queryLog,
    view.randomDraws⟩

theorem View.mapProofs_queryLog (f : Request → P → P') (view : View P) :
    (view.mapProofs f).queryLog = view.queryLog := rfl

/-- One more proof, before or behind the map. -/
theorem View.mapProofs_snoc (f : Request → P → P') (view : View P) (request : Request) (proof : P) :
    ({ view.mapProofs f with
        proofs := (view.mapProofs f).proofs ++ [(request, f request proof)] } : View P')
      = View.mapProofs f { view with proofs := view.proofs ++ [(request, proof)] } := by
  simp only [View.mapProofs, List.map_append, List.map_cons, List.map_nil]

/-- The verifier on plain proofs that lays f on each proof itself and goes on as the given one. -/
def MaliciousVerifier.comapProofs (f : Request → P → P') : MaliciousVerifier P' → MaliciousVerifier P
  | .stop => .stop
  | .query input next => .query input fun answer => (next answer).comapProofs f
  | .sample bound next => .sample bound fun draw => (next draw).comapProofs f
  | .requestProof next => .requestProof fun request proof => (next request (f request proof)).comapProofs f

/-- It makes no more queries. -/
theorem MaliciousVerifier.queryBound_comapProofs (f : Request → P → P') :
    ∀ (verifier : MaliciousVerifier P') (queries : ℕ), verifier.QueryBound queries →
      (verifier.comapProofs f).QueryBound queries
  | .stop, _, _ => trivial
  | .query _ _, 0, h => h
  | .query _ next, queries + 1, h => fun answer =>
      queryBound_comapProofs f (next answer) queries (h answer)
  | .sample _ next, queries, h => fun draw => queryBound_comapProofs f (next draw) queries (h draw)
  | .requestProof next, queries, h => fun request proof =>
      queryBound_comapProofs f (next request (f request proof)) queries (h request (f request proof))

/-! ## 4 The real steps -/

/-- "realSteps" with the prover as a letter. -/
def stepsWith (prove : Request → RandomizedAlgorithm P) (chooser : View P → Option Request) :
    MaliciousVerifier P → ℕ → View P → RandomizedAlgorithm (View P)
  | .stop, _, view => pure view
  | .query input next, remaining, view =>
      .query input fun answer =>
        stepsWith prove chooser (next answer) remaining
          { view with queryLog := view.queryLog ++ [(input, answer)] }
  | .sample bound next, remaining, view =>
      .sample bound fun draw =>
        stepsWith prove chooser (next draw) remaining
          { view with randomDraws := view.randomDraws ++ [draw.val] }
  | .requestProof _, 0, view => pure view
  | .requestProof next, remaining + 1, view =>
      match chooser view with
      | none => pure view
      | some request =>
        (prove request).bind fun proof =>
          stepsWith prove chooser (next request proof) remaining
            { view with proofs := view.proofs ++ [(request, proof)] }

/-- "realSteps" is "stepsWith" at the system's prover. -/
theorem realSteps_eq_stepsWith (system : ArgumentSystem) (chooser : View system.Proof → Option Request)
    (weights : system.Weights) (randomness : system.CommitmentRandomness) :
    ∀ (verifier : MaliciousVerifier system.Proof) (remaining : ℕ) (view : View system.Proof),
      realSteps system chooser weights randomness verifier remaining view
        = stepsWith (fun request => system.prove weights randomness request.1 request.2) chooser
            verifier remaining view
  | .stop, _, _ => rfl
  | .query input next, remaining, view => by
      have ih := fun answer => realSteps_eq_stepsWith system chooser weights randomness (next answer)
        remaining { view with queryLog := view.queryLog ++ [(input, answer)] }
      simp only [realSteps, stepsWith]
      exact congrArg _ (funext fun answer => ih answer)
  | .sample bound next, remaining, view => by
      have ih := fun draw => realSteps_eq_stepsWith system chooser weights randomness (next draw)
        remaining { view with randomDraws := view.randomDraws ++ [draw.val] }
      simp only [realSteps, stepsWith]
      exact congrArg _ (funext fun draw => ih draw)
  | .requestProof _, 0, _ => rfl
  | .requestProof next, remaining + 1, view => by
      have ih := fun request proof => realSteps_eq_stepsWith system chooser weights randomness
        (next request proof) remaining { view with proofs := view.proofs ++ [(request, proof)] }
      cases hChoice : chooser view with
      | none => simp only [realSteps, stepsWith, hChoice]
      | some request =>
          simp only [realSteps, stepsWith, hChoice]
          exact congrArg _ (funext fun proof => ih request proof)

/-- **THE FIRST INDUCTION.** At the prover that lays f on each proof, from a mapped view: the steps are
the image of the plain prover's steps, at the chooser and the verifier that lay f themselves. An equation
of trees: no hash function is named. -/
theorem stepsWith_mapProofs (f : Request → P → P') (prove : Request → RandomizedAlgorithm P)
    (chooser : View P' → Option Request) :
    ∀ (verifier : MaliciousVerifier P') (remaining : ℕ) (view : View P),
      stepsWith (fun request => (prove request).mapResult (f request)) chooser verifier remaining
          (view.mapProofs f)
        = (stepsWith prove (fun plain => chooser (plain.mapProofs f)) (verifier.comapProofs f)
            remaining view).mapResult (View.mapProofs f)
  | .stop, _, _ => rfl
  | .query input next, remaining, view => by
      have ih := fun answer => stepsWith_mapProofs f prove chooser (next answer) remaining
        { view with queryLog := view.queryLog ++ [(input, answer)] }
      simp only [stepsWith, MaliciousVerifier.comapProofs, RandomizedAlgorithm.mapResult_query]
      exact congrArg _ (funext fun answer => ih answer)
  | .sample bound next, remaining, view => by
      have ih := fun draw => stepsWith_mapProofs f prove chooser (next draw) remaining
        { view with randomDraws := view.randomDraws ++ [draw.val] }
      simp only [stepsWith, MaliciousVerifier.comapProofs, RandomizedAlgorithm.mapResult_sample]
      exact congrArg _ (funext fun draw => ih draw)
  | .requestProof _, 0, _ => rfl
  | .requestProof next, remaining + 1, view => by
      have ih := fun request proof => stepsWith_mapProofs f prove chooser
        (next request (f request proof)) remaining
        { view with proofs := view.proofs ++ [(request, proof)] }
      cases hChoice : chooser (view.mapProofs f) with
      | none =>
          simp only [stepsWith, MaliciousVerifier.comapProofs, hChoice]
          rfl
      | some request =>
          simp only [stepsWith, MaliciousVerifier.comapProofs, hChoice]
          rw [RandomizedAlgorithm.bind_mapResult, RandomizedAlgorithm.mapResult_bind]
          refine congrArg _ (funext fun proof => ?_)
          exact (congrArg
            (stepsWith (fun request => (prove request).mapResult (f request)) chooser
              (next request (f request proof)) remaining)
            (View.mapProofs_snoc f view request proof)).trans (ih request proof)

/-! ## 5 The simulated steps -/

variable {State : Type}

/-- "simulatedSteps" with the simulator's two functions as letters. -/
def simulatedStepsWith (answerQuery : State → BitString → PMF (Digest × State))
    (simulateProof : State → Request → PMF (P × State)) (chooser : View P → Option Request) :
    MaliciousVerifier P → ℕ → View P → State → PMF (View P)
  | .stop, _, view, _ => PMF.pure view
  | .query input next, remaining, view, state =>
      (answerQuery state input).bind fun answered =>
        simulatedStepsWith answerQuery simulateProof chooser (next answered.1) remaining
          { view with queryLog := view.queryLog ++ [(input, answered.1)] } answered.2
  | .sample bound next, remaining, view, state =>
      (PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw =>
        simulatedStepsWith answerQuery simulateProof chooser (next draw) remaining
          { view with randomDraws := view.randomDraws ++ [draw.val] } state
  | .requestProof _, 0, view, _ => PMF.pure view
  | .requestProof next, remaining + 1, view, state =>
      match chooser view with
      | none => PMF.pure view
      | some request =>
        (simulateProof state request).bind fun simulated =>
          simulatedStepsWith answerQuery simulateProof chooser (next request simulated.1) remaining
            { view with proofs := view.proofs ++ [(request, simulated.1)] } simulated.2

/-- "simulatedSteps" is "simulatedStepsWith" at the simulator's own two functions. -/
theorem simulatedSteps_eq_simulatedStepsWith {PublicParameters : Type}
    (simulator : Simulator PublicParameters P) (chooser : View P → Option Request) :
    ∀ (verifier : MaliciousVerifier P) (remaining : ℕ) (view : View P) (state : simulator.State),
      simulatedSteps simulator chooser verifier remaining view state
        = simulatedStepsWith simulator.answerQuery simulator.simulateProof chooser verifier remaining
            view state
  | .stop, _, _, _ => by
      simp only [simulatedSteps, simulatedStepsWith]
  | .query input next, remaining, view, state => by
      have ih := fun (answered : Digest × simulator.State) =>
        simulatedSteps_eq_simulatedStepsWith simulator chooser (next answered.1) remaining
          { view with queryLog := view.queryLog ++ [(input, answered.1)] } answered.2
      simp only [simulatedSteps, simulatedStepsWith]
      exact congrArg _ (funext fun answered => ih answered)
  | .sample bound next, remaining, view, state => by
      have ih := fun draw =>
        simulatedSteps_eq_simulatedStepsWith simulator chooser (next draw) remaining
          { view with randomDraws := view.randomDraws ++ [draw.val] } state
      simp only [simulatedSteps, simulatedStepsWith]
      exact congrArg _ (funext fun draw => ih draw)
  | .requestProof _, 0, _, _ => by
      simp only [simulatedSteps, simulatedStepsWith]
  | .requestProof next, remaining + 1, view, state => by
      have ih := fun request (simulated : P × simulator.State) =>
        simulatedSteps_eq_simulatedStepsWith simulator chooser (next request simulated.1)
          remaining { view with proofs := view.proofs ++ [(request, simulated.1)] } simulated.2
      cases hChoice : chooser view with
      | none => simp only [simulatedSteps, simulatedStepsWith, hChoice]
      | some request =>
          simp only [simulatedSteps, simulatedStepsWith, hChoice]
          exact congrArg _ (funext fun simulated => ih request simulated)

/-- **THE SECOND INDUCTION.** At the simulator that lays f on each proof that it makes, from a mapped
view: the steps' distribution is the image of the plain simulator's, at the chooser and the verifier that
lay f themselves. The state and the answers to queries are the same. -/
theorem simulatedStepsWith_mapProofs (f : Request → P → P')
    (answerQuery : State → BitString → PMF (Digest × State))
    (simulateProof : State → Request → PMF (P × State)) (chooser : View P' → Option Request) :
    ∀ (verifier : MaliciousVerifier P') (remaining : ℕ) (view : View P) (state : State),
      simulatedStepsWith answerQuery
          (fun state request =>
            (simulateProof state request).map fun simulated => (f request simulated.1, simulated.2))
          chooser verifier remaining (view.mapProofs f) state
        = (simulatedStepsWith answerQuery simulateProof (fun plain => chooser (plain.mapProofs f))
            (verifier.comapProofs f) remaining view state).map (View.mapProofs f)
  | .stop, _, view, _ => by
      simp only [simulatedStepsWith, MaliciousVerifier.comapProofs]
      exact (PMF.pure_map _ _).symm
  | .query input next, remaining, view, state => by
      have ih := fun (answered : Digest × State) =>
        simulatedStepsWith_mapProofs f answerQuery simulateProof chooser (next answered.1) remaining
          { view with queryLog := view.queryLog ++ [(input, answered.1)] } answered.2
      simp only [simulatedStepsWith, MaliciousVerifier.comapProofs]
      rw [PMF.map_bind]
      exact congrArg _ (funext fun answered => ih answered)
  | .sample bound next, remaining, view, state => by
      have ih := fun draw =>
        simulatedStepsWith_mapProofs f answerQuery simulateProof chooser (next draw) remaining
          { view with randomDraws := view.randomDraws ++ [draw.val] } state
      simp only [simulatedStepsWith, MaliciousVerifier.comapProofs]
      rw [PMF.map_bind]
      exact congrArg _ (funext fun draw => ih draw)
  | .requestProof _, 0, view, _ => by
      simp only [simulatedStepsWith, MaliciousVerifier.comapProofs]
      exact (PMF.pure_map _ _).symm
  | .requestProof next, remaining + 1, view, state => by
      have ih := fun request (simulated : P × State) =>
        simulatedStepsWith_mapProofs f answerQuery simulateProof chooser
          (next request (f request simulated.1)) remaining
          { view with proofs := view.proofs ++ [(request, simulated.1)] } simulated.2
      cases hChoice : chooser (view.mapProofs f) with
      | none =>
          simp only [simulatedStepsWith, MaliciousVerifier.comapProofs, hChoice]
          exact (PMF.pure_map _ _).symm
      | some request =>
          simp only [simulatedStepsWith, MaliciousVerifier.comapProofs, hChoice]
          rw [PMF.map_bind, PMF.bind_map]
          refine congrArg _ (funext fun simulated => ?_)
          exact (congrArg
            (fun mapped => simulatedStepsWith answerQuery
              (fun state request =>
                (simulateProof state request).map fun simulated =>
                  (f request simulated.1, simulated.2))
              chooser (next request (f request simulated.1)) remaining mapped simulated.2)
            (View.mapProofs_snoc f view request simulated.1)).trans (ih request simulated)

end VerifiableInference

#print axioms VerifiableInference.statisticalDistance_preimage_le
#print axioms VerifiableInference.eventProbability_map
#print axioms VerifiableInference.Prob_mapResult
#print axioms VerifiableInference.statisticalDistance_images_le
#print axioms VerifiableInference.MaliciousVerifier.queryBound_comapProofs
#print axioms VerifiableInference.realSteps_eq_stepsWith
#print axioms VerifiableInference.stepsWith_mapProofs
#print axioms VerifiableInference.simulatedSteps_eq_simulatedStepsWith
#print axioms VerifiableInference.simulatedStepsWith_mapProofs
