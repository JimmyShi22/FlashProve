-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/AgreementZeroKnowledge.lean

Proved, for every argument system: `ZeroKnowledge system ζ` is the stronger form of index privacy
that ZKCP/Defs.lean defines (HasStrongIndexPrivacyWith), for some simulator, for the relation and
the algorithms of the argument system (`zeroKnowledge_iff`). It gives index privacy,
ZKCP.HasIndexPrivacy (`indexPrivacy_of_zeroKnowledge`), and the three statements together give
ZKCP.IsZKCPArg (`CompleteSoundZeroKnowledge.toIsZKCPArg`). Not proved here: that any argument system
is zero-knowledge. Which systems of this library have a statement or a proof of zero knowledge:
lean/THEOREM.md. `ZeroKnowledge`, as defined in VerifiableInference/Statements.lean, is proved of no
system in this library. No privacy statement is proved about any program.
-/
import VerifiableInference.Agreement

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

open RandomizedAlgorithm

/-! ## 1. The same verifiers, views, simulators and choosers -/

namespace MaliciousVerifier
variable {P : Type}

/-- The same verifier in the library's type. -/
def toUpload : MaliciousVerifier P → ZKCP.AdvVerifier 256 (List Token × List Token) P
  | stop => .halt
  | query input next => .query input fun answer => (next answer).toUpload
  | sample bound next => .sample bound fun draw => (next draw).toUpload
  | requestProof next => .request fun request proof => (next request proof).toUpload

/-- A verifier of the library's type, in the renamed type. -/
def ofUpload : ZKCP.AdvVerifier 256 (List Token × List Token) P → MaliciousVerifier P
  | .halt => stop
  | .query input next => query input fun answer => ofUpload (next answer)
  | .sample bound next => sample bound fun draw => ofUpload (next draw)
  | .request next => requestProof fun request proof => ofUpload (next request proof)

theorem toUpload_ofUpload : ∀ verifier : ZKCP.AdvVerifier 256 (List Token × List Token) P,
    (ofUpload verifier).toUpload = verifier
  | .halt => rfl
  | .query input next => by
      show ZKCP.AdvVerifier.query input (fun answer => (ofUpload (next answer)).toUpload) =
          ZKCP.AdvVerifier.query input next
      exact congrArg _ (funext fun answer => toUpload_ofUpload (next answer))
  | .sample bound next => by
      show ZKCP.AdvVerifier.sample bound (fun draw => (ofUpload (next draw)).toUpload) =
          ZKCP.AdvVerifier.sample bound next
      exact congrArg _ (funext fun draw => toUpload_ofUpload (next draw))
  | .request next => by
      show ZKCP.AdvVerifier.request (fun request proof => (ofUpload (next request proof)).toUpload)
          = ZKCP.AdvVerifier.request next
      exact congrArg _ (funext fun request => funext fun proof => toUpload_ofUpload
          (next request proof))

theorem queryBound_toUpload : ∀ (verifier : MaliciousVerifier P) (queries : ℕ),
    verifier.toUpload.QueryBound queries ↔ verifier.QueryBound queries
  | stop, _ => Iff.rfl
  | query _ _, 0 => Iff.rfl
  | query _ next, queries + 1 => forall_congr' fun answer => queryBound_toUpload (next answer)
      queries
  | sample _ next, queries => forall_congr' fun draw => queryBound_toUpload (next draw) queries
  | requestProof next, queries =>
      forall_congr' fun request => forall_congr' fun proof => queryBound_toUpload
          (next request proof) queries

end MaliciousVerifier

variable {PP P : Type}

/-- The same view in the library's type. -/
def View.toUpload (view : View P) : ZKCP.View 256 Commitment (List Token × List Token) P :=
  ⟨view.commitment, view.proofs, view.queryLog, view.randomDraws⟩

/-- A view of the library's type, in the renamed type. -/
def View.ofUpload (view : ZKCP.View 256 Commitment (List Token × List Token) P) : View P :=
  ⟨view.ivk, view.sessions, view.trace, view.coins⟩

theorem View.ofUpload_toUpload (view : View P) : View.ofUpload view.toUpload = view := rfl
theorem View.toUpload_ofUpload (view : ZKCP.View 256 Commitment (List Token × List Token) P) :
    (View.ofUpload view).toUpload = view := rfl

/-- The same simulator in the library's type. -/
def Simulator.toUpload (simulator : Simulator PP P) : ZKCP.Simulator 256 PP Commitment
    (List Token × List Token) P :=
  ⟨simulator.State, simulator.start, simulator.answerQuery, simulator.simulateProof⟩

/-- A simulator of the library's type, in the renamed type. -/
def Simulator.ofUpload (simulator : ZKCP.Simulator 256 PP Commitment (List Token × List Token) P) :
    Simulator PP P :=
  ⟨simulator.St, simulator.init, simulator.answer, simulator.prove⟩

theorem Simulator.toUpload_ofUpload (simulator : ZKCP.Simulator 256 PP Commitment
    (List Token × List Token) P) :
    (Simulator.ofUpload simulator).toUpload = simulator := rfl

/-- The same chooser in the library's type of environments (`ZKCP.ViewEnv`): it has no witness to
choose. -/
def chooserToUpload (chooser : View P → Option (List Token × List Token)) :
    ZKCP.ViewEnv 256 Commitment (List Token × List Token) Unit P :=
  fun view => (chooser (View.ofUpload view)).map fun request => (request, ())

/-- A chooser of the library's type, in the renamed type. -/
def chooserOfUpload (chooser : ZKCP.ViewEnv 256 Commitment (List Token × List Token) Unit P) :
    View P → Option (List Token × List Token) :=
  fun view => (chooser view.toUpload).map Prod.fst

theorem chooserToUpload_ofUpload (chooser : ZKCP.ViewEnv 256 Commitment (List Token × List Token)
    Unit P) :
    chooserToUpload (chooserOfUpload chooser) = chooser := by
  funext view
  show ((chooser view).map Prod.fst).map (fun request => (request, ())) = chooser view
  cases chooser view with
  | none => rfl
  | some _ => rfl

/-! ## 2. The same experiments

The two experiments of Statements.lean correspond to those of ZKCP/Defs.lean step by step. -/

theorem OComp_bind_assoc {α β γ : Type} : ∀ (first : ZKCP.OComp 256 α)
    (second : α → ZKCP.OComp 256 β) (third : β → ZKCP.OComp 256 γ),
    (first.bind second).bind third = first.bind fun a => (second a).bind third
  | .pure _, _, _ => rfl
  | .query input next, second, third => by
      show ZKCP.OComp.query input (fun answer => ((next answer).bind second).bind third)
        = ZKCP.OComp.query input fun answer => (next answer).bind fun a => (second a).bind third
      exact congrArg _ (funext fun answer => OComp_bind_assoc (next answer) second third)
  | .sample bound next, second, third => by
      show ZKCP.OComp.sample bound (fun draw => ((next draw).bind second).bind third)
        = ZKCP.OComp.sample bound fun draw => (next draw).bind fun a => (second a).bind third
      exact congrArg _ (funext fun draw => OComp_bind_assoc (next draw) second third)

variable (system : ArgumentSystem)

/-- The verifier's steps of the real experiment are those of the library's real experiment. -/
theorem realSteps_toUpload (chooser : View system.Proof → Option (List Token × List Token))
    (weights : system.Weights) (randomness : system.CommitmentRandomness) :
    ∀ (verifier : MaliciousVerifier system.Proof) (remaining : ℕ) (view : View system.Proof),
      (realSteps system chooser weights randomness verifier remaining view).toUpload
        = (ZKCP.realLoop system.uploadArgument (chooserToUpload chooser) (weights, randomness)
            verifier.toUpload remaining
            view.toUpload).bind fun result => ZKCP.OComp.pure (View.ofUpload result)
  | .stop, _, _ => rfl
  | .query input next, remaining, view => by
      have ih := fun answer => realSteps_toUpload chooser weights randomness (next answer) remaining
        { view with queryLog := view.queryLog ++ [(input, answer)] }
      simp only [realSteps, MaliciousVerifier.toUpload, ZKCP.realLoop, RandomizedAlgorithm.toUpload,
          ZKCP.OComp.bind]
      exact congrArg _ (funext fun answer => ih answer)
  | .sample bound next, remaining, view => by
      have ih := fun draw => realSteps_toUpload chooser weights randomness (next draw) remaining
        { view with randomDraws := view.randomDraws ++ [draw.val] }
      simp only [realSteps, MaliciousVerifier.toUpload, ZKCP.realLoop, RandomizedAlgorithm.toUpload,
          ZKCP.OComp.bind]
      exact congrArg _ (funext fun draw => ih draw)
  | .requestProof _, 0, _ => rfl
  | .requestProof next, remaining + 1, view => by
      have ih := fun request proof => realSteps_toUpload chooser weights randomness
          (next request proof) remaining
        { view with proofs := view.proofs ++ [(request, proof)] }
      have hZ : chooserToUpload chooser view.toUpload = (chooser view).map fun request =>
          (request, ()) := rfl
      cases hChoice : chooser view with
      | none =>
          rw [hChoice] at hZ
          simp only [realSteps, MaliciousVerifier.toUpload, ZKCP.realLoop, hChoice, hZ,
              Option.map_none]
          rfl
      | some request =>
          rw [hChoice] at hZ
          simp only [realSteps, MaliciousVerifier.toUpload, ZKCP.realLoop, hChoice, hZ,
              Option.map_some]
          rw [toUpload_bind, OComp_bind_assoc]
          exact congrArg _ (funext fun proof => ih request proof)

/-- The verifier's steps of the simulated experiment are those of the library's ideal experiment. -/
theorem simulatedSteps_eq (simulator : Simulator PP P) (chooser : View P → Option
    (List Token × List Token)) :
    ∀ (verifier : MaliciousVerifier P) (remaining : ℕ) (view : View P) (state : simulator.State),
      simulatedSteps simulator chooser verifier remaining view state
        = (ZKCP.idealLoop simulator.toUpload (chooserToUpload chooser) verifier.toUpload remaining
            view.toUpload state).bind
            fun result => PMF.pure (View.ofUpload result)
  | .stop, _, view, _ => by
      simp only [simulatedSteps, MaliciousVerifier.toUpload, ZKCP.idealLoop, PMF.pure_bind]
      rfl
  | .query input next, remaining, view, state => by
      have ih := fun (answered : Digest × simulator.State) => simulatedSteps_eq simulator chooser
          (next answered.1) remaining
        { view with queryLog := view.queryLog ++ [(input, answered.1)] } answered.2
      simp only [simulatedSteps, MaliciousVerifier.toUpload, ZKCP.idealLoop, PMF.bind_bind]
      exact congrArg _ (funext fun answered => ih answered)
  | .sample bound next, remaining, view, state => by
      have ih := fun draw => simulatedSteps_eq simulator chooser (next draw) remaining
        { view with randomDraws := view.randomDraws ++ [draw.val] } state
      simp only [simulatedSteps, MaliciousVerifier.toUpload, ZKCP.idealLoop, PMF.bind_bind]
      exact congrArg _ (funext fun draw => ih draw)
  | .requestProof _, 0, view, _ => by
      simp only [simulatedSteps, MaliciousVerifier.toUpload, ZKCP.idealLoop, PMF.pure_bind]
      rfl
  | .requestProof next, remaining + 1, view, state => by
      have ih := fun request (simulated : P × simulator.State) => simulatedSteps_eq simulator
          chooser (next request simulated.1) remaining
        { view with proofs := view.proofs ++ [(request, simulated.1)] } simulated.2
      have hZ : chooserToUpload chooser view.toUpload = (chooser view).map fun request =>
          (request, ()) := rfl
      cases hChoice : chooser view with
      | none =>
          rw [hChoice] at hZ
          simp only [simulatedSteps, MaliciousVerifier.toUpload, ZKCP.idealLoop, hChoice, hZ,
              Option.map_none, PMF.pure_bind]
          rfl
      | some request =>
          rw [hChoice] at hZ
          simp only [simulatedSteps, MaliciousVerifier.toUpload, ZKCP.idealLoop, hChoice, hZ,
              Option.map_some, PMF.bind_bind]
          exact congrArg _ (funext fun simulated => ih request simulated)

/-- The real experiment is the library's real experiment. -/
theorem realExperiment_toUpload (verifier : Commitment → MaliciousVerifier system.Proof)
    (chooser : View system.Proof → Option (List Token × List Token)) (weights : system.Weights)
        (proofCount : ℕ) :
    (realExperiment system verifier chooser weights proofCount).toUpload
      = (ZKCP.realExp system.uploadArgument (fun commitment => (verifier commitment).toUpload)
          (chooserToUpload chooser)
          weights proofCount).bind fun result => ZKCP.OComp.pure (View.ofUpload result) := by
  show (system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit weights randomness).toRandomized.bind fun commitment =>
        realSteps system chooser weights randomness (verifier commitment) proofCount
            ⟨commitment, [], [], []⟩).toUpload
    = ((system.committer weights).toUpload.bind fun key =>
        ZKCP.realLoop system.uploadArgument (chooserToUpload chooser) key.2
            (verifier key.1).toUpload proofCount ⟨key.1, [], [], []⟩).bind
          fun result => ZKCP.OComp.pure (View.ofUpload result)
  simp only [ArgumentSystem.committer, toUpload_bind, OComp_bind_assoc, realSteps_toUpload,
      RandomizedAlgorithm.toUpload, ZKCP.OComp.bind]
  rfl

/-- The probability of an event under the image of a distribution is that of its preimage. -/
theorem prob_bind_pure_map {α β : Type} (distribution : PMF α) (f : α → β) (event : Set β) :
    ZKCP.prob (distribution.bind fun a => PMF.pure (f a)) event = ZKCP.prob distribution
        (f ⁻¹' event) := by
  rw [ZKCP.prob_bind, ZKCP.prob_eq_expect]
  refine ZKCP.expect_congr _ fun a => ?_
  rw [ZKCP.prob_pure]
  rfl

theorem Prob_realExperiment (verifier : Commitment → MaliciousVerifier system.Proof)
    (chooser : View system.Proof → Option (List Token × List Token)) (weights : system.Weights)
        (proofCount : ℕ)
    (event : Set (View system.Proof)) :
    Prob (realExperiment system verifier chooser weights proofCount) event
      = ZKCP.Pr (ZKCP.realExp system.uploadArgument (fun commitment =>
          (verifier commitment).toUpload) (chooserToUpload chooser)
          weights proofCount) (fun _ => View.ofUpload ⁻¹' event) := by
  rw [Prob_eq_Pr, realExperiment_toUpload]
  unfold ZKCP.Pr ZKCP.PrCoins
  refine lintegral_congr fun H => ?_
  rw [ZKCP.run_bind]
  exact prob_bind_pure_map _ _ _

/-- The simulated experiment is the library's ideal experiment. -/
theorem simulatedExperiment_eq (simulator : Simulator system.PublicParameters system.Proof)
    (verifier : Commitment → MaliciousVerifier system.Proof)
    (chooser : View system.Proof → Option (List Token × List Token)) (weights : system.Weights)
        (proofCount : ℕ) :
    simulatedExperiment system simulator verifier chooser weights proofCount
      = (ZKCP.idealExp system.uploadRelation simulator.toUpload
          (fun commitment => (verifier commitment).toUpload)
          (chooserToUpload chooser) weights proofCount).bind fun result => PMF.pure
              (View.ofUpload result) := by
  unfold simulatedExperiment ZKCP.idealExp
  simp only [simulatedSteps_eq, PMF.bind_bind]
  rfl

/-- The statistical distance of two distributions on views is the same in both types of views. -/
theorem statisticalDistance_views (first second : Set (ZKCP.View 256 Commitment
    (List Token × List Token) P) → ℝ≥0∞) :
    statisticalDistance (fun event : Set (View P) => first (View.ofUpload ⁻¹' event))
        (fun event => second (View.ofUpload ⁻¹' event))
      = ZKCP.SD first second := by
  unfold statisticalDistance ZKCP.SD
  exact Function.Surjective.iSup_comp
    (f := fun event : Set (View P) => (View.ofUpload ⁻¹' event : Set
        (ZKCP.View 256 Commitment (List Token × List Token) P)))
    (fun event => ⟨View.toUpload ⁻¹' event, rfl⟩) (fun event => max (first event - second event)
        (second event - first event))

/-! ## 3. Zero-knowledge -/

/-- `ZeroKnowledge` is the stronger form of index privacy of ZKCP/Defs.lean
(HasStrongIndexPrivacyWith), for some simulator, for the relation and the algorithms of the argument
system.
Which systems of this library have a statement or a proof of zero knowledge: lean/THEOREM.md.
`ZeroKnowledge` is proved of no system in this library. -/
theorem zeroKnowledge_iff (ζ : ℕ → ℕ → ℝ≥0∞) :
    ZeroKnowledge system ζ ↔ ∃ S : ZKCP.Simulator 256 system.PublicParameters Commitment
        (List Token × List Token) system.Proof,
      ZKCP.HasStrongIndexPrivacyWith system.uploadRelation system.uploadArgument S ζ := by
  -- the two quantities of the statement, in the library's terms
  have key : ∀ (simulator : Simulator system.PublicParameters system.Proof)
      (verifier : Commitment → MaliciousVerifier system.Proof)
      (chooser : View system.Proof → Option (List Token × List Token)) (weights : system.Weights)
          (proofCount : ℕ),
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
    intro simulator verifier chooser weights proofCount
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
  constructor
  · rintro ⟨simulator, h⟩
    refine ⟨simulator.toUpload, fun weights Z hZ tV Vt N hV => ?_⟩
    have hChooser : ∀ view prompt output, chooserOfUpload Z view = some (prompt, output) →
        system.IsModelOutput weights prompt output := by
      intro view prompt output hChoice
      have hChoice' : (Z view.toUpload).map Prod.fst = some (prompt, output) := hChoice
      cases hValue : Z view.toUpload with
      | none => rw [hValue] at hChoice'; cases hChoice'
      | some xw =>
          rw [hValue] at hChoice'
          have hx : xw.1 = (prompt, output) := Option.some.inj hChoice'
          have hRel := hZ view.toUpload xw.1 xw.2 hValue
          rw [hx] at hRel
          exact hRel
    have h' := h weights (chooserOfUpload Z) hChooser tV
        (fun commitment => MaliciousVerifier.ofUpload (Vt commitment)) N
      (fun commitment => (MaliciousVerifier.queryBound_toUpload _ tV).mp
          (by rw [MaliciousVerifier.toUpload_ofUpload]; exact hV commitment))
    have k := key simulator (fun commitment => MaliciousVerifier.ofUpload (Vt commitment))
        (chooserOfUpload Z) weights N
    simp only [MaliciousVerifier.toUpload_ofUpload, chooserToUpload_ofUpload] at k
    rw [k.1, k.2] at h'
    exact h'
  · rintro ⟨S, h⟩
    refine ⟨Simulator.ofUpload S, fun weights chooser hChooser queries verifier proofCount hV => ?_⟩
    have hValid : ZKCP.ViewEnv.IsValid system.uploadRelation (chooserToUpload chooser) weights := by
      intro view x w hChoice
      have hChoice' : (chooser (View.ofUpload view)).map (fun request => (request, ())) = some
          (x, w) := hChoice
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
    have k := key (Simulator.ofUpload S) verifier chooser weights proofCount
    rw [k.1, k.2]
    exact h'

/-- `ZeroKnowledge` gives index privacy (ZKCP/Defs.lean: HasIndexPrivacy). -/
theorem indexPrivacy_of_zeroKnowledge (ζ : ℕ → ℕ → ℝ≥0∞) (h : ZeroKnowledge system ζ) :
    ZKCP.HasIndexPrivacy system.uploadRelation system.uploadArgument ζ := by
  obtain ⟨S, hS⟩ := (zeroKnowledge_iff system ζ).mp h
  refine ⟨S, fun i Z hZ => hS i (Z.onView i) ?_⟩
  intro v x w hv
  have e : (Z i v.sessions) = (x, w) := Option.some.inj hv
  have := hZ v.sessions
  rw [e] at this
  exact this

/-- An argument system that meets the three statements is an argument with the three properties
together (ZKCP/Defs.lean: IsZKCPArg), for its relation and its three algorithms. -/
theorem CompleteSoundZeroKnowledge.toIsZKCPArg {system : ArgumentSystem} {α : ℝ≥0∞} {ε : ℕ → ℝ≥0∞}
    {ζ : ℕ → ℕ → ℝ≥0∞}
    (h : CompleteSoundZeroKnowledge system α ε ζ) :
    ZKCP.IsZKCPArg system.uploadRelation system.uploadArgument α (fun tC tP => ε (tC + tP)) ζ :=
  ⟨(complete_iff system α).mp h.complete, indexBinding_of_sound system ε h.sound,
      indexPrivacy_of_zeroKnowledge system ζ h.zeroKnowledge⟩

end VerifiableInference
