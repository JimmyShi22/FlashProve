-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/RefuseUnserved.lean: the provers under refuseUnserved, and what the compiled prover does at a request that is not
served.

1.  WHAT IS CLAIMED: facts on any three provers. This file proves neither completeness nor zero knowledge of the protocol.
2.  refuseUnserved (Protocol.lean): the same provers, but that the online prover withholds at every message of a request that is not
    served. Whether a request is served depends on the weights, which the prover holds.
3.  AT SERVED REQUESTS NOTHING TURNS: the abort set, the private stops, the output, the strategy and the tables are those of the given provers. So
    CompleteInParts holds of the new provers if and only if it holds of the given ones, and RunByRun holds of the new provers if and only if
    all its clauses but refuses hold of the given ones (ServedRuns); refuses holds of the new ones whatever the provers.
4.  AFTER COMPILATION: at a request that is not served, under every oracle and all coins, the compiled prover hands no proof string
    (proveAt_unserved), and the compiled verifier refuses what it hands, under every oracle (verifyW_unserved).
5.  STATED, NOT PROVED HERE: at compile, the prover hands out one fixed form there (Spec.compile_hands_no_proof), where the writer sends
    every typed proof without a proof string to that form (Protocol.WritesNoProof). That verify rejects the form is a fact about the
    parser at one form (Protocol.RejectsNoProof).
-/
import VerifiableInference.Final.CompilerTheorems
import VerifiableInference.Final.ZeroKnowledgeLaws

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {L : HolographicProtocol I X}

variable {provers : HonestProvers L} {Served : I → X → Prop}

/-! ## 1 Completeness carries both ways -/

theorem failsAt_refuse_iff (work : WorkBits L.onlineBatch.loc.shape) (table : (oneExternalString L.wordLength L.Symbol).Str) (n : ℕ)
    (w : I × L.EncodingRandomness × L.OutOfDomainSeed) (y : X × L.Rec)
    (h : Served w.1 y.1) (c : provers.onlineProver.Coin) (ρ : Rho L.onlineBatch.loc.shape) :
    FailsAt (provers.refuseUnserved Served).onlineProver work table (w.1, w.2.1, w.2.2, n) y c ρ ↔
      FailsAt provers.onlineProver work table (w.1, w.2.1, w.2.2, n) y c ρ := by
  have e : (provers.refuseUnserved Served).onlineProver.withheld (w.1, w.2.1, w.2.2, n) y =
      provers.onlineProver.withheld (w.1, w.2.1, w.2.2, n) y := refuseUnserved_withheld_eq provers Served n w y h
  unfold FailsAt
  rw [e]
  exact Iff.rfl

theorem failsRarely_refuse_iff (work : WorkBits L.onlineBatch.loc.shape) (table : (oneExternalString L.wordLength L.Symbol).Str) (n : ℕ)
    (w : I × L.EncodingRandomness × L.OutOfDomainSeed) (y : X × L.Rec)
    (h : Served w.1 y.1) (e : ℝ≥0∞) :
    FailsRarely (provers.refuseUnserved Served).onlineProver work table (w.1, w.2.1, w.2.2, n) y e ↔
      FailsRarely provers.onlineProver work table (w.1, w.2.1, w.2.2, n) y e := by
  have hs : {d : provers.onlineProver.Coin × Rho L.onlineBatch.loc.shape |
        FailsAt (provers.refuseUnserved Served).onlineProver work table (w.1, w.2.1, w.2.2, n) y d.1
          (work.cleared d.2)} =
      {d | FailsAt provers.onlineProver work table (w.1, w.2.1, w.2.2, n) y d.1 (work.cleared d.2)} :=
    Set.ext fun d => failsAt_refuse_iff work table n w y h d.1 _
  unfold FailsRarely
  exact iff_of_eq (congrArg (fun S => pr (unif (provers.onlineProver.Coin × Rho L.onlineBatch.loc.shape)) S ≤ e) hs)

/-- **Completeness as an IOP holds of the provers under refuseUnserved exactly where it holds of the provers.** -/
theorem completeInParts_refuse_iff (work : PartsWork L) (num : ℕ → Plains L.onlineBatch.loc.shape → Bool)
    (eO eL eB : ℝ≥0∞) :
    CompleteInParts L (provers.refuseUnserved Served) work num Served eO eL eB ↔
      CompleteInParts L provers work num Served eO eL eB :=
  ⟨fun h => ⟨h.offlineAccepted, h.linkAccepted,
      fun i x r e n hs => (failsRarely_refuse_iff work.online _ n (i, r, e) (x, L.recOf i r e) hs _).1
        (h.onlineAccepted i x r e n hs),
      h.sendsCopyNumber⟩,
    fun h => ⟨h.offlineAccepted, h.linkAccepted,
      fun i x r e n hs => (failsRarely_refuse_iff work.online _ n (i, r, e) (x, L.recOf i r e) hs _).2
        (h.onlineAccepted i x r e n hs),
      h.sendsCopyNumber⟩⟩

/-! ## 2 Zero knowledge, run by run, carries both ways -/

/-- All clauses of RunByRun but refuses: they speak of served requests alone. -/
structure ServedRuns (work : PartsWork L) (provers : HonestProvers L) (simulators : RunSimulators L)
    (inRange : I → Prop) (Served : I → X → Prop) (N : Budget) : Prop where
  tables : provers.SpeakOfTheirTables
  offline : ExactOutsideStops provers.offlineProver (fun w y => inRange w.1 ∧ L.validT w y)
    work.offline.cleared simulators.offline
  link : ExactOutsideStops provers.linkProver (fun w y => inRange w.1 ∧ L.validL w y) work.link.cleared
    simulators.link
  online : ∀ n, ExactOutsideStops (provers.onlineAtCopy n)
    (fun w y => inRange w.1 ∧ L.validB Served w y) work.online.cleared (simulators.online n)
  offlineStops : PrivateStopsAtMost provers.offlineProver (fun w y => inRange w.1 ∧ L.validT w y) work.offline
    N.offlineStops
  linkStops : PrivateStopsAtMost provers.linkProver (fun w y => inRange w.1 ∧ L.validL w y) work.link N.linkStops
  onlineStops : ∀ n, PrivateStopsAtMost (provers.onlineAtCopy n)
    (fun w y => inRange w.1 ∧ L.validB Served w y) work.online N.onlineStops

theorem exact_refuse_iff (n : ℕ) (clear : Rho L.onlineBatch.loc.shape → Rho L.onlineBatch.loc.shape)
    (valid : I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop) (hv : ∀ w y, valid w y → Served w.1 y.1)
    (sim : Compile.Lifetime.SimOf L.onlineBatch.loc) :
    ExactOutsideStops ((provers.refuseUnserved Served).onlineAtCopy n) valid clear sim ↔
      ExactOutsideStops (provers.onlineAtCopy n) valid clear sim :=
  ⟨fun h w y v ρ hρ => by
      have e := h w y v ρ (by rw [refuseUnserved_hid_served provers Served n w y (hv w y v)]; exact hρ)
      rw [refuseUnserved_output provers Served n w y (hv w y v)] at e
      exact e,
    fun h w y v ρ hρ => by
      rw [refuseUnserved_output provers Served n w y (hv w y v)]
      exact h w y v ρ (by rw [← refuseUnserved_hid_served provers Served n w y (hv w y v)]; exact hρ)⟩

theorem privateStops_refuse_iff (work : WorkBits L.onlineBatch.loc.shape) (n : ℕ) (w : I × L.EncodingRandomness × L.OutOfDomainSeed) (y : X × L.Rec)
    (h : Served w.1 y.1) (e : ℝ≥0∞) :
    chanceAtPassing work (fun ρ => ρ ∈ ((provers.refuseUnserved Served).onlineAtCopy n).Hid w y) ≤ e ↔
      chanceAtPassing work (fun ρ => ρ ∈ (provers.onlineAtCopy n).Hid w y) ≤ e := by
  rw [refuseUnserved_hid_served provers Served n w y h]

/-- **RunByRun holds of the provers under refuseUnserved exactly where its served clauses hold of the provers.** -/
theorem runByRun_refuse_iff (work : PartsWork L) (simulators : RunSimulators L) (inRange : I → Prop) (N : Budget) :
    RunByRun work (provers.refuseUnserved Served) simulators inRange Served N ↔
      ServedRuns work provers simulators inRange Served N :=
  ⟨fun h => ⟨⟨h.tables.offline, h.tables.link, h.tables.online⟩, h.offline, h.link,
      fun n => (exact_refuse_iff n _ _ (fun _ _ v => v.2.2) _).1 (h.online n), h.offlineStops, h.linkStops,
      fun n w y v => (privateStops_refuse_iff work.online n w y v.2.2 _).1 (h.onlineStops n w y v)⟩,
    fun h => ⟨⟨h.tables.offline, h.tables.link, h.tables.online⟩, h.offline, h.link,
      fun n => (exact_refuse_iff n _ _ (fun _ _ v => v.2.2) _).2 (h.online n), h.offlineStops, h.linkStops,
      fun n w y v => (privateStops_refuse_iff work.online n w y v.2.2 _).2 (h.onlineStops n w y v),
      fun n w y _ _ hs => refuseUnserved_withheld provers Served n w y hs⟩⟩

/-! ## 3 After compilation -/

/-- The online prover withholds at every message of a request that is not served. -/
def HonestProvers.RefusesUnserved (provers : HonestProvers L) (Served : I → X → Prop) : Prop :=
  ∀ w y, ¬ Served w.1 y.1 → provers.onlineProver.withheld w y = Set.univ

/-- Under refuseUnserved it does, whatever the provers. -/
theorem refusesUnserved_refuseUnserved (provers : HonestProvers L) (Served : I → X → Prop) :
    (provers.refuseUnserved Served).RefusesUnserved Served :=
  fun _ _ hs => Set.eq_univ_of_forall fun _ => Or.inr (Or.inl hs)

variable {offlineRoundMarks : RoundSplits L.offline.shape} {linkRoundMarks : RoundSplits L.link.shape}

/-- What is handed is nothing if the test for a stop says yes at every message. -/
theorem shown_of_stops {P' : Type} {s : Shape} {stop : Rho s → Bool} (h : ∀ ρ, stop ρ = true) (r : Res (P' × Tr s)) :
    shown stop r = none := by
  cases r with
  | ok a =>
    show (if stop a.2.rho then none else some a.1) = none
    rw [h]
    rfl
  | noFormat => rfl
  | ranOut _ => rfl

/-- At a request that is not served the compiled run's test for a stop says yes at every message. -/
theorem stopB_unserved (w : HashLayout L offlineRoundMarks linkRoundMarks) (s : CompiledSettings w provers) (hR : provers.RefusesUnserved Served)
    {i : I} {x : X} (hS : ¬ Served i x) (r : L.EncodingRandomness) (e : L.OutOfDomainSeed) (n : ℕ) (ρ : Rho L.onlineBatch.loc.shape) :
    (honestSide w provers s).side.st.stopB i r e x n ρ = true :=
  @decide_eq_true _ (_) (by
    have h := hR (i, r, e, n) (x, L.recOf i r e) hS
    exact h ▸ Set.mem_univ ρ)

/-- **THE COMPILED PROVER HANDS NO PROOF STRING AT A REQUEST THAT IS NOT SERVED**, under every oracle, at all coins. -/
theorem proveAt_unserved (w : HashLayout L offlineRoundMarks linkRoundMarks) (s : CompiledSettings w provers) (hR : provers.RefusesUnserved Served)
    (isk : Isk 256 L w.LeafBody offlineRoundMarks linkRoundMarks) {x : X} (hS : ¬ Served isk.i x)
    (d : DrawP 256 L w.LeafBody offlineRoundMarks linkRoundMarks (honestSide w provers s).side.KB)
    (g : Fam (typedOracleFamily 256 w.queryLayout.K (typedOracleCarrier L w.LeafBody offlineRoundMarks linkRoundMarks))) :
    ((proveAt w.queryLayout w.answerCode w.fixedSample (honestSide w provers s).side isk x d).det g).piB = none := by
  unfold proveAt
  split
  · rfl
  · rw [OComp.det_bind]
    exact shown_of_stops (fun ρ => stopB_unserved w s hR hS _ _ _ ρ) _

/-- **The compiled verifier refuses a proof without a string**, under every oracle. -/
theorem verifyW_no_string (w : HashLayout L offlineRoundMarks linkRoundMarks)
    (k : FullKey 256 L offlineRoundMarks linkRoundMarks) (x : X) (π : RequestProof 256 L) (h : π.piB = none) :
    verifyW w.queryLayout w.seedQueries w.answerCode w.fixedSample w.compilerParameters k x π = .pure false := by
  show verifyAtFullKey w.queryLayout w.seedQueries w.answerCode w.fixedSample w.compilerParameters _ x ⟨0, π.copy, π.piB⟩ = _
  rw [h]
  unfold verifyAtFullKey
  split <;> first | rfl | simp_all

/-- **So the compiled verifier refuses what the compiled prover hands at a request that is not served**, under every two oracles. -/
theorem verifyW_unserved (w : HashLayout L offlineRoundMarks linkRoundMarks) (s : CompiledSettings w provers) (hR : provers.RefusesUnserved Served)
    (isk : Isk 256 L w.LeafBody offlineRoundMarks linkRoundMarks) {x : X} (hS : ¬ Served isk.i x)
    (d : DrawP 256 L w.LeafBody offlineRoundMarks linkRoundMarks (honestSide w provers s).side.KB)
    (k : FullKey 256 L offlineRoundMarks linkRoundMarks)
    (g : Fam (typedOracleFamily 256 w.queryLayout.K (typedOracleCarrier L w.LeafBody offlineRoundMarks linkRoundMarks))) :
    verifyW w.queryLayout w.seedQueries w.answerCode w.fixedSample w.compilerParameters k x
      ((proveAt w.queryLayout w.answerCode w.fixedSample (honestSide w provers s).side isk x d).det g) = .pure false :=
  verifyW_no_string w k x _ (proveAt_unserved w s hR isk hS d g)

/-! ## 4 At compile: stated -/

/-- The writer sends every typed proof without a proof string to the one form noProof. A premise on
the writer alone. -/
def Compilable.WritesNoProof (input : Compilable) (noProof : input.format.Form) : Prop :=
  ∀ typed : TypedProof input.publicSide.protocol input.publicSide.offlineRoundSplits
      input.publicSide.linkRoundSplits,
    typed.2.2.piB = none → input.format.write typed = noProof

/-- The verifier rejects the form noProof, under every hash function: a fact about the parser at one
form. -/
def Compilable.RejectsNoProof (input : Compilable) (noProof : input.format.Form) : Prop :=
  ∀ (hash : VerifiableInference.Hash) (commitment : Commitment) (prompt output : List Token),
    ((compile input).verify commitment prompt output noProof).evaluate hash = false

namespace Spec

/-- **At a request that builds an instance which is not served, compile's prover hands out the form
noProof**, under every oracle and at all coins: with probability 0 anything else. -/
def compile_hands_no_proof (input : Compilable) : Prop :=
  ∀ (Served : input.publicSide.Index → input.publicSide.Instance → Prop)
    (noProof : input.format.Form),
    input.provers.RefusesUnserved Served → input.WritesNoProof noProof →
    ∀ (weights : input.publicSide.model.Weights)
      (randomness : (compile input).CommitmentRandomness)
      (request : List Token × List Token) (x : input.publicSide.Instance),
      (input.publicSide.layoutAt input.wiring.baseDigest input.wiring.baseFurther).input.buildInstance
        request [] = some x →
      ¬ Served (input.publicSide.indexOf weights) x →
      VerifiableInference.Prob ((compile input).prove weights randomness request.1 request.2)
        {form | form ≠ noProof} = 0

end Spec

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.completeInParts_refuse_iff
#print axioms VerifiableInference.Compilation.runByRun_refuse_iff
#print axioms VerifiableInference.Compilation.stopB_unserved
#print axioms VerifiableInference.Compilation.proveAt_unserved
#print axioms VerifiableInference.Compilation.verifyW_no_string
#print axioms VerifiableInference.Compilation.verifyW_unserved
#print axioms VerifiableInference.Compilation.refusesUnserved_refuseUnserved
#print axioms VerifiableInference.Compilation.Compilable.WritesNoProof
#print axioms VerifiableInference.Compilation.Compilable.RejectsNoProof
#print axioms VerifiableInference.Compilation.Spec.compile_hands_no_proof
