-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/CompleteOfCoins.lean: CompleteOn (VerifiableInference/Steps.lean) FROM A
BOUND AT EVERY FIXING OF THE HONEST SIDE's COINS. General in the argument system.

If the sampler draws one number and asks the hash function nothing, and the prover draws one number
and is from there on an algorithm without coins, then the experiment of CompleteOn is a mean over
the two numbers; so a bound on the probability, over the hash function alone, that the verifier says
no, at each pair of numbers, is a bound for the experiment.

Main names.
  Prob_sample_le   if each continuation of a draw has the event with probability at most α, so has
    the draw: ZKCP.Pr_sample_le (ZKCP/AtCoins.lean) at the goals' own Prob.
  expFixed   the experiment with both numbers fixed: committer, prover, verifier: no coins.
  completeOn_of_coins   THE STATEMENT.
  run_expFixed   under a hash function the fixed experiment has one value.
  expFixed_le_Pr   THE FIXED EXPERIMENT AGAINST A PROGRAM WITHOUT COINS OVER THE ONE HASH FUNCTION:
    if, at every hash function, the verifier's no forces the program's value into E, then the
    probability of a no is at most Rom.Pr of E at that program.
  completeOn_of_programs   the two joined: CompleteOn from one such program for each fixing of the
    coins.

This file states no goal. A theorem about the goals' own definition, at letters.

Limits. expFixed is a new definition in the namespace VerifiableInference, on the goals' own type of
an argument system: it names no goal. The two forms (hs, hp) are premises: an honest side whose
sampler asks the hash function, or whose prover draws again later, is not covered. The bound at
fixed numbers is a premise. At α = 1 the statement says nothing.
Terms: lean/GLOSSARY.md.

-/
import VerifiableInference.Steps
import VerifiableInference.Bridge
import ZKCP.AtCoins
import ZKCP.ManyOfOne
import Rom.Bridge
import Rom.Cache

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifiableInference
open RandomizedAlgorithm

/-- If each continuation of a draw has the event with probability at most α, so has the draw. -/
theorem Prob_sample_le {β : Type} (n : ℕ) (next : Fin (n + 1) → RandomizedAlgorithm β)
    (event : Set β) (α : ℝ≥0∞) (h : ∀ draw, Prob (next draw) event ≤ α) :
    Prob (.sample n next) event ≤ α := by
  rw [Prob_eq_Pr]
  exact ZKCP.Pr_sample_le n (fun draw => (next draw).toUpload) event α fun draw =>
    (Prob_eq_Pr (next draw) event) ▸ h draw

variable (system : ArgumentSystem)

/-- The experiment with the honest side's coins fixed: committer, prover, verifier. -/
def expFixed (weights : system.Weights) (prompt output : List Token)
    (ρ : system.CommitmentRandomness) (prover : DeterministicAlgorithm system.Proof) :
    RandomizedAlgorithm Bool :=
  (system.commit weights ρ).toRandomized.bind fun commitment =>
    prover.toRandomized.bind fun proof =>
      (system.verify commitment prompt output proof).toRandomized

/-- **CompleteOn from a bound at every fixing of the coins.** -/
theorem completeOn_of_coins (domain : system.Weights → List Token → List Token → Prop) (α : ℝ≥0∞)
    {B N : ℕ} (ρOf : Fin (B + 1) → system.CommitmentRandomness)
    (hs : system.sampleCommitmentRandomness = .sample B fun t => .done (ρOf t))
    (pd : system.Weights → system.CommitmentRandomness → List Token → List Token → Fin (N + 1) →
      DeterministicAlgorithm system.Proof)
    (hp : ∀ w ρ p o, system.prove w ρ p o = .sample N fun a => (pd w ρ p o a).toRandomized)
    (h : ∀ w p o, domain w p o → system.IsModelOutput w p o → ∀ t a,
      Prob (expFixed system w p o (ρOf t) (pd w (ρOf t) p o a)) {accepted | accepted = false} ≤ α) :
    CompleteOn system domain α := by
  intro w p o hd hm
  show Prob (system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit w randomness).toRandomized.bind fun commitment =>
      (system.prove w randomness p o).bind fun proof =>
      (system.verify commitment p o proof).toRandomized) {accepted | accepted = false} ≤ α
  rw [hs]
  refine Prob_sample_le B _ _ α fun t => ?_
  show Prob ((system.commit w (ρOf t)).toRandomized.bind fun commitment =>
      (system.prove w (ρOf t) p o).bind fun proof =>
      (system.verify commitment p o proof).toRandomized) {accepted | accepted = false} ≤ α
  rw [hp]
  have e : Prob ((system.commit w (ρOf t)).toRandomized.bind fun commitment =>
      (RandomizedAlgorithm.sample N fun a => (pd w (ρOf t) p o a).toRandomized).bind fun proof =>
      (system.verify commitment p o proof).toRandomized) {accepted | accepted = false} =
      Prob (.sample N fun a => expFixed system w p o (ρOf t) (pd w (ρOf t) p o a))
        {accepted | accepted = false} := by
    refine Prob_congr_run (fun hash => ?_) _
    show _ = (PMF.uniformOfFintype (Fin (N + 1))).bind fun a =>
      (expFixed system w p o (ρOf t) (pd w (ρOf t) p o a)).run hash
    rw [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind]
    show ((PMF.uniformOfFintype (Fin (N + 1))).bind fun a =>
      (((pd w (ρOf t) p o a).toRandomized).bind fun proof =>
        (system.verify ((system.commit w (ρOf t)).evaluate hash) p o proof).toRandomized).run
          hash) = _
    refine congrArg _ (funext fun a => ?_)
    unfold expFixed
    rw [run_bind (first := (system.commit w (ρOf t)).toRandomized),
      DeterministicAlgorithm.run_toRandomized, PMF.pure_bind]
  rw [e]
  exact Prob_sample_le N _ _ α fun a => h w p o hd hm t a

/-- Under a hash function the fixed experiment has one value. -/
theorem run_expFixed (w : system.Weights) (p o : List Token) (ρ : system.CommitmentRandomness)
    (prover : DeterministicAlgorithm system.Proof) (hash : Hash) :
    (expFixed system w p o ρ prover).run hash =
      PMF.pure ((system.verify ((system.commit w ρ).evaluate hash) p o
        (prover.evaluate hash)).evaluate hash) := by
  unfold expFixed
  rw [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_bind,
    DeterministicAlgorithm.run_toRandomized, PMF.pure_bind,
    DeterministicAlgorithm.run_toRandomized]

/-- **The fixed experiment against a program without coins over the one hash function.** -/
theorem expFixed_le_Pr (w : system.Weights) (p o : List Token) (ρ : system.CommitmentRandomness)
    (prover : DeterministicAlgorithm system.Proof) {γ : Type} (c : Rom.OComp (Rom.rom 256) γ)
    (hc : c.NoCoin) (E : Set γ)
    (h : ∀ hash : Hash, (system.verify ((system.commit w ρ).evaluate hash) p o
      (prover.evaluate hash)).evaluate hash = false → c.det (Rom.famOf hash) ∈ E) :
    Prob (expFixed system w p o ρ prover) {accepted | accepted = false} ≤
      Rom.Pr c (fun _ => E) := by
  have e : Rom.Pr c (fun _ => E) = ZKCP.Pr (Rom.ofRom c) fun _ => E := by
    conv_lhs => rw [← Rom.toRom_ofRom c]
    exact Rom.Pr_toRom (Rom.ofRom c) fun _ => E
  rw [Prob_eq_Pr, e]
  refine MeasureTheory.lintegral_mono fun f => ?_
  show ZKCP.prob ((expFixed system w p o ρ prover).toUpload.run f) _ ≤
    ZKCP.prob ((Rom.ofRom c).run f) E
  have r2 : (Rom.ofRom c).run f = PMF.pure (c.det (Rom.famOf f)) := by
    rw [← Rom.runEager_toRom, Rom.toRom_ofRom]
    exact hc.runEager _
  rw [run_toUpload, run_expFixed, r2]
  refine ZKCP.prob_pure_le_of_support fun hv z hz => ?_
  rw [PMF.support_pure, Set.mem_singleton_iff] at hz
  rw [hz]
  exact h f hv

/-- **CompleteOn from programs without coins over the one hash function**: one for each fixing of
the coins: the verifier's no forces its value into its event, and the event has probability at most
α. The two statements above, joined. -/
theorem completeOn_of_programs (domain : system.Weights → List Token → List Token → Prop)
    (α : ℝ≥0∞) {B N : ℕ} (ρOf : Fin (B + 1) → system.CommitmentRandomness)
    (hs : system.sampleCommitmentRandomness = .sample B fun t => .done (ρOf t))
    (pd : system.Weights → system.CommitmentRandomness → List Token → List Token → Fin (N + 1) →
      DeterministicAlgorithm system.Proof)
    (hp : ∀ w ρ p o, system.prove w ρ p o = .sample N fun a => (pd w ρ p o a).toRandomized)
    {γ : Type}
    (c : system.Weights → List Token → List Token → Fin (B + 1) → Fin (N + 1) →
      Rom.OComp (Rom.rom 256) γ)
    (E : system.Weights → List Token → List Token → Fin (B + 1) → Fin (N + 1) → Set γ)
    (hc : ∀ w p o t a, (c w p o t a).NoCoin)
    (hno : ∀ w p o, domain w p o → system.IsModelOutput w p o → ∀ t a (hash : Hash),
      (system.verify ((system.commit w (ρOf t)).evaluate hash) p o
        ((pd w (ρOf t) p o a).evaluate hash)).evaluate hash = false →
      (c w p o t a).det (Rom.famOf hash) ∈ E w p o t a)
    (hε : ∀ w p o, domain w p o → system.IsModelOutput w p o → ∀ t a,
      Rom.Pr (c w p o t a) (fun _ => E w p o t a) ≤ α) :
    CompleteOn system domain α :=
  completeOn_of_coins system domain α ρOf hs pd hp fun w p o hd hm t a =>
    (expFixed_le_Pr system w p o (ρOf t) (pd w (ρOf t) p o a) (c w p o t a) (hc w p o t a)
      (E w p o t a) (hno w p o hd hm t a)).trans (hε w p o hd hm t a)

end VerifiableInference

#print axioms VerifiableInference.completeOn_of_programs
#print axioms VerifiableInference.run_expFixed
#print axioms VerifiableInference.expFixed_le_Pr
#print axioms VerifiableInference.Prob_sample_le
#print axioms VerifiableInference.completeOn_of_coins
