-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/JoinControls.lean: TWO TESTS AT THE JOIN: what soundness after an honest
commitment (SoundAfterHonestCommitmentFor, VerifiableInference/MoreStatements.lean), the form of
Johnson/Bind/Cpp/SoundAtCommitted.lean, does not test of a committer, and what it tests beside
completeness. Instances of Johnson/Bind/SilentAndBlind.lean at the description of the theorem on
soundness and at theCpp (Johnson/Bind/Cpp/Defs.lean).
NONE OF THESE THEOREMS SAYS THAT A BLIND COMMITTER FAILS THE FORM: without an accept of verify
no theorem can (an argument); and none says anything of the running committer (Bind.Twin.twinID).

Why. The form bounds accepts alone. A committer under whose commitments verify accepts nothing meets
it, whatever it does with the weights. So the join is no test of the committer by itself. Teeth are
shown here against blind committers alone, beside completeness; that it has teeth ONLY beside an
accept is an argument, no theorem.

Main names (namespace Bind.Cpp).
  sample_D₀, commit_D₀, extractorOn_nil, extractor_D₀_nil: the description's own honest side samples
    nothing, asks nothing and returns a commitment of zeros; in an empty log the extractor finds
    nothing.
  **`hollow_meets_join`**: THE POSITIVE TEST: at every Z in scope that is read, at every parser
    within n queries, THE DESCRIPTION's OWN HOLLOW COMMITTER MEETS THE FORM FOR EVERY CLAIM, at the
    error soundnessErrorInQueries (c + p) n. `hollow_meets_join_never`: at the claim that never holds: after that
    committer verify accepts nothing, but with probability soundnessErrorInQueries (c + p) n.
  honest_count_cpp: the committer of theCpp T, its sampler before it, asks at most 2^35 + 2 queries
    where T.id keeps the count.
  **`blind_join_and_complete`**: THE CONDITIONAL NEGATIVE TEST: a committer that is blind at the
    full size's shape and Z's files (BlindAt, Johnson/Bind/Cpp/Controls.lean) and keeps the count
    (CountAt T Z: a premise) cannot meet the form and completeness (CompleteFor, Ladder.lean)
    together at small errors, if some request meets completeness' claim at weights w and fails
    soundness' claim at weights w': 1 ≤ α + ε c p at c = 2^35 + 2. Here ε c p is the error ε AT the
    two numbers c and p: no product.
  **`blind_exact_join_and_complete`**: at THE CLAIM of exact match ("is the model's output": the
    claim, not the files' policy, of which nothing is asked) such a request exists at every Z that
    is read (`exists_parting`, from voting_served, Ladder/Ties.lean): a blind committer that keeps
    the count cannot meet SoundAfterHonestCommitment and CompleteOn … CanServe (the form of
    `completeOnCanServe`, AtFullSide/Face/TheSixLines.lean) together. At another claim, the policy
    (25856, 512, 1) among them, the
    parting request stays a premise.
  `blindTwin_exact_join_and_complete`: that at the member blindTwin g.
Limits. Tests alone. hollow_meets_join shows soundness of nothing: it is true for a poor reason,
and is stated to show that reason. The conditional negative tests take completeness as a premise,
and NO THEOREM OF THIS LIBRARY GIVES COMPLETENESS, OR ONE ACCEPT, AT A COMMITTER OF Johnson/Bind/:
so they refute nothing; they name what is missing. p bounds the honest prover's queries: a premise.
THE TWO TESTS DO NOT MEET: hollow_meets_join stands at the system of the description with its own
honest side; the conditional negative tests stand at theCpp T, whose committer samples a seed and
asks two queries before T.id: the hollow committer is no theCpp T. That the hollow committer, which
meets the form, is not complete follows from the general tool one_le_of_blind_join
(Johnson/Bind/SilentAndBlind.lean): argued, not typed. No blind T is shown to meet the form at a
small error at theCpp T. NOT COVERED: a committer that reads the weights and lays them wrongly, or
reads some of them (the general tool takes it, given two weights at which it is one algorithm and a
request that parts them). The conclusion stays 1 ≤ α + ε c p: no closed "cannot" at the goals' own
numbers is typed. Nothing on any program.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.SilentAndBlind
import Johnson.Bind.Cpp.Controls

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open Bind.Twin (Shape Table)
open Bind.Control

/-- In an empty log the told structure's named extractor finds nothing. -/
theorem extractorOn_nil {R : InnerCompilerInput} (T : LayoutsByPublicReading R) {J : Type} (φ : R.Index → Option J)
    (commitment : Commitment) : T.extractorOn φ commitment [] = none := rfl

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows
  FlashProve.thePlan FlashProve.theItem

/-- The description's own honest side samples nothing: its sampler returns at once. Which value it
returns is of no account (its type has one member): it is named here by the library's firstResult.
-/
theorem sample_D₀ : flashProveDescription.sample = .done (firstResult flashProveDescription.sample) := rfl

/-- It asks nothing and returns a commitment of zeros, whatever the weights. -/
theorem commit_D₀ (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) (ρ : flashProveDescription.Rand) :
    flashProveDescription.commit Z s w ρ = .done fun _ => false := rfl

/- And these. -/
attribute [local irreducible] Bind.Twin.twinID Bind.Twin.calls shapeFull twinBudget descriptionOfDataOnBytes T₀
  LayoutsByPublicReading.commitAtCoins

/-- In an empty log the description's extractor finds nothing. -/
theorem extractor_D₀_nil (Z : PublicFiles) (s : IntegerTransformer.Settings) (commitment : Commitment) :
    flashProveDescription.extractor Z s commitment [] = none := by
  rw [extractor_D₀]
  exact extractorOn_nil _ _ _

/-- **THE POSITIVE TEST: THE DESCRIPTION's OWN HOLLOW COMMITTER MEETS THE FORM OF THE JOIN, FOR
EVERY CLAIM**, at every Z in scope that is read and every parser within n queries. Its log is empty,
so the extractor gives nothing, so soundness under the files' policy bounds every accept. The form
is no test of the committer. -/
theorem hollow_meets_join (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (Form : Type)
    (prv : ModelWeights (settingsOfRead pp) → flashProveDescription.Rand → List Token → List Token →
      RandomizedAlgorithm Form)
    (parse : Parser flashProveDescription Z Form) (n : ℕ) (hn : parse.Within n)
    (claim : ModelWeights (settingsOfRead pp) → List Token → List Token → Prop) :
    SoundAfterHonestCommitmentFor (system flashProveDescription Z (settingsOfRead pp) Form prv parse) claim
      fun committerQueries proverQueries => soundnessErrorInQueries (committerQueries + proverQueries) n := by
  have h := VerifierAndGoals.AtTheName.g8bits_of_verify
  unfold G8bits at h
  rw [VerifierAndGoals.AtTheName.the_description_is] at h
  exact soundAfter_of_silent (ε := fun t => soundnessErrorInQueries t n)
    ((h.2 Z pp hs hr).2 Form prv parse n hn) sample_D₀
    (fun w ρ => commit_D₀ Z (settingsOfRead pp) w ρ)
    (extractor_D₀_nil Z (settingsOfRead pp) _) claim

/-- At the claim that never holds: after the hollow committer verify accepts nothing, but with
probability soundnessErrorInQueries (c + p) n. -/
theorem hollow_meets_join_never (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (Form : Type)
    (prv : ModelWeights (settingsOfRead pp) → flashProveDescription.Rand → List Token → List Token →
      RandomizedAlgorithm Form)
    (parse : Parser flashProveDescription Z Form) (n : ℕ) (hn : parse.Within n) :
    SoundAfterHonestCommitmentFor (system flashProveDescription Z (settingsOfRead pp) Form prv parse)
      (fun _ _ _ => False)
      fun committerQueries proverQueries => soundnessErrorInQueries (committerQueries + proverQueries) n :=
  hollow_meets_join Z pp hs hr Form prv parse n hn _

variable (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- The committer of theCpp T, its sampler before it, asks at most 2^35 + 2 queries, where T.id
keeps the count. -/
theorem honest_count_cpp (T : Letters) (Z : PublicFiles) (cnt : CountAt T Z)
    (s : IntegerTransformer.Settings) (w : ModelWeights s) :
    ((atSecondHashFunction (theCpp T prove)).sample.bind fun ρ =>
      ((atSecondHashFunction (theCpp T prove)).commit Z s w ρ).toRandomized).QueryBound (twinBudget + 2) :=
  fun t => commit_count T Z cnt s w (.inl t)

/-- **THE CONDITIONAL NEGATIVE TEST: A BLIND COMMITTER THAT KEEPS THE COUNT CANNOT MEET THE FORM OF
THE JOIN AND COMPLETENESS TOGETHER**, at small errors, if some request meets completeness' claim at
w and fails soundness' claim at w'. p bounds the honest prover's queries at that request. ε is taken
at the two numbers 2^35 + 2 and p: no product. -/
theorem blind_join_and_complete {T : Letters} {Z : PublicFiles}
    (hT : BlindAt T shapeFull Z.pol Z.lay Z.KL) (cnt : CountAt T Z)
    (s : IntegerTransformer.Settings)
    {claim served : ModelWeights s → List Token → List Token → Prop} {ε : ℕ → ℕ → ℝ≥0∞} {α : ℝ≥0∞}
    (hJ : SoundAfterHonestCommitmentFor (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z s) claim ε)
    (hC : CompleteFor (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z s) served α)
    (w w' : ModelWeights s) (prompt output : List Token) (h1 : served w prompt output)
    (h2 : ¬ claim w' prompt output) (p : ℕ)
    (hp : ∀ ρ, (prove Z s w ρ prompt output).QueryBound p) : 1 ≤ α + ε (twinBudget + 2) p :=
  one_le_of_blind_join_complete hJ hC (fun ρ => commit_blind hT s w w' ρ) prompt output h1 h2
    (honest_count_cpp prove T Z cnt s w') hp

/-- **A request that parts two weights at exact match**, at whatever the reader returns: the prompt
[0] and the output [1] can be served and are the model's at weights that vote for the token 1, and
are not the model's at weights that vote for the token 2. -/
theorem exists_parting {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) :
    ∃ w w' : ModelWeights (settingsOfRead pp), CanServe (settingsOfRead pp) w [0] [1] ∧
      ModelOutput (settingsOfRead pp) w [0] [1] ∧ ¬ ModelOutput (settingsOfRead pp) w' [0] [1] := by
  have v1 := voting_served (valid_of_read hr) 1 (by decide)
  have v2 := voting_served (valid_of_read hr) 2 (by decide)
  refine ⟨weightsOfIndex (valid_of_read hr) (Cm.biteI (fun _ => 0) fun _ => 1),
    weightsOfIndex (valid_of_read hr) (Cm.biteI (fun _ => 0) fun _ => 2), v1.1, v1.2, fun h => ?_⟩
  have a := h 0 (by decide)
  have b := v2.2 0 (by decide)
  exact absurd (Option.some.inj (a.symm.trans b)) (by decide)

/-- **AT THE CLAIM OF EXACT MATCH** ("is the model's output"; nothing is asked of the files'
policy), at every Z that is read: a blind committer that keeps the count cannot meet soundness after
an honest commitment and completeness on the requests that can be served together, at small errors.
The request: the prompt [0] and the output [1], at weights that vote for the token 1 and at weights
that vote for the token 2. -/
theorem blind_exact_join_and_complete {T : Letters} {Z : PublicFiles}
    (hT : BlindAt T shapeFull Z.pol Z.lay Z.KL) (cnt : CountAt T Z) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) {ε : ℕ → ℕ → ℝ≥0∞} {α : ℝ≥0∞}
    (hJ : SoundAfterHonestCommitment
      (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp)) ε)
    (hC : CompleteOn (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp))
      (CanServe (settingsOfRead pp)) α)
    (p : ℕ)
    (hp : ∀ w ρ, (prove Z (settingsOfRead pp) w ρ [0] [1]).QueryBound p) :
    1 ≤ α + ε (twinBudget + 2) p := by
  obtain ⟨w, w', h1, h2, h3⟩ := exists_parting hr
  exact one_le_of_blind_join hJ (fun ρ => commit_blind hT (settingsOfRead pp) w w' ρ) [0] [1] h3
    (hC w [0] [1] h1 h2) (honest_count_cpp prove T Z cnt (settingsOfRead pp) w') (hp w)

/-- That at the member: the running committer run at entries of 0. -/
theorem blindTwin_exact_join_and_complete (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) {ε : ℕ → ℕ → ℝ≥0∞} {α : ℝ≥0∞}
    (hJ : SoundAfterHonestCommitment
      (systemOfRecord (atSecondHashFunction (theCpp (blindTwin g) prove)) Z (settingsOfRead pp)) ε)
    (hC : CompleteOn (systemOfRecord (atSecondHashFunction (theCpp (blindTwin g) prove)) Z (settingsOfRead pp))
      (CanServe (settingsOfRead pp)) α)
    (p : ℕ)
    (hp : ∀ w ρ, (prove Z (settingsOfRead pp) w ρ [0] [1]).QueryBound p) :
    1 ≤ α + ε (twinBudget + 2) p :=
  blind_exact_join_and_complete prove (blind_blindTwin g shapeFull Z.pol Z.lay Z.KL)
    (count_blindTwin g Z) pp hr hJ hC p hp

end Bind.Cpp

end

#print axioms Bind.Cpp.extractorOn_nil
#print axioms Bind.Cpp.sample_D₀
#print axioms Bind.Cpp.commit_D₀
#print axioms Bind.Cpp.extractor_D₀_nil
#print axioms Bind.Cpp.hollow_meets_join
#print axioms Bind.Cpp.hollow_meets_join_never
#print axioms Bind.Cpp.honest_count_cpp
#print axioms Bind.Cpp.blind_join_and_complete
#print axioms Bind.Cpp.exists_parting
#print axioms Bind.Cpp.blind_exact_join_and_complete
#print axioms Bind.Cpp.blindTwin_exact_join_and_complete
