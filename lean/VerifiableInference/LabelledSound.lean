-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/LabelledSound.lean: SOUNDNESS, BINDING AND EXTRACTION DO NOT SEE A LABEL: each holds of an
argument system with a label beside each proof (labelled) if and only if it holds of the system, at the
same error; in the forms that name an extractor (soundForWith…, bindsWith…, extracts…), at the same
extractor. General in the system, in the labels and in their type.

Why it is so. The verifier drops the label, so a cheating prover's label is idle: drop it one way, lay
any label beside the proof the other way. The committer, its sampler and the model are the system's, so
what reads these alone is the same statement.

  `isModelOutput_labelled`: by definition (`labelled_verify`: VerifiableInference/Labelled.lean).
  `soundForWith_labelled`: from the system to the labelled one, at every extractor, claim and error.
    THE DIRECTION THAT THE TOP LINES NEED; it asks nothing of the type of labels.
  `soundForWith_of_labelled`, `soundForWith_labelled_iff`: back, where there is a label at all.
  `sound_labelled`, `sound_labelled_iff`.
  `bindsWith_labelled_iff`, `extractsCommittedWeights_labelled_iff`: by definition.
  `soundAndBinding_labelled`, `soundAndBinding_labelled_iff`.
  `soundOpened_labelled`, `soundOpened_labelled_iff`.
  `sound_labelled_of_no_label`: a control: why the directions back ask for a label.

Limits. Nothing on what a label says: no statement here reads the honest prover, so none reads the map
"label". A label is checked by no verifier, and soundness says nothing of it. Nothing on completeness
or zero knowledge, which do read the honest prover. So "Sound (labelled …)" never means that a label is
verified, sound or bound. THE DIRECTIONS BACK, AND SO THE FOUR "IF AND ONLY IF", ASK THAT THE TYPE OF LABELS
HAS A MEMBER. At a system with any weights w that costs nothing: the rule itself gives a label, label w
([], []). It bites only at a system WITH NO WEIGHTS AT ALL, the only kind at which a rule into an empty
type exists: there the labelled system has no proof, no prover ends, and it is sound at every error, 0
among them (`sound_labelled_of_no_label`), while the system itself need not be sound.
-/
import VerifiableInference.Labelled
import VerifiableInference.Binds
import VerifiableInference.Bridge

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-- One algorithm after another after a third: the brackets do not matter. -/
theorem RandomizedAlgorithm.bind_bind {α β γ : Type} (second : α → RandomizedAlgorithm β)
    (third : β → RandomizedAlgorithm γ) : ∀ first : RandomizedAlgorithm α,
      (first.bind second).bind third = first.bind fun result => (second result).bind third
  | .done _ => rfl
  | .query input next =>
      congrArg (RandomizedAlgorithm.query input)
        (funext fun answer => RandomizedAlgorithm.bind_bind second third (next answer))
  | .sample bound next =>
      congrArg (RandomizedAlgorithm.sample bound)
        (funext fun draw => RandomizedAlgorithm.bind_bind second third (next draw))

/-- A function of the result, then a further algorithm: the further algorithm at the function's value. -/
theorem RandomizedAlgorithm.bind_map_bind {α β γ : Type} (f : α → β)
    (rest : β → RandomizedAlgorithm γ) (first : RandomizedAlgorithm α) :
    (first.bind fun result => .done (f result)).bind rest = first.bind fun result => rest (f result) :=
  RandomizedAlgorithm.bind_bind (fun result => .done (f result)) rest first

variable {Label : Type} (system : ArgumentSystem)
  (label : system.Weights → List Token × List Token → Label)

/-- "The output tokens are the model's" is the same claim. -/
theorem isModelOutput_labelled :
    (labelled system label).IsModelOutput = system.IsModelOutput := rfl

/-! ## Soundness at an extractor -/

/-- **From the system to the labelled one**: soundness for a claim, at the same extractor and error. -/
theorem soundForWith_labelled (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞)
    (sound : SoundForWith system extractor claim ε) :
    SoundForWith (labelled system label) extractor claim ε := by
  intro committerQueries proverQueries State committer committerBound prover proverBound
  refine le_of_eq_of_le (congrArg (fun experiment => Prob experiment _) ?_)
    (sound committerQueries proverQueries State committer committerBound
      (fun state => (prover state).bind fun reply => .done (reply.1, reply.2.1, reply.2.2.2))
      fun state => queryBound_map _ _ _ (proverBound state))
  refine congrArg committer.withQueryLog.bind (funext fun made => ?_)
  obtain ⟨⟨commitment, state⟩, queryLog⟩ := made
  exact (RandomizedAlgorithm.bind_map_bind
    (fun reply : List Token × List Token × Label × system.Proof =>
      (reply.1, reply.2.1, reply.2.2.2))
    (fun reply : List Token × List Token × system.Proof =>
      (system.verify commitment reply.1 reply.2.1 reply.2.2).toRandomized.bind fun accepted =>
        .done (extractor commitment queryLog, reply.1, reply.2.1, accepted))
    (prover state)).symm

/-- **Back**, where there is a label. -/
theorem soundForWith_of_labelled [Nonempty Label]
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞)
    (sound : SoundForWith (labelled system label) extractor claim ε) :
    SoundForWith system extractor claim ε := by
  intro committerQueries proverQueries State committer committerBound prover proverBound
  refine le_of_eq_of_le (congrArg (fun experiment => Prob experiment _) ?_)
    (sound committerQueries proverQueries State committer committerBound
      (fun state => (prover state).bind fun reply =>
        .done (reply.1, reply.2.1, ((Classical.arbitrary Label), reply.2.2)))
      fun state => queryBound_map _ _ _ (proverBound state))
  refine congrArg committer.withQueryLog.bind (funext fun made => ?_)
  obtain ⟨⟨commitment, state⟩, queryLog⟩ := made
  exact (RandomizedAlgorithm.bind_map_bind
    (fun reply : List Token × List Token × system.Proof =>
      (reply.1, reply.2.1, ((Classical.arbitrary Label), reply.2.2)))
    (fun reply : List Token × List Token × Label × system.Proof =>
      (system.verify commitment reply.1 reply.2.1 reply.2.2.2).toRandomized.bind fun accepted =>
        .done (extractor commitment queryLog, reply.1, reply.2.1, accepted))
    (prover state)).symm

theorem soundForWith_labelled_iff [Nonempty Label]
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞) :
    SoundForWith (labelled system label) extractor claim ε ↔
      SoundForWith system extractor claim ε :=
  ⟨soundForWith_of_labelled system label extractor claim ε,
    soundForWith_labelled system label extractor claim ε⟩

/-! ## Sound -/

theorem sound_labelled (ε : ℕ → ℝ≥0∞) (sound : Sound system ε) :
    Sound (labelled system label) ε :=
  let ⟨extractor, h⟩ := (sound_iff_soundFor system ε).1 sound
  (sound_iff_soundFor (labelled system label) ε).2
    ⟨extractor, soundForWith_labelled system label extractor system.IsModelOutput ε h⟩

theorem sound_labelled_iff [Nonempty Label] (ε : ℕ → ℝ≥0∞) :
    Sound (labelled system label) ε ↔ Sound system ε :=
  ⟨fun sound =>
      let ⟨extractor, h⟩ := (sound_iff_soundFor (labelled system label) ε).1 sound
      (sound_iff_soundFor system ε).2
        ⟨extractor, soundForWith_of_labelled system label extractor system.IsModelOutput ε h⟩,
    sound_labelled system label ε⟩

/-! ## Binding and extraction: they read no proof -/

theorem bindsWith_labelled_iff (extractor : Commitment → QueryLog → Option system.Weights)
    (ε : ℕ → ℝ≥0∞) :
    BindsWith (labelled system label) extractor ε ↔ BindsWith system extractor ε := Iff.rfl

theorem extractsCommittedWeights_labelled_iff
    (extractor : Commitment → QueryLog → Option system.Weights) (α : ℝ≥0∞) :
    ExtractsCommittedWeights (labelled system label) extractor α ↔
      ExtractsCommittedWeights system extractor α := Iff.rfl

/-! ## SoundAndBinding -/

theorem soundAndBinding_labelled (ε : ℕ → ℝ≥0∞) (h : SoundAndBinding system ε) :
    SoundAndBinding (labelled system label) ε :=
  let ⟨extractor, sound, binds⟩ := (soundAndBinding_iff system ε).1 h
  (soundAndBinding_iff (labelled system label) ε).2
    ⟨extractor, soundForWith_labelled system label extractor system.IsModelOutput ε sound, binds⟩

theorem soundAndBinding_labelled_iff [Nonempty Label] (ε : ℕ → ℝ≥0∞) :
    SoundAndBinding (labelled system label) ε ↔ SoundAndBinding system ε :=
  ⟨fun h =>
      let ⟨extractor, sound, binds⟩ := (soundAndBinding_iff (labelled system label) ε).1 h
      (soundAndBinding_iff system ε).2
        ⟨extractor, soundForWith_of_labelled system label extractor system.IsModelOutput ε sound,
          binds⟩,
    soundAndBinding_labelled system label ε⟩

/-! ## SoundOpened -/

theorem soundOpened_labelled (ε : ℕ → ℝ≥0∞) (h : SoundOpened system ε) :
    SoundOpened (labelled system label) ε := by
  intro queries adversary bound
  refine le_of_eq_of_le (congrArg (fun experiment => Prob experiment _) ?_)
    (h queries
      (adversary.bind fun made =>
        .done (made.1, made.2.1, (made.2.2.1, made.2.2.2.1, made.2.2.2.2.2)))
      (queryBound_map _ _ _ bound))
  exact (RandomizedAlgorithm.bind_map_bind
    (fun made : Commitment × (system.Weights × system.CommitmentRandomness) ×
        (List Token × List Token × Label × system.Proof) =>
      (made.1, made.2.1, (made.2.2.1, made.2.2.2.1, made.2.2.2.2.2)))
    (fun made : Commitment × (system.Weights × system.CommitmentRandomness) ×
        (List Token × List Token × system.Proof) =>
      (system.commit made.2.1.1 made.2.1.2).toRandomized.bind fun recomputed =>
        (system.verify made.1 made.2.2.1 made.2.2.2.1 made.2.2.2.2).toRandomized.bind fun accepted =>
          .done (made.1, recomputed, made.2.1.1, made.2.2.1, made.2.2.2.1, accepted))
    adversary).symm

theorem soundOpened_of_labelled [Nonempty Label] (ε : ℕ → ℝ≥0∞)
    (h : SoundOpened (labelled system label) ε) : SoundOpened system ε := by
  intro queries adversary bound
  refine le_of_eq_of_le (congrArg (fun experiment => Prob experiment _) ?_)
    (h queries
      (adversary.bind fun made =>
        .done (made.1, made.2.1, (made.2.2.1, made.2.2.2.1, ((Classical.arbitrary Label), made.2.2.2.2))))
      (queryBound_map _ _ _ bound))
  exact (RandomizedAlgorithm.bind_map_bind
    (fun made : Commitment × (system.Weights × system.CommitmentRandomness) ×
        (List Token × List Token × system.Proof) =>
      (made.1, made.2.1, (made.2.2.1, made.2.2.2.1, ((Classical.arbitrary Label), made.2.2.2.2))))
    (fun made : Commitment × (system.Weights × system.CommitmentRandomness) ×
        (List Token × List Token × Label × system.Proof) =>
      (system.commit made.2.1.1 made.2.1.2).toRandomized.bind fun recomputed =>
        (system.verify made.1 made.2.2.1 made.2.2.2.1 made.2.2.2.2.2).toRandomized.bind
          fun accepted => .done (made.1, recomputed, made.2.1.1, made.2.2.1, made.2.2.2.1, accepted))
    adversary).symm

theorem soundOpened_labelled_iff [Nonempty Label] (ε : ℕ → ℝ≥0∞) :
    SoundOpened (labelled system label) ε ↔ SoundOpened system ε :=
  ⟨soundOpened_of_labelled system label ε, soundOpened_labelled system label ε⟩

/-! ## Why the directions back ask for a label -/

/-- Some result of an algorithm: at the hash answer of zeros and the draw 0 throughout. -/
def RandomizedAlgorithm.someResult {α : Type} : RandomizedAlgorithm α → α
  | .done result => result
  | .query _ next => (next fun _ => false).someResult
  | .sample _ next => (next 0).someResult

/-- **With no label the labelled system is sound at every error**: there is no proof, so no prover
ends. (A rule into an empty type exists only at a system with no weights.) So Sound of the labelled
system does not give Sound of the system unless the type of labels has a member. -/
theorem sound_labelled_of_no_label [IsEmpty Label] (ε : ℕ → ℝ≥0∞) :
    Sound (labelled system label) ε :=
  ⟨fun _ _ => none, fun _ _ _ committer _ prover _ =>
    isEmptyElim (prover committer.someResult.2).someResult.2.2.1⟩

end VerifiableInference

#print axioms VerifiableInference.sound_labelled_of_no_label
#print axioms VerifiableInference.RandomizedAlgorithm.bind_bind
#print axioms VerifiableInference.RandomizedAlgorithm.bind_map_bind
#print axioms VerifiableInference.isModelOutput_labelled
#print axioms VerifiableInference.soundForWith_labelled
#print axioms VerifiableInference.soundForWith_of_labelled
#print axioms VerifiableInference.soundForWith_labelled_iff
#print axioms VerifiableInference.sound_labelled
#print axioms VerifiableInference.sound_labelled_iff
#print axioms VerifiableInference.bindsWith_labelled_iff
#print axioms VerifiableInference.extractsCommittedWeights_labelled_iff
#print axioms VerifiableInference.soundAndBinding_labelled
#print axioms VerifiableInference.soundAndBinding_labelled_iff
#print axioms VerifiableInference.soundOpened_labelled
#print axioms VerifiableInference.soundOpened_of_labelled
#print axioms VerifiableInference.soundOpened_labelled_iff
