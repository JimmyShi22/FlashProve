-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/GreedyOutputExists.lean

Where no range condition ever fails, greedy decoding goes through, token by token.
- `modelNextToken_isSome_of_rangeConditionsNeverFail`: under `RangeConditionsNeverFail`, the model
  has a next token after every list of 1 to 1,024 tokens of the vocabulary, and that next token is
  of the vocabulary.
- `exists_greedyOutput`: under `RangeConditionsNeverFail`, for every prompt of at least one token of
  the vocabulary and every number of output tokens from 1 on, with at most 1,025 tokens together,
  there is an output of that length, of tokens of the vocabulary, each of which is the model's next
  token after the prompt and the output tokens before it.
- `greedyOutput_unique`: two outputs of one length, each token of which is the model's next token
  after the prompt and the output tokens before it, are equal. It has no hypothesis on the weights.
Limits: `RangeConditionsNeverFail` is a hypothesis, and the file says of no weights that they meet
it. It binds all arrays of tokens: it is a statement on the weights, not a test that can be run. The
last output token is never fed to the model, which is why 1,025 tokens together are allowed while
the model runs on at most 1,024. The file imports Lean's core and the model's own files.
-/
import VerifiableInference.ModelNeverFails

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer

/-- A list of 1 to 1,024 tokens of the vocabulary is an array of tokens that the model can run
on. -/
private theorem isPrompt_toArray (settings : Settings) (weights : ModelWeights settings)
    (tokens : List Nat) (nonempty : 0 < tokens.length) (fits : tokens.length ≤ 1024)
    (inVocabulary : ∀ token ∈ tokens, token < settings.vocabulary) :
    isPrompt settings tokens.toArray = true := by
  have positions := positions_of_modelWeights settings weights
  unfold isPrompt
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.size_toArray]; exact nonempty
  · rw [List.size_toArray, positions]; exact fits
  · rw [Array.all_eq_true]
    intro index inside
    simp only [List.getElem_toArray, decide_eq_true_eq]
    exact inVocabulary _ (List.getElem_mem _)

/-- **If no range condition ever fails, the model has a next token** after every list of 1 to 1,024
tokens of the vocabulary, and the next token is of the vocabulary. -/
theorem modelNextToken_isSome_of_rangeConditionsNeverFail (settings : Settings)
    (weights : ModelWeights settings) (never : RangeConditionsNeverFail settings weights)
    (tokens : List Nat) (nonempty : 0 < tokens.length) (fits : tokens.length ≤ 1024)
    (inVocabulary : ∀ token ∈ tokens, token < settings.vocabulary) :
    ∃ next, modelNextToken settings weights tokens = some next ∧ next < settings.vocabulary := by
  have valid := weights.property
  simp only [weightsAreValid, Bool.and_eq_true] at valid
  have runs := isPrompt_toArray settings weights tokens nonempty fits inVocabulary
  have size : 0 < tokens.toArray.size := by rw [List.size_toArray]; exact nonempty
  refine ⟨(trace settings lookupTables weights.val tokens.toArray).choices.entry
    (tokens.toArray.size - 1), ?_, ?_⟩
  · unfold modelNextToken
    exact (model_eq_some settings lookupTables weights.val _ _).mpr
      ⟨valid.1, runs, never _ runs, rfl⟩
  · exact (trace_shape settings lookupTables weights.val _ valid.1 runs).2.2.2.2.2.2.2 _
      (by omega)

/-- The greedy output of any length from 0 on: `exists_greedyOutput` without the hypothesis that
there is at least one output token. -/
theorem exists_greedyOutput_of_length (settings : Settings) (weights : ModelWeights settings)
    (never : RangeConditionsNeverFail settings weights) (prompt : List Nat) (count : Nat)
    (nonempty : prompt ≠ []) (inVocabulary : ∀ token ∈ prompt, token < settings.vocabulary)
    (fits : prompt.length + count ≤ 1025) :
    ∃ output : List Nat, output.length = count ∧
      (∀ token ∈ output, token < settings.vocabulary) ∧
      ∀ position (inOutput : position < output.length),
        modelNextToken settings weights (prompt ++ output.take position) =
          some output[position] := by
  induction count with
  | zero =>
    exact ⟨[], rfl, fun _ inEmpty => absurd inEmpty List.not_mem_nil,
      fun _ inOutput => absurd inOutput (Nat.not_lt_zero _)⟩
  | succ count step =>
    obtain ⟨output, length, tokens, greedy⟩ := step (by omega)
    have promptLength : 0 < prompt.length := List.length_pos_iff.mpr nonempty
    obtain ⟨next, isNext, nextInVocabulary⟩ :=
      modelNextToken_isSome_of_rangeConditionsNeverFail settings weights never (prompt ++ output)
        (by rw [List.length_append]; omega) (by rw [List.length_append]; omega)
        (fun token inBoth => (List.mem_append.mp inBoth).elim (inVocabulary token) (tokens token))
    refine ⟨output ++ [next], ?_, ?_, ?_⟩
    · rw [List.length_append, length]; rfl
    · intro token inLonger
      rcases List.mem_append.mp inLonger with earlier | last
      · exact tokens token earlier
      · rw [List.mem_singleton.mp last]; exact nextInVocabulary
    · intro position inOutput
      rw [List.length_append, List.length_singleton] at inOutput
      by_cases earlier : position < output.length
      · rw [List.take_append_of_le_length (Nat.le_of_lt earlier),
          List.getElem_append_left earlier]
        exact greedy position earlier
      · have atEnd : position = output.length := by omega
        subst atEnd
        rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length,
          List.getElem_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        exact isNext

/-- **If no range condition ever fails, every prompt has its greedy output of every length.** The
prompt has at least one token, all its tokens are of the vocabulary, there is at least one output
token, and prompt and output together have at most 1,025 tokens. Each token of the output is the
model's next token after the prompt and the output tokens before it. The proof does not use that
there is at least one output token: see `exists_greedyOutput_of_length`. -/
theorem exists_greedyOutput (settings : Settings) (weights : ModelWeights settings)
    (never : RangeConditionsNeverFail settings weights) (prompt : List Nat) (count : Nat)
    (nonempty : prompt ≠ []) (inVocabulary : ∀ token ∈ prompt, token < settings.vocabulary)
    (_positive : 0 < count) (fits : prompt.length + count ≤ 1025) :
    ∃ output : List Nat, output.length = count ∧
      (∀ token ∈ output, token < settings.vocabulary) ∧
      ∀ position (inOutput : position < output.length),
        modelNextToken settings weights (prompt ++ output.take position) =
          some output[position] :=
  exists_greedyOutput_of_length settings weights never prompt count nonempty inVocabulary fits

/-- **A prompt has at most one greedy output of each length.** -/
theorem greedyOutput_unique (settings : Settings) (weights : ModelWeights settings)
    (prompt first second : List Nat) (sameLength : first.length = second.length)
    (firstIsGreedy : ∀ position (inOutput : position < first.length),
      modelNextToken settings weights (prompt ++ first.take position) = some first[position])
    (secondIsGreedy : ∀ position (inOutput : position < second.length),
      modelNextToken settings weights (prompt ++ second.take position) = some second[position]) :
    first = second := by
  have prefixes : ∀ count, count ≤ first.length → first.take count = second.take count := by
    intro count
    induction count with
    | zero => intro _; simp
    | succ count sameBefore =>
      intro within
      have inFirst : count < first.length := by omega
      have inSecond : count < second.length := by omega
      have same := sameBefore (by omega)
      have nextOfFirst := firstIsGreedy count inFirst
      rw [same] at nextOfFirst
      have sameToken : first[count] = second[count] :=
        Option.some.inj (nextOfFirst.symm.trans (secondIsGreedy count inSecond))
      rw [List.take_succ_eq_append_getElem inFirst, List.take_succ_eq_append_getElem inSecond,
        same, sameToken]
  have whole := prefixes first.length (Nat.le_refl _)
  rw [List.take_length] at whole
  rw [whole, sameLength, List.take_length]

end VerifiableInference

#print axioms VerifiableInference.exists_greedyOutput
#print axioms VerifiableInference.greedyOutput_unique
