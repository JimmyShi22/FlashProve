-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Front/MeetsPolicyGuards.lean

Sanity theorems on the claim `MeetsPolicy` (Policy/Front/MeetsPolicy.lean), stated for all settings
and all weights, over the text of `IntegerTransformer.model` and `IntegerTransformer.trace`
(IntegerModel/Model.lean). Part 1: the gap. Part 2: the model's next token and `modelLogits`. Part
3: the edges of `HasScores`. Part 4: clauses (a) and (b) for any costs on a range of positions. Part
5: what the claim gives, what meets it, and where it is exact match, says nothing, or is met by
nothing.
Sources: part 4 has the arguments of `Inst.Model.exact_match` (Inst/Model/ProgramR.lean) and
`polOK_of_const` (Inst/Model/RequestGuards2.lean).

Limits: No theorem of this file speaks of a protocol, a commitment or a request; of the library's
relation on a request it names the gap alone (`Inst.Model.gapOf`). For the relation:
Policy/Front/TrueUnder.lean, Policy/Front/TrueUnderConverse.lean. The claim is not monotone in C
(`meetsPolicy_reads_policy`, Policy/Front/TrueUnder.lean). This file has no example. Those of
Policy/Front/TrueUnder.lean are at the all-zero weights, where a gap is 0 or 1 and comes from the
rule for ties: the size of a gap, and which context's logits meet which token, are seen by general
theorems alone (`logitGap_eq_choice`, `outputCost_eq_iff`, `meetsPolicy_exact_iff`).
-/
import Policy.Front.MeetsPolicy
import IntegerModel.Readable.Facts
import IntegerModel.Readable.Helpers
import IntegerModel.ReplyOnWindow

set_option autoImplicit false

/- No default table of scales is in sight in this file: the low-priority instance `Scl.ref`
(Inst/Model/Scl.lean) is switched off, so whatever takes an `Scl` has to say which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open VerifiableInference

/-! ## 1. The gap -/

/-- The three properties of `IntegerTransformer.firstArgmax_spec` (IntegerModel/Readable/Facts.lean)
fix the first arg-max. -/
theorem firstArgmax_unique (f : Nat → Int) {n a : Nat} (small : a < n) (h1 : ∀ v < n, f v ≤ f a)
    (h2 : ∀ v < a, f v < f a) : IntegerTransformer.firstArgmax f n = a := by
  rw [IntegerModel.Readable.firstArgmax_eq]
  exact IntegerModel.argTo_unique f (n - 1) a (by omega) (fun v hv => h1 v (by omega)) h2

/-- The gap of this folder is the gap of the library's relation on a request, at the array read as a
function. -/
theorem logitGap_eq_gapOf (vocabulary : Nat) (logits : IntegerTransformer.IntegerVector) (token : Token) :
    logitGap vocabulary logits token =
      Inst.Model.gapOf vocabulary (fun v => logits.entry v) token := by
  unfold logitGap Inst.Model.gapOf
  exact IntegerModel.Readable.maxUpTo_eq _ _

/-- The gap of a token of the vocabulary is at least 0. -/
theorem logitGap_nonneg {vocabulary : Nat} (logits : IntegerTransformer.IntegerVector) {token : Token}
    (small : token < vocabulary) : 0 ≤ logitGap vocabulary logits token := by
  rw [logitGap_eq_gapOf]
  exact Inst.Model.gapOf_nonneg _ _ small

/-- The gap of a token of the vocabulary is 0 exactly if no token has a larger logit and every
smaller token has a smaller logit. -/
theorem logitGap_eq_zero_iff {vocabulary : Nat} (logits : IntegerTransformer.IntegerVector) {token : Token}
    (small : token < vocabulary) :
    logitGap vocabulary logits token = 0 ↔
      (∀ other < vocabulary, logits.entry other ≤ logits.entry token) ∧
        ∀ other < token, logits.entry other < logits.entry token := by
  rw [logitGap_eq_gapOf]
  exact Inst.Model.gapOf_eq_zero_iff _ _ small

/-- The gap of a token of the vocabulary is 0 exactly if it is the first arg-max of the logits. -/
theorem logitGap_eq_zero_iff_firstArgmax {vocabulary : Nat} (logits : IntegerTransformer.IntegerVector)
    {token : Token} (small : token < vocabulary) :
    logitGap vocabulary logits token = 0 ↔
      IntegerTransformer.firstArgmax (fun v => logits.entry v) vocabulary = token := by
  rw [logitGap_eq_zero_iff logits small]
  constructor
  · rintro ⟨h1, h2⟩
    exact firstArgmax_unique (fun v => logits.entry v) small h1 h2
  · intro e
    obtain ⟨-, h1, h2⟩ := IntegerTransformer.firstArgmax_spec (fun v => logits.entry v) vocabulary
      (Nat.lt_of_le_of_lt (Nat.zero_le _) small)
    rw [e] at h1 h2
    exact ⟨h1, h2⟩

/-- The library's gap, by the first arg-max a of the logits: l[a] − l[w], and 1 more if a < w. -/
theorem gapOf_eq_choice (V : ℕ) (l : ℕ → ℤ) {w : ℕ} (hw : w < V) :
    Inst.Model.gapOf V l w =
      l (IntegerTransformer.firstArgmax l V) - l w +
        if IntegerTransformer.firstArgmax l V < w then 1 else 0 := by
  obtain ⟨ha, h1, h2⟩ :=
    IntegerTransformer.firstArgmax_spec l V (Nat.lt_of_le_of_lt (Nat.zero_le _) hw)
  generalize IntegerTransformer.firstArgmax l V = a at ha h1 h2 ⊢
  apply le_antisymm
  · obtain ⟨j, hj, e⟩ :=
      (Inst.Model.maxTo_spec (fun v => l v - l w + if v < w then 1 else 0) (V - 1)).2
    unfold Inst.Model.gapOf
    rw [← e]
    show l j - l w + (if j < w then 1 else 0) ≤ l a - l w + if a < w then 1 else 0
    have hja : l j ≤ l a := h1 j (by omega)
    by_cases hlt : l j < l a
    · split <;> split <;> omega
    · have haj : a ≤ j := by
        by_contra hc
        exact hlt (h2 j (not_le.1 hc))
      split <;> split <;> omega
  · exact Inst.Model.le_gapOf V l (w := w) ha

/-- The gap of a token of the vocabulary: how far its logit lies below the first choice's, and 1
more if the first choice is the smaller token. -/
theorem logitGap_eq_choice {vocabulary : Nat} (logits : IntegerTransformer.IntegerVector) {token : Token}
    (small : token < vocabulary) :
    logitGap vocabulary logits token =
      logits.entry (IntegerTransformer.firstArgmax (fun v => logits.entry v) vocabulary)
        - logits.entry token
        + if IntegerTransformer.firstArgmax (fun v => logits.entry v) vocabulary < token
          then 1 else 0 := by
  rw [logitGap_eq_gapOf]
  exact gapOf_eq_choice vocabulary (fun v => logits.entry v) small

/-! ## 2. The model's next token and the logits -/

/-- An entry of a mapped array, if the function sends the default value to the default value: a read
outside the array then gives the same on both sides. -/
theorem entry_map {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (g : α → β) (k : Nat)
    (atDefault : g default = default) : (a.map g).entry k = g (a.entry k) := by
  by_cases h : k < a.size
  · simp [Array.entry, Array.getD, h]
  · simp [Array.entry, Array.getD, h, atDefault]

/-- The first arg-max of a constant function is 0. -/
theorem firstArgmax_const (c : Int) : ∀ n, IntegerTransformer.firstArgmax (fun _ => c) n = 0
  | 0 => rfl
  | n + 1 => by
      show (if c < c then n else IntegerTransformer.firstArgmax (fun _ => c) n) = 0
      rw [if_neg (lt_irrefl c), firstArgmax_const c n]

/-- Every entry of the default vector, the empty one, reads as 0. -/
theorem entry_default (v : Nat) : (default : IntegerTransformer.IntegerVector).entry v = 0 := by
  show (#[] : Array Int).getD v default = 0
  simp

/-- At every position, inside the trace or not, the field `choices` is the first arg-max of the
field `logits`. -/
theorem choices_entry (s : IntegerTransformer.Settings) (tables : IntegerTransformer.Tables)
    (weights : IntegerTransformer.Weights) (prompt : Array Nat) (k : Nat) :
    (IntegerTransformer.trace s tables weights prompt).choices.entry k =
      IntegerTransformer.firstArgmax
        (fun v => ((IntegerTransformer.trace s tables weights prompt).logits.entry k).entry v)
        s.vocabulary := by
  show ((IntegerTransformer.trace s tables weights prompt).logits.map fun lam =>
      IntegerTransformer.firstArgmax (fun v => lam.entry v) s.vocabulary).entry k = _
  refine entry_map _ _ k ?_
  show IntegerTransformer.firstArgmax
      (fun v => (default : IntegerTransformer.IntegerVector).entry v) s.vocabulary = 0
  rw [show (fun v => (default : IntegerTransformer.IntegerVector).entry v) = fun _ => (0 : Int) from
    funext entry_default]
  exact firstArgmax_const 0 _

/-- Where `IntegerTransformer.model` has a value: its two tests are passed, and the value is the
field `choices` of the trace at the last position. -/
theorem model_of_isSome (s : IntegerTransformer.Settings) (tables : IntegerTransformer.Tables)
    (weights : IntegerTransformer.Weights) (prompt : Array Nat)
    (h : (IntegerTransformer.model s tables weights prompt).isSome = true) :
    (IntegerTransformer.wellFormed s tables weights = true ∧
        IntegerTransformer.isPrompt s prompt = true) ∧
      IntegerTransformer.model s tables weights prompt =
        some ((IntegerTransformer.trace s tables weights prompt).choices.entry
          (prompt.size - 1)) := by
  unfold IntegerTransformer.model at h ⊢
  by_cases hc : (IntegerTransformer.wellFormed s tables weights &&
      IntegerTransformer.isPrompt s prompt) = true
  · rw [if_pos hc] at h ⊢
    have hc' := hc
    rw [Bool.and_eq_true] at hc'
    by_cases ha : IntegerTransformer.allConditionsHold s
        (IntegerTransformer.trace s tables weights prompt) = true
    · exact ⟨hc', if_pos ha⟩
    · have h' : (if IntegerTransformer.allConditionsHold s
            (IntegerTransformer.trace s tables weights prompt) = true then
          some ((IntegerTransformer.trace s tables weights prompt).choices.entry
            (prompt.size - 1))
          else none).isSome = true := h
      rw [if_neg ha] at h'
      exact absurd h' (by simp)
  · rw [if_neg hc] at h
    exact absurd h (by simp)

/-- Where the model has a value: there are 1 to `positions` tokens, all in the vocabulary, and the
vocabulary is not empty. -/
theorem isPrompt_of_isSome {settings : IntegerTransformer.Settings}
    {weights : ModelWeights settings} {tokens : List Token}
    (h : (modelNextToken settings weights tokens).isSome = true) :
    0 < tokens.length ∧ tokens.length ≤ settings.positions ∧
      (∀ token ∈ tokens, token < settings.vocabulary) ∧ 0 < settings.vocabulary := by
  obtain ⟨⟨hw, hp⟩, -⟩ := model_of_isSome settings lookupTables weights.val tokens.toArray h
  unfold IntegerTransformer.isPrompt at hp
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    List.size_toArray] at hp
  obtain ⟨⟨p1, p2⟩, p3⟩ := hp
  simp only [IntegerTransformer.wellFormed, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, h6⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
            -⟩,
          -⟩,
        -⟩,
      -⟩ := hw
  refine ⟨p1, p2, fun token member => ?_, h6⟩
  have := Array.all_eq_true_iff_forall_mem.1 p3 token (by simpa using member)
  simpa using this

/-- Where the model has a value, it is the first arg-max of `modelLogits`: the logits that the claim
reads are those off which the model's next token is read. -/
theorem modelNextToken_eq_firstArgmax {settings : IntegerTransformer.Settings}
    (weights : ModelWeights settings) (tokens : List Token)
    (h : (modelNextToken settings weights tokens).isSome = true) :
    modelNextToken settings weights tokens = some (IntegerTransformer.firstArgmax
      (fun v => (modelLogits settings weights tokens).entry v) settings.vocabulary) := by
  have e := (model_of_isSome settings lookupTables weights.val tokens.toArray h).2
  rw [choices_entry, List.size_toArray] at e
  exact e

/-- "The model's next token after these tokens is this one" says: the model has a value, the token
is in the vocabulary, and its gap is 0. -/
theorem modelNextToken_eq_some_iff {settings : IntegerTransformer.Settings}
    (weights : ModelWeights settings) (tokens : List Token) (token : Token) :
    modelNextToken settings weights tokens = some token ↔
      (modelNextToken settings weights tokens).isSome = true ∧ token < settings.vocabulary ∧
        logitGap settings.vocabulary (modelLogits settings weights tokens) token = 0 := by
  constructor
  · intro h
    have hs : (modelNextToken settings weights tokens).isSome = true := by rw [h]; rfl
    have e : IntegerTransformer.firstArgmax
        (fun v => (modelLogits settings weights tokens).entry v) settings.vocabulary = token :=
      Option.some.inj ((modelNextToken_eq_firstArgmax weights tokens hs).symm.trans h)
    have small : token < settings.vocabulary := by
      rw [← e]
      exact (IntegerTransformer.firstArgmax_spec _ _ (isPrompt_of_isSome hs).2.2.2).1
    exact ⟨hs, small, (logitGap_eq_zero_iff_firstArgmax _ small).2 e⟩
  · rintro ⟨hs, small, hg⟩
    rw [modelNextToken_eq_firstArgmax weights tokens hs,
      (logitGap_eq_zero_iff_firstArgmax _ small).1 hg]

/-! ## 3. The edges -/

/-- Three clauses of `HasScores` carry the others: a non-empty output of tokens of the vocabulary,
on each of whose contexts the model has a value. -/
theorem hasScores_iff {settings : IntegerTransformer.Settings} (weights : ModelWeights settings)
    (prompt output : List Token) :
    HasScores settings weights prompt output ↔
      output ≠ [] ∧ (∀ token ∈ output, token < settings.vocabulary) ∧
        ∀ position < output.length,
          (modelNextToken settings weights (prompt ++ output.take position)).isSome = true := by
  constructor
  · intro h
    exact ⟨h.outputNonempty, fun token member => h.inVocabulary token
      (List.mem_append_right _ member), h.defined⟩
  · rintro ⟨nonempty, small, defined⟩
    have positive : 0 < output.length := List.length_pos_iff.2 nonempty
    have first := isPrompt_of_isSome (defined 0 positive)
    rw [List.take_zero, List.append_nil] at first
    have last := (isPrompt_of_isSome (defined (output.length - 1) (by omega))).2.1
    rw [List.length_append, List.length_take] at last
    exact ⟨List.length_pos_iff.1 first.1, nonempty, by omega,
      fun token member => (List.mem_append.1 member).elim (first.2.2.1 token) (small token),
      defined⟩

/-- No empty output meets a policy. (`IsModelOutput`, VerifiableInference/Statements.lean, is true
of every empty output, by its definition.) -/
theorem not_meetsPolicy_nil {settings : IntegerTransformer.Settings} (policy : Inst.Model.AcceptancePolicy)
    (weights : ModelWeights settings) (prompt : List Token) :
    ¬ MeetsPolicy settings policy weights prompt [] :=
  fun h => h.outputNonempty rfl

/-- A non-empty output each of whose tokens is the model's next token has scores. -/
theorem hasScores_of_isModelOutput {settings : IntegerTransformer.Settings}
    {weights : ModelWeights settings} {prompt output : List Token} (nonempty : output ≠ [])
    (isOutput : ∀ position (h : position < output.length),
      modelNextToken settings weights (prompt ++ output.take position) = some output[position]) :
    HasScores settings weights prompt output :=
  (hasScores_iff weights prompt output).2 ⟨nonempty,
    fun token member => by
      obtain ⟨position, hp, rfl⟩ := List.getElem_of_mem member
      exact ((modelNextToken_eq_some_iff weights _ _).1 (isOutput position hp)).2.1,
    fun position hp => by rw [isOutput position hp]; rfl⟩

/-- An output token of the vocabulary costs at least 2^8. -/
theorem outputCost_ge {settings : IntegerTransformer.Settings} (weights : ModelWeights settings)
    (prompt : List Token) {output : List Token}
    (small : ∀ token ∈ output, token < settings.vocabulary) {position : Nat}
    (h : position < output.length) :
    (2 : Int) ^ 8 ≤ outputCost settings weights prompt output position := by
  unfold outputCost tokenCost
  rw [List.getD_eq_getElem _ _ h]
  have := logitGap_nonneg (modelLogits settings weights (prompt ++ output.take position))
    (small _ (List.getElem_mem h))
  omega

/-- Where the model has a value on its context, an output token of the vocabulary costs 2^8 exactly
if it is the model's next token. -/
theorem outputCost_eq_iff {settings : IntegerTransformer.Settings}
    (weights : ModelWeights settings) (prompt : List Token) {output : List Token}
    (small : ∀ token ∈ output, token < settings.vocabulary) {position : Nat}
    (h : position < output.length)
    (defined : (modelNextToken settings weights (prompt ++ output.take position)).isSome = true) :
    outputCost settings weights prompt output position = 2 ^ 8 ↔
      modelNextToken settings weights (prompt ++ output.take position) = some output[position] := by
  unfold outputCost tokenCost
  rw [List.getD_eq_getElem _ _ h, modelNextToken_eq_some_iff]
  constructor
  · intro e
    exact ⟨defined, small _ (List.getElem_mem h), by omega⟩
  · rintro ⟨-, -, e⟩
    rw [e, zero_add]

/-! ## 4. Clauses (a) and (b), for any costs on the positions below n -/

section Range
variable {n : ℕ} {cost : ℕ → ℤ} {policy : Inst.Model.AcceptancePolicy}

/-- If every cost is at least 2^8, theta = 2^8, and cap = 0 or 2^8 < C, then (a) and (b) force every
cost to be 2^8. (The argument of `Inst.Model.exact_match`, Inst/Model/ProgramR.lean.) -/
theorem cost_eq_of_exactKind (low : ∀ j < n, (2 : ℤ) ^ 8 ≤ cost j) (mean : policy.theta = 2 ^ 8)
    (limit : policy.cap = 0 ∨ 2 ^ 8 < policy.C)
    (a : ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ))
    (b : ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap) :
    ∀ j < n, cost j = 2 ^ 8 := by
  have hle : policy.cap = 0 → ∀ j ∈ Finset.range n, cost j ≤ policy.C := by
    intro h0 j hj
    by_contra hlt
    have hmem : j ∈ (Finset.range n).filter (fun j => (policy.C : ℤ) < cost j) :=
      Finset.mem_filter.2 ⟨hj, not_le.1 hlt⟩
    have h1 := Finset.card_pos.2 ⟨j, hmem⟩
    omega
  have hm : ∀ j ∈ Finset.range n, (2 : ℤ) ^ 8 ≤ min (cost j) policy.C := by
    intro j hj
    have hc8 := low j (Finset.mem_range.1 hj)
    rcases limit with h0 | h1
    · rw [min_eq_left (hle h0 j hj)]
      exact hc8
    · exact le_min hc8 (by exact_mod_cast le_of_lt h1)
  have hs : ∑ j ∈ Finset.range n, (min (cost j) (policy.C : ℤ) - 2 ^ 8) ≤ 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [mean] at a
    push_cast at a
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j hj => sub_nonneg.2 (hm j hj)).1
    (le_antisymm hs (Finset.sum_nonneg fun j hj => sub_nonneg.2 (hm j hj)))
  intro j hj
  have hj' := Finset.mem_range.2 hj
  have e : min (cost j) (policy.C : ℤ) = 2 ^ 8 := by
    have := hz j hj'
    omega
  rcases limit with h0 | h1
  · rwa [min_eq_left (hle h0 j hj')] at e
  · rcases min_choice (cost j) (policy.C : ℤ) with h3 | h3
    · rwa [h3] at e
    · rw [h3] at e
      have h4 : (2 : ℤ) ^ 8 < policy.C := by exact_mod_cast h1
      omega

/-- If all costs are one number k ≤ C, theta, then (a) and (b) hold. (The argument of
`Inst.Model.RequestGuards2.polOK_of_const`, Inst/Model/RequestGuards2.lean.) -/
theorem clauses_of_const {k : ℤ} (hk : ∀ j < n, cost j = k) (clip : k ≤ policy.C)
    (mean : k ≤ policy.theta) :
    ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ∧
      ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap := by
  constructor
  · have hs : ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) = ∑ _j ∈ Finset.range n, k :=
      Finset.sum_congr rfl fun j hj => by rw [hk j (Finset.mem_range.1 hj), min_eq_left clip]
    rw [hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm (n : ℤ) k]
    exact mul_le_mul_of_nonneg_right mean (Int.natCast_nonneg _)
  · have hf : ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j) = ∅ :=
      Finset.filter_false_of_mem fun j hj => by
        rw [hk j (Finset.mem_range.1 hj)]
        exact not_lt.2 clip
    rw [hf]
    exact Nat.zero_le _

/-- With C ≤ theta and n ≤ cap, (a) and (b) hold whatever the costs are. -/
theorem clauses_of_clip_le_mean (clip : policy.C ≤ policy.theta) (limit : n ≤ policy.cap) :
    ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ∧
      ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap := by
  constructor
  · calc ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ)
        ≤ ∑ _j ∈ Finset.range n, (policy.C : ℤ) :=
          Finset.sum_le_sum fun j _ => min_le_right _ _
      _ = (policy.C : ℤ) * (n : ℤ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
      _ ≤ (policy.theta : ℤ) * (n : ℤ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast clip) (Int.natCast_nonneg _)
  · exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range]; exact limit)

end Range

/-! ## 5. The claim -/

section Claim
variable {settings : IntegerTransformer.Settings}

/-- The model's own output, if it is not empty, meets every policy with 2^8 ≤ theta and 2^8 ≤ C. -/
theorem meetsPolicy_of_isModelOutput {policy : Inst.Model.AcceptancePolicy} (mean : 2 ^ 8 ≤ policy.theta)
    (clip : 2 ^ 8 ≤ policy.C) {weights : ModelWeights settings} {prompt output : List Token}
    (nonempty : output ≠ [])
    (isOutput : ∀ position (h : position < output.length),
      modelNextToken settings weights (prompt ++ output.take position) = some output[position]) :
    MeetsPolicy settings policy weights prompt output := by
  have scores := hasScores_of_isModelOutput nonempty isOutput
  have small : ∀ token ∈ output, token < settings.vocabulary := fun token member =>
    scores.inVocabulary token (List.mem_append_right _ member)
  have hk : ∀ j < countedTokens settings prompt output,
      outputCost settings weights prompt output j = 2 ^ 8 := fun j hj =>
    have hj' : j < output.length := lt_of_lt_of_le hj (Nat.min_le_left _ _)
    (outputCost_eq_iff weights prompt small hj' (scores.defined j hj')).2 (isOutput j hj')
  obtain ⟨a, b⟩ := clauses_of_const (policy := policy) hk (by exact_mod_cast clip)
    (by exact_mod_cast mean)
  exact { toHasScores := scores, meanCost := a, aboveClip := b,
          afterFullWindow := fun position h _ => isOutput position h }

/-- At every policy with theta = 2^8 ≤ C and (cap = 0 or 2^8 < C) the claim is: the output is not
empty, and every output token is the model's next token after the prompt and the output tokens
before it. -/
theorem meetsPolicy_iff_of_exactKind {policy : Inst.Model.AcceptancePolicy} (mean : policy.theta = 2 ^ 8)
    (clip : 2 ^ 8 ≤ policy.C) (limit : policy.cap = 0 ∨ 2 ^ 8 < policy.C)
    (weights : ModelWeights settings) (prompt output : List Token) :
    MeetsPolicy settings policy weights prompt output ↔
      output ≠ [] ∧ ∀ position (h : position < output.length),
        modelNextToken settings weights (prompt ++ output.take position) =
          some output[position] := by
  constructor
  · intro h
    have small : ∀ token ∈ output, token < settings.vocabulary := fun token member =>
      h.inVocabulary token (List.mem_append_right _ member)
    refine ⟨h.outputNonempty, fun position hp => ?_⟩
    by_cases hc : position < countedTokens settings prompt output
    · exact (outputCost_eq_iff weights prompt small hp (h.defined position hp)).1
        (cost_eq_of_exactKind
          (fun j hj => outputCost_ge weights prompt small
            (lt_of_lt_of_le hj (Nat.min_le_left _ _)))
          mean limit h.meanCost h.aboveClip position hc)
    · refine h.afterFullWindow position hp ?_
      unfold countedTokens at hc
      omega
  · rintro ⟨nonempty, isOutput⟩
    exact meetsPolicy_of_isModelOutput (le_of_eq mean.symm) clip nonempty isOutput

/-- At the policy of exact match the claim is: the output is not empty, and the output tokens are
the model's (`ArgumentSystem.IsModelOutput`, VerifiableInference/Statements.lean, at a system whose
model is `modelNextToken settings`). -/
theorem meetsPolicy_exact_iff (weights : ModelWeights settings) (prompt output : List Token) :
    MeetsPolicy settings Inst.Model.AcceptancePolicy.exact weights prompt output ↔
      output ≠ [] ∧ ∀ position (h : position < output.length),
        modelNextToken settings weights (prompt ++ output.take position) =
          some output[position] :=
  meetsPolicy_iff_of_exactKind rfl (le_refl _) (Or.inl rfl) weights prompt output

/-- After a prompt that fills the window no output token is counted, and the claim is exact match,
whatever the policy. -/
theorem meetsPolicy_iff_of_fullPrompt (policy : Inst.Model.AcceptancePolicy) (weights : ModelWeights settings)
    (prompt output : List Token) (full : settings.positions ≤ prompt.length) :
    MeetsPolicy settings policy weights prompt output ↔
      output ≠ [] ∧ ∀ position (h : position < output.length),
        modelNextToken settings weights (prompt ++ output.take position) =
          some output[position] := by
  have noneCounted : countedTokens settings prompt output = 0 := by
    unfold countedTokens
    omega
  constructor
  · intro h
    exact ⟨h.outputNonempty, fun position hp => h.afterFullWindow position hp (by omega)⟩
  · rintro ⟨nonempty, isOutput⟩
    exact { toHasScores := hasScores_of_isModelOutput nonempty isOutput
            meanCost := by rw [noneCounted]; simp
            aboveClip := by rw [noneCounted]; simp
            afterFullWindow := fun position h _ => isOutput position h }

/-- A policy that is empty of content: with C ≤ theta and cap at least the number of counted tokens,
clauses (a) and (b) hold of every output that has scores. Clause (c) stays: a token that follows a
full window has to be the model's next token. -/
theorem meetsPolicy_iff_of_clip_le_mean {policy : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token}
    (clip : policy.C ≤ policy.theta) (limit : countedTokens settings prompt output ≤ policy.cap) :
    MeetsPolicy settings policy weights prompt output ↔
      HasScores settings weights prompt output ∧
        ∀ position (h : position < output.length), settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position] := by
  constructor
  · intro h
    exact ⟨h.toHasScores, h.afterFullWindow⟩
  · rintro ⟨scores, after⟩
    obtain ⟨a, b⟩ := clauses_of_clip_le_mean
      (cost := outputCost settings weights prompt output) clip limit
    exact { toHasScores := scores, meanCost := a, aboveClip := b, afterFullWindow := after }

/-- With theta < 2^8 ≤ C no output with a counted token meets the policy: every counted token costs
at least 2^8. -/
theorem not_meetsPolicy_of_mean_lt {policy : Inst.Model.AcceptancePolicy} (mean : policy.theta < 2 ^ 8)
    (clip : 2 ^ 8 ≤ policy.C) {weights : ModelWeights settings} {prompt output : List Token}
    (counted : 0 < countedTokens settings prompt output) :
    ¬ MeetsPolicy settings policy weights prompt output := by
  intro h
  have small : ∀ token ∈ output, token < settings.vocabulary := fun token member =>
    h.inVocabulary token (List.mem_append_right _ member)
  have low : ∑ _j ∈ Finset.range (countedTokens settings prompt output), (2 : ℤ) ^ 8 ≤
      ∑ position ∈ Finset.range (countedTokens settings prompt output),
        min (outputCost settings weights prompt output position) (policy.C : ℤ) :=
    Finset.sum_le_sum fun j hj => le_min
      (outputCost_ge weights prompt small
        (lt_of_lt_of_le (Finset.mem_range.1 hj) (Nat.min_le_left _ _)))
      (by exact_mod_cast clip)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at low
  have a := low.trans h.meanCost
  have hθ : (policy.theta : ℤ) < 2 ^ 8 := by exact_mod_cast mean
  have hn : (0 : ℤ) < (countedTokens settings prompt output : ℤ) := by exact_mod_cast counted
  nlinarith [mul_pos (sub_pos.2 hθ) hn]

/-- What the claim gives: a count of costly tokens. For every number c ≤ C: the number of counted
tokens that cost at least c, times (c − 2^8), is at most the number of counted tokens times
(theta − 2^8). So, for 2^8 < c ≤ C, of n counted tokens at most n (theta − 2^8) / (c − 2^8) have a
gap of c − 2^8 or more. At c = C it is the inequality `room` of `meetsPolicy_of_few_costly`. Here it
follows from the claim; there, with `few`, it is enough for that many tokens to be any tokens of the
vocabulary. A token above the clip enters clause (a) as C and clause (b) as one, whatever its
cost. -/
theorem few_costly_of_meetsPolicy {policy : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings}
    {prompt output : List Token} (h : MeetsPolicy settings policy weights prompt output) {c : ℤ}
    (clip : c ≤ policy.C) :
    (((Finset.range (countedTokens settings prompt output)).filter fun position =>
        c ≤ outputCost settings weights prompt output position).card : ℤ) * (c - 2 ^ 8) ≤
      (countedTokens settings prompt output : ℤ) * ((policy.theta : ℤ) - 2 ^ 8) := by
  have small : ∀ token ∈ output, token < settings.vocabulary := fun token member =>
    h.inVocabulary token (List.mem_append_right _ member)
  have step : ∀ j ∈ Finset.range (countedTokens settings prompt output),
      (if c ≤ outputCost settings weights prompt output j then c - 2 ^ 8 else 0) ≤
        min (outputCost settings weights prompt output j) (policy.C : ℤ) - 2 ^ 8 := by
    intro j hj
    have low := outputCost_ge weights prompt small
      (lt_of_lt_of_le (Finset.mem_range.1 hj) (Nat.min_le_left _ _))
    by_cases hc : c ≤ outputCost settings weights prompt output j
    · rw [if_pos hc]
      have := le_min hc clip
      linarith
    · rw [if_neg hc, min_eq_left (le_trans (le_of_lt (not_le.1 hc)) clip)]
      linarith
  have sums := Finset.sum_le_sum step
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at sums
  have a := h.meanCost
  linarith

/-- With cap = 0 the claim does bound each counted token: none costs more than C. -/
theorem outputCost_le_clip_of_cap_zero {policy : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token}
    (h : MeetsPolicy settings policy weights prompt output) (limit : policy.cap = 0) :
    ∀ position < countedTokens settings prompt output,
      outputCost settings weights prompt output position ≤ (policy.C : ℤ) := by
  intro position hp
  by_contra above
  have member : position ∈ (Finset.range (countedTokens settings prompt output)).filter
      (fun position => (policy.C : ℤ) < outputCost settings weights prompt output position) :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 hp, not_le.1 above⟩
  have positive := Finset.card_pos.2 ⟨position, member⟩
  have b := h.aboveClip
  omega

/-- How many tokens can be any tokens of the vocabulary. Let 2^8 ≤ C, and let the output have scores
and meet clause (c). Let `costly` be a set of positions with at most cap members and with
(its number) (C − 2^8) ≤ (the number of counted tokens) (theta − 2^8). If every counted token
outside `costly` is the model's next token, the output meets the policy: of the tokens at the
positions of `costly` nothing is asked but what `HasScores` asks of every token. -/
theorem meetsPolicy_of_few_costly {policy : Inst.Model.AcceptancePolicy} (clip : 2 ^ 8 ≤ policy.C)
    {weights : ModelWeights settings} {prompt output : List Token}
    (scores : HasScores settings weights prompt output)
    (after : ∀ position (h : position < output.length),
      settings.positions ≤ prompt.length + position →
        modelNextToken settings weights (prompt ++ output.take position) = some output[position])
    (costly : Finset ℕ) (few : costly.card ≤ policy.cap)
    (room : (costly.card : ℤ) * ((policy.C : ℤ) - 2 ^ 8) ≤
      (countedTokens settings prompt output : ℤ) * ((policy.theta : ℤ) - 2 ^ 8))
    (others : ∀ position (h : position < output.length),
      position < countedTokens settings prompt output → position ∉ costly →
        modelNextToken settings weights (prompt ++ output.take position) =
          some output[position]) :
    MeetsPolicy settings policy weights prompt output := by
  have small : ∀ token ∈ output, token < settings.vocabulary := fun token member =>
    scores.inVocabulary token (List.mem_append_right _ member)
  have hC : (0 : ℤ) ≤ (policy.C : ℤ) - 2 ^ 8 := by
    have : (2 : ℤ) ^ 8 ≤ (policy.C : ℤ) := by exact_mod_cast clip
    linarith
  have cheap : ∀ j ∈ Finset.range (countedTokens settings prompt output), j ∉ costly →
      outputCost settings weights prompt output j = 2 ^ 8 := fun j hj hd =>
    have hj' : j < countedTokens settings prompt output := Finset.mem_range.1 hj
    have hj'' : j < output.length := lt_of_lt_of_le hj' (Nat.min_le_left _ _)
    (outputCost_eq_iff weights prompt small hj'' (scores.defined j hj'')).2 (others j hj'' hj' hd)
  have inCostly : ((Finset.range (countedTokens settings prompt output)).filter
      fun j => j ∈ costly).card ≤ costly.card :=
    Finset.card_le_card fun j hj => (Finset.mem_filter.1 hj).2
  refine { toHasScores := scores, meanCost := ?_, aboveClip := ?_, afterFullWindow := after }
  · calc ∑ position ∈ Finset.range (countedTokens settings prompt output),
          min (outputCost settings weights prompt output position) (policy.C : ℤ)
        ≤ ∑ position ∈ Finset.range (countedTokens settings prompt output),
            ((2 : ℤ) ^ 8 + if position ∈ costly then (policy.C : ℤ) - 2 ^ 8 else 0) := by
          refine Finset.sum_le_sum fun j hj => ?_
          by_cases hd : j ∈ costly
          · rw [if_pos hd]
            have := min_le_right (outputCost settings weights prompt output j) (policy.C : ℤ)
            linarith
          · rw [if_neg hd, cheap j hj hd, add_zero]
            exact min_le_left _ _
      _ = (countedTokens settings prompt output : ℤ) * 2 ^ 8 +
            (((Finset.range (countedTokens settings prompt output)).filter
              fun j => j ∈ costly).card : ℤ) * ((policy.C : ℤ) - 2 ^ 8) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (countedTokens settings prompt output : ℤ) * 2 ^ 8 +
            (costly.card : ℤ) * ((policy.C : ℤ) - 2 ^ 8) := by
          have : (((Finset.range (countedTokens settings prompt output)).filter
              fun j => j ∈ costly).card : ℤ) ≤ (costly.card : ℤ) := by exact_mod_cast inCostly
          have := mul_le_mul_of_nonneg_right this hC
          linarith
      _ ≤ (policy.theta : ℤ) * (countedTokens settings prompt output : ℤ) := by
          linarith
  · refine le_trans (Finset.card_le_card fun j hj => ?_) (inCostly.trans few)
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    refine Finset.mem_filter.2 ⟨hj1, ?_⟩
    by_contra hd
    rw [cheap j hj1 hd] at hj2
    linarith

/-- The claim is monotone in theta and in cap, at one clip. -/
theorem MeetsPolicy.mono {policy policy' : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings}
    {prompt output : List Token} (clip : policy.C = policy'.C)
    (mean : policy.theta ≤ policy'.theta) (limit : policy.cap ≤ policy'.cap)
    (h : MeetsPolicy settings policy weights prompt output) :
    MeetsPolicy settings policy' weights prompt output :=
  { toHasScores := h.toHasScores
    meanCost := by
      rw [← clip]
      exact h.meanCost.trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast mean) (Int.natCast_nonneg _))
    aboveClip := by
      rw [← clip]
      exact h.aboveClip.trans limit
    afterFullWindow := h.afterFullWindow }

end Claim

end Policy

#print axioms Policy.firstArgmax_unique
#print axioms Policy.logitGap_eq_gapOf
#print axioms Policy.logitGap_nonneg
#print axioms Policy.logitGap_eq_zero_iff
#print axioms Policy.logitGap_eq_zero_iff_firstArgmax
#print axioms Policy.gapOf_eq_choice
#print axioms Policy.logitGap_eq_choice
#print axioms Policy.entry_map
#print axioms Policy.firstArgmax_const
#print axioms Policy.entry_default
#print axioms Policy.choices_entry
#print axioms Policy.model_of_isSome
#print axioms Policy.isPrompt_of_isSome
#print axioms Policy.modelNextToken_eq_firstArgmax
#print axioms Policy.modelNextToken_eq_some_iff
#print axioms Policy.hasScores_iff
#print axioms Policy.not_meetsPolicy_nil
#print axioms Policy.hasScores_of_isModelOutput
#print axioms Policy.outputCost_ge
#print axioms Policy.outputCost_eq_iff
#print axioms Policy.cost_eq_of_exactKind
#print axioms Policy.clauses_of_const
#print axioms Policy.clauses_of_clip_le_mean
#print axioms Policy.meetsPolicy_of_isModelOutput
#print axioms Policy.meetsPolicy_iff_of_exactKind
#print axioms Policy.meetsPolicy_exact_iff
#print axioms Policy.meetsPolicy_iff_of_fullPrompt
#print axioms Policy.meetsPolicy_iff_of_clip_le_mean
#print axioms Policy.not_meetsPolicy_of_mean_lt
#print axioms Policy.few_costly_of_meetsPolicy
#print axioms Policy.outputCost_le_clip_of_cap_zero
#print axioms Policy.meetsPolicy_of_few_costly
#print axioms Policy.MeetsPolicy.mono
