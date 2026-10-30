-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/ModelOutput.lean: a true request (`Cm.PaperTrue`, Cm/RelTruePaper.lean; in words: the
opening comment of IntegerModel/TrueRequest.lean), for a prompt and output tokens given as lists.
`nextToken s w`: the next token after a list of numbers, by `IntegerTransformer.model`
(IntegerModel/Model.lean) at the arrays made from a table of scales s, from weights w and from the
library's five fixed tables.
`isModelOutput_of_isTrueRequest`: at a lawful table, if the request built from a prompt, output
tokens and a padding (VerifiableInference/RequestOfTokens.lean) is true, each output token is the
value of `nextToken` on the prompt and the output tokens before it.
`canServeModelOutput_iff`: at a lawful table, the request built without padding (the padding is
`[]`) exists and is true exactly if each output token is that value, every token is in the
vocabulary, the output is not empty, and `nextToken` has a value on the whole window of 1,024 tokens
(the first 1,024 tokens of the list that consists of the prompt, then the output tokens, then token
0 repeated). Part 1 has the steps for lists of tokens of the vocabulary, part 2 for lists of
numbers.
-/
import IntegerModel.TrueRequest
import IntegerModel.Window
import IntegerModel.Readable.AnyInput
import VerifiableInference.RequestOfTokens

set_option autoImplicit false

open Inst.Model
open VerifiableInference (vocabularyTokens vocabularyTokens_map_val map_val_of_vocabularyTokens
  exists_large_of_vocabularyTokens_none lt_of_vocabularyTokens requestOfTokens)

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace IntegerModel

/-! ## 1. Lists of tokens of the vocabulary -/

/-- "The reply is the model's" for the built request gives "the output tokens are the model's". -/
theorem isModelOutput_of_isReply {m : Committed} {x : Request} {prompt output padding : List Token}
    (hs : requestOf prompt output padding = some x) (h : IsReply m x) :
    IsModelOutput m prompt output := by
  have h2 := h.2
  rw [promptOf_requestOf hs, replyOf_requestOf hs] at h2
  have hl : x.e - x.r = output.length := by
    obtain ⟨-, hr, he, -⟩ := requestOf_some hs
    rw [hr, he]
    omega
  rw [hl] at h2
  exact greedy_positions (programNextToken m) output prompt h2

/-- The 1,024 tokens of the request that is built without padding: the first 1,024 tokens of the
list that consists of the prompt, then the output tokens, then token 0 repeated. With 1,025 tokens
in all, the last output token is outside it. -/
def windowOf (prompt output : List Token) : List Token :=
    (prompt ++ output ++ List.replicate 1024 tokenZero).take 1024

/- If f gives the tokens of `out` position by position, `greedyOutput` gives `out`. -/
theorem greedy_of_positions (f : List Token → Option Token) : ∀ (out ctx : List Token),
    (∀ (i : ℕ) (h : i < out.length), f (ctx ++ out.take i) = some out[i]) → greedyOutput f ctx
        out.length
    = some out
  | [], _, _ => by
      show greedyOutput f _ 0 = some []
      rw [greedyOutput]
  | y :: rest, ctx, h => by
      have h0 : f ctx = some y := by simpa using h 0 (Nat.succ_pos _)
      have ih := greedy_of_positions f rest (ctx ++ [y]) fun i hi =>
          by simpa [List.append_assoc] using h (i + 1) (Nat.succ_lt_succ hi)
      show greedyOutput f ctx (rest.length + 1) = some (y :: rest)
      rw [greedyOutput, h0]
      show (greedyOutput f (ctx ++ [y]) rest.length).map (y :: ·) = some (y :: rest)
      rw [ih]
      rfl

/- "The output tokens are the model's" gives "the reply is the model's" for the built request. -/
theorem isReply_of_isModelOutput {m : Committed} {x : Request} {prompt output padding : List Token}
    (hs : requestOf prompt output padding = some x) (h : IsModelOutput m prompt output) : IsReply
    m x := by
  obtain ⟨⟨h1, h2, h3⟩, hr, he, -⟩ := requestOf_some hs
  refine ⟨by omega, ?_⟩
  rw [promptOf_requestOf hs, replyOf_requestOf hs, show x.e - x.r = output.length by omega]
  exact greedy_of_positions (programNextToken m) output prompt h

/- The built request passes the test on a request's form (`requestWellFormed`). -/
theorem requestWellFormed_requestOf {x : Request} {prompt output padding : List Token}
    (hs : requestOf prompt output padding = some x) : requestWellFormed x = true := by
  obtain ⟨⟨h1, h2, h3⟩, hr, he, -⟩ := requestOf_some hs
  have hy : x.e < ppref.T → x.y.val = 0 := fun hlt => by
    unfold requestOf at hs
    rw [dif_pos ⟨h1, h2, h3⟩] at hs
    obtain rfl := Option.some.inj hs
    show ((prompt ++ output).getD ppref.T tokenZero).val = 0
    rw [List.getD_eq_default _ _ (by rw [List.length_append]; omega)]
    rfl
  have a1 : x.r < x.e := by omega
  have a2 : x.e ≤ ppref.T := by omega
  unfold requestWellFormed
  by_cases a3 : x.e < ppref.T
  · simp [a1, a2, a3, hy a3]
  · simp [a1, a2, a3]

/- `programNextToken` is defined only on 1 to 1,024 tokens. -/
theorem model_length {m : Committed} {ctx : List Token} {y : Token}
    (h : programNextToken m ctx = some y) : 0 <
    ctx.length ∧ ctx.length ≤ ppref.T := by
  unfold programNextToken at h
  split at h
  · rename_i hc
    exact ⟨hc.1, hc.2.1⟩
  · cases h

/-- A non-empty output that is the model's has a request, whatever the padding. So a non-empty
prompt and at most 1,025 tokens together follow from these two. -/
theorem requestOf_of_output {m : Committed} {prompt output : List Token} (padding : List Token)
    (hne : output ≠ []) (ho : IsModelOutput m prompt output) : ∃ x, requestOf prompt output
    padding = some x := by
  have hpos : 0 < output.length := List.length_pos_iff.2 hne
  have h0 := (model_length (ho 0 hpos)).1
  have h1 := (model_length (ho (output.length - 1) (by omega))).2
  rw [List.length_append, List.length_take] at h0 h1
  unfold requestOf
  rw [dif_pos ⟨by omega, hpos, by omega⟩]
  exact ⟨_, rfl⟩

/- Token j of the request that is built without padding. -/
theorem tok_requestOf {x : Request} {prompt output : List Token}
    (hs : requestOf prompt output [] = some x) (j : ℕ) (hj : j < ppref.T) : x.tok j =
    ((prompt ++ output).getD j tokenZero).val := by
  obtain ⟨hc, -, -, -⟩ := requestOf_some hs
  unfold requestOf at hs
  rw [dif_pos hc] at hs
  obtain rfl := Option.some.inj hs
  unfold Instance.tok
  rw [dif_pos hj]
  show ((prompt ++ output ++ []).getD j tokenZero).val = _
  rw [List.append_nil]

/-- Position j of a list followed by n copies of d. -/
theorem getElem_pad {α : Type} (l : List α) (d : α) (n j : ℕ)
    (h : j < (l ++ List.replicate n d).length) : (l ++ List.replicate n d)[j] = l.getD j d := by
  by_cases hl : j < l.length
  · rw [List.getElem_append_left hl, List.getD_eq_getElem _ _ hl]
  · rw [List.getElem_append_right (Nat.le_of_not_lt hl), List.getElem_replicate,
      List.getD_eq_default _ _ (Nat.le_of_not_lt hl)]

/- The 1,024 tokens of the request that is built without padding are `windowOf`. -/
theorem firstToks_requestOf {x : Request} {prompt output : List Token}
    (hs : requestOf prompt output [] = some x) : firstToks x 1024 = windowOf prompt output := by
  have hT : ppref.T = 1024 := by decide
  unfold firstToks windowOf
  refine List.ext_getElem
      (by
        rw [List.length_map, List.length_range, List.length_take, List.length_append,
          List.length_replicate]
        omega) fun j hj hj' => ?_
  have hj4 : j < 1024 := by rw [List.length_map, List.length_range] at hj; exact hj
  rw [List.getElem_map, List.getElem_range, List.getElem_take, getElem_pad]
  exact Fin.ext (tok_requestOf hs j (by rw [hT]; exact hj4))

/-- At a lawful table, if the request built from a prompt, output tokens and a padding is true, the
output tokens are the model's. -/
theorem isModelOutput_of_isTrueRequest_requestOf (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx)
    {x : Request} {prompt output padding : List Token}
    (built : requestOf prompt output padding = some x) (holds : Cm.PaperTrue s.kap s.nf i x) :
    IsModelOutput (committedOf s hs i) prompt output :=
  isModelOutput_of_isReply built ((isTrueRequest_iff_isReply s hs i x).1 holds).2.1

/-- At a lawful table, if the output is not empty and is the model's, and the model has a value on
the whole window, the request built without padding exists and is true. -/
theorem isTrueRequest_of_isModelOutput_requestOf (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx)
    {prompt output : List Token} (nonempty : output ≠ [])
    (isOutput : IsModelOutput (committedOf s hs i) prompt output)
    (runs : (programNextToken (committedOf s hs i) (windowOf prompt output)).isSome = true) :
    ∃ x, requestOf prompt output [] = some x ∧ Cm.PaperTrue s.kap s.nf i x := by
  obtain ⟨x, built⟩ := requestOf_of_output [] nonempty isOutput
  refine ⟨x, built, (isTrueRequest_iff_isReply s hs i x).2
    ⟨requestWellFormed_requestOf built, isReply_of_isModelOutput built isOutput, ?_⟩⟩
  rw [firstToks_requestOf built]
  exact runs

/-! ## 2. Lists of numbers -/

/-- The next token after `tokens`: `IntegerTransformer.model` (IntegerModel/Model.lean) at the
arrays made from a table of scales, from weights and from the library's five fixed tables
(IntegerModel/Readable/Exists.lean). It is greedy decoding of the integer program: the least token
with the largest logit. `none` if a token is outside the vocabulary, the list is empty or longer
than 1,024 tokens, or a range condition fails at some position of the list. At a lawful table these
are all the cases (`nextToken_eq_programNextToken`); at another table it is also `none` where the
arrays fail the test `IntegerTransformer.wellFormed`. -/
def nextToken (s : Cm.Scales) (w : Weights) (tokens : List ℕ) : Option ℕ :=
  IntegerTransformer.model (Readable.settingsArrays ppref ⟨s.w, s.nf, AcceptancePolicy.exact⟩)
    (Readable.tablesArrays ppref) (Readable.weightsArrays ppref w.val) tokens.toArray

/-- `nextToken` equals `programNextToken` on lists of tokens of the vocabulary and is `none` on
every other list, for every lawful table and all weights. -/
theorem nextToken_eq_programNextToken (s : Cm.Scales) (hs : s.Lawful) (w : Weights)
    (tokens : List ℕ) :
    nextToken s w tokens = (vocabularyTokens tokens).bind fun list =>
      (programNextToken ⟨⟨s.w, s.nf, AcceptancePolicy.exact⟩, w, hs.toPP⟩ list).map Fin.val := by
  cases h : vocabularyTokens tokens with
  | some list =>
      have e : list.map Fin.val = tokens := map_val_of_vocabularyTokens tokens list h
      show nextToken s w tokens = (programNextToken ⟨⟨s.w, s.nf, AcceptancePolicy.exact⟩, w, hs.toPP⟩ list).map
          Fin.val
      rw [← e]
      exact Readable.modelOf_eq ⟨⟨s.w, s.nf, AcceptancePolicy.exact⟩, w, hs.toPP⟩ list
  | none =>
      obtain ⟨position, hp, hb⟩ := exists_large_of_vocabularyTokens_none tokens h
      show nextToken s w tokens = none
      refine Readable.model_none_of_token _ _ _ _ fun a => hb ?_
      exact a position (by rw [List.size_toArray]; exact hp)

/-- The window, for tokens of the vocabulary written as numbers. -/
theorem zeroFilledWindow_map (prompt output : List Token) :
    zeroFilledWindow (prompt.map Fin.val) (output.map Fin.val) =
      (windowOf prompt output).map Fin.val := by
  unfold zeroFilledWindow windowOf
  rw [List.map_take, List.map_append, List.map_append, List.map_replicate]
  rfl

/-- At a lawful table, "the output tokens are the model's" for tokens of the vocabulary gives the
same for `nextToken` on these tokens written as numbers. -/
theorem nextToken_of_isModelOutput (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx)
    (prompt output : List Token) (h : IsModelOutput (committedOf s hs i) prompt output)
    (position : ℕ) (hp : position < (output.map Fin.val).length) :
    nextToken s i.index (prompt.map Fin.val ++ (output.map Fin.val).take position) =
      some (output.map Fin.val)[position] := by
  have hp' : position < output.length := by rw [List.length_map] at hp; exact hp
  rw [← List.map_take, ← List.map_append, nextToken_eq_programNextToken s hs,
      vocabularyTokens_map_val]
  show (programNextToken (committedOf s hs i) (prompt ++ output.take position)).map Fin.val = _
  rw [h position hp', List.getElem_map]
  rfl

/-- The converse of `nextToken_of_isModelOutput`. -/
theorem isModelOutput_of_nextToken (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx)
    (prompt output : List Token)
    (h : ∀ (position : ℕ) (hp : position < (output.map Fin.val).length),
      nextToken s i.index (prompt.map Fin.val ++ (output.map Fin.val).take position) =
        some (output.map Fin.val)[position]) :
    IsModelOutput (committedOf s hs i) prompt output := by
  intro position hp
  have hp' : position < (output.map Fin.val).length := by rw [List.length_map]; exact hp
  have h1 := h position hp'
  rw [← List.map_take, ← List.map_append, nextToken_eq_programNextToken s hs,
      vocabularyTokens_map_val,
    List.getElem_map] at h1
  have h2 : (programNextToken (committedOf s hs i) (prompt ++ output.take position)).map Fin.val =
      some (output[position]).val := h1
  obtain ⟨token, ht, hv⟩ := Option.map_eq_some_iff.1 h2
  rw [ht, Fin.ext hv]

/-- Numbers below the size of the vocabulary are tokens. -/
theorem vocabularyTokens_of_small (list : List ℕ) (h : ∀ token ∈ list, token < ppref.V) :
    ∃ tokens, vocabularyTokens list = some tokens := by
  cases e : vocabularyTokens list with
  | some tokens => exact ⟨tokens, rfl⟩
  | none =>
      obtain ⟨position, hp, hb⟩ := exists_large_of_vocabularyTokens_none list e
      exact absurd (h _ (List.getElem_mem hp)) hb

/-- Side conditions on a prompt and an output, at a table of scales and weights: every token is in
the vocabulary; the output is not empty; `nextToken` has a value on the zero-filled window
(IntegerModel/Window.lean). The last clause depends on the weights: a range condition of the integer
program can fail at a position after the output. `Cm.filler` (Cm/RelTrueExp.lean) shows that for a
window whose last token is 1; for a zero-filled window no example is proved. Alone these conditions
do not bound the lengths: an empty prompt can meet them. The name looks ahead to a completeness
theorem; no statement in this file speaks of a prover. -/
def CanServeAtIndex (s : Cm.Scales) (w : Weights) (prompt output : List ℕ) : Prop :=
  (∀ token ∈ prompt ++ output, token < ppref.V) ∧ output ≠ [] ∧
    (nextToken s w (zeroFilledWindow prompt output)).isSome = true

/-- `CanServeAtIndex`, and each output token is the value of `nextToken` on the prompt and the
output tokens before it. At a lawful table it holds exactly if the request built without padding
exists and is true (`canServeModelOutput_iff`); such a request exists only if the prompt is not
empty and prompt and output have at most 1,025 tokens together. -/
def CanServeModelOutput (s : Cm.Scales) (w : Weights) (prompt output : List ℕ) : Prop :=
  CanServeAtIndex s w prompt output ∧
    ∀ (position : ℕ) (h : position < output.length),
      nextToken s w (prompt ++ output.take position) = some output[position]

/-- At a lawful table, if the request built from a prompt, output tokens and a padding is true, each
output token is the value of `nextToken` on the prompt and the output tokens before it. -/
theorem isModelOutput_of_isTrueRequest (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx) {x : Request}
    {prompt output padding : List ℕ} (built : requestOfTokens (prompt, output) padding = some x)
    (holds : Cm.PaperTrue s.kap s.nf i x) (position : ℕ) (h : position < output.length) :
    nextToken s i.index (prompt ++ output.take position) = some output[position] := by
  obtain ⟨p, o, pad, hp, ho, -, hx⟩ := VerifiableInference.requestOfTokens_some built
  obtain rfl : p.map Fin.val = prompt := map_val_of_vocabularyTokens prompt p hp
  obtain rfl : o.map Fin.val = output := map_val_of_vocabularyTokens output o ho
  exact nextToken_of_isModelOutput s hs i p o
    (isModelOutput_of_isTrueRequest_requestOf s hs i hx holds) position h

/-- At a lawful table and under `CanServeAtIndex`, if each output token is the value of `nextToken`
on the prompt and the output tokens before it, the request built without padding exists and is true.
-/
theorem isTrueRequest_of_canServe (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx)
    {prompt output : List ℕ} (canServe : CanServeAtIndex s i.index prompt output)
    (isOutput : ∀ (position : ℕ) (h : position < output.length),
      nextToken s i.index (prompt ++ output.take position) = some output[position]) :
    ∃ x, requestOfTokens (prompt, output) [] = some x ∧ Cm.PaperTrue s.kap s.nf i x := by
  obtain ⟨small, nonempty, runs⟩ := canServe
  obtain ⟨p, hp⟩ := vocabularyTokens_of_small prompt fun token member =>
    small token (List.mem_append_left _ member)
  obtain ⟨o, ho⟩ := vocabularyTokens_of_small output fun token member =>
    small token (List.mem_append_right _ member)
  obtain rfl : p.map Fin.val = prompt := map_val_of_vocabularyTokens prompt p hp
  obtain rfl : o.map Fin.val = output := map_val_of_vocabularyTokens output o ho
  have nonempty' : o ≠ [] := fun e => nonempty (congrArg (List.map Fin.val) e)
  rw [zeroFilledWindow_map, nextToken_eq_programNextToken s hs, vocabularyTokens_map_val] at runs
  have runs' : ((programNextToken (committedOf s hs i) (windowOf p o)).map Fin.val).isSome = true :=
    runs
  rw [Option.isSome_map] at runs'
  obtain ⟨x, built, holds⟩ := isTrueRequest_of_isModelOutput_requestOf s hs i nonempty'
    (isModelOutput_of_nextToken s hs i p o isOutput) runs'
  exact ⟨x, (VerifiableInference.requestOfTokens_eq hp ho rfl).trans built, holds⟩

/-- The converse, at a lawful table: if the request built without padding is true,
`CanServeModelOutput` holds. -/
theorem canServeModelOutput_of_isTrueRequest (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx)
    {x : Request}
    {prompt output : List ℕ} (built : requestOfTokens (prompt, output) [] = some x)
    (holds : Cm.PaperTrue s.kap s.nf i x) : CanServeModelOutput s i.index prompt output := by
  obtain ⟨p, o, pad, hp, ho, hpad, hx⟩ := VerifiableInference.requestOfTokens_some built
  obtain rfl : [] = pad := Option.some.inj hpad
  have small : ∀ token ∈ prompt ++ output, token < ppref.V := fun token member =>
    (List.mem_append.1 member).elim (lt_of_vocabularyTokens hp token)
      (lt_of_vocabularyTokens ho token)
  refine ⟨⟨small, ?_, ?_⟩, isModelOutput_of_isTrueRequest s hs i built holds⟩
  · intro e
    have positive : 0 < o.length := (requestOf_some hx).1.2.1
    have length : o.length = output.length := by
      rw [← map_val_of_vocabularyTokens output o ho, List.length_map]
    rw [length, e] at positive
    exact Nat.lt_irrefl 0 positive
  · obtain rfl : p.map Fin.val = prompt := map_val_of_vocabularyTokens prompt p hp
    obtain rfl : o.map Fin.val = output := map_val_of_vocabularyTokens output o ho
    rw [zeroFilledWindow_map, nextToken_eq_programNextToken s hs, vocabularyTokens_map_val]
    show ((programNextToken (committedOf s hs i) (windowOf p o)).map Fin.val).isSome = true
    rw [Option.isSome_map, ← firstToks_requestOf hx]
    exact ((isTrueRequest_iff_isReply s hs i x).1 holds).2.2

/-- At a lawful table, `CanServeModelOutput` holds exactly if the request built without padding
exists and is true. -/
theorem canServeModelOutput_iff (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx)
    (prompt output : List ℕ) :
    CanServeModelOutput s i.index prompt output ↔
      ∃ x, requestOfTokens (prompt, output) [] = some x ∧ Cm.PaperTrue s.kap s.nf i x :=
  ⟨fun canServe => isTrueRequest_of_canServe s hs i canServe.1 canServe.2,
    fun ⟨_, built, holds⟩ => canServeModelOutput_of_isTrueRequest s hs i built holds⟩

/-- `CanServeModelOutput` is met: at every lawful table and the all-zero weights, by the prompt of
one token 0 and the output of one token 0. At these weights every logit is 0
(Inst/Model/ProgramRGuards.lean: `lg_zero`), so the example does not show that weights or earlier
tokens are read; for that see `Cm.true_layer` and `Cm.true_earlier` (Cm/RelTrue.lean), and, for the
model as a function on arrays, `modelNextToken_reads_layer` and `modelNextToken_reads_earlier_token`
(VerifiableInference/ModelGuardsAtReference.lean). -/
theorem canServeModelOutput_atZeroWeights (s : Cm.Scales) (hs : s.Lawful) :
    CanServeModelOutput s ScalesSanity.iZero [0] [0] := by
  obtain ⟨x, hx⟩ : ∃ x, requestOf [tokenZero] [tokenZero] [] = some x := by
    unfold requestOf
    rw [dif_pos ⟨by decide, by decide, by decide⟩]
    exact ⟨_, rfl⟩
  obtain ⟨-, hr, he, ht⟩ := requestOf_some hx
  have hr0 : x.r = 0 := hr
  have he1 : x.e = 1 := he
  have checked : ∀ t, x.r ≤ t → t < x.e → x.w t = 0 := by
    intro t _ h2
    obtain rfl : t = 0 := by omega
    show x.tok 1 = 0
    rw [ht 1 (by decide)]
    rfl
  have holds : Cm.PaperTrue s.kap s.nf (Cm.Idx.ofIndex ScalesSanity.iZero) x :=
    (Cm.paper_iff _ _ _ _).1 ((Cm.trueAt_ofIndex _ _ _ _).2 (ProgramRGuards.zero_true_of hs.toPP x
      (form_of_requestWellFormed (requestWellFormed_requestOf hx)) checked))
  have zero : vocabularyTokens [0] = some [tokenZero] := vocabularyTokens_map_val [tokenZero]
  have built : requestOfTokens ([0], [0]) [] = some x :=
      (VerifiableInference.requestOfTokens_eq zero zero rfl).trans hx
  have result := canServeModelOutput_of_isTrueRequest s hs (Cm.Idx.ofIndex ScalesSanity.iZero) built
      holds
  rw [Cm.index_ofIndex] at result
  exact result

end IntegerModel
