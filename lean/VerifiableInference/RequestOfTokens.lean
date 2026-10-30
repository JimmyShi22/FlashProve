-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/RequestOfTokens.lean: from a prompt and output tokens to the request that the
verifier checks.

In VerifiableInference/Statements.lean a token is a number, and an instance is a prompt with output
tokens, two lists of any length. The integer model's relation is about a request
(`IntegerModel.Request`, IntegerModel/Reply.lean): a window of exactly 1,024 tokens below the size
of the vocabulary, two numbers r, e ≤ 1,024, and one further token y.
- `IntegerModel.requestOf` builds the request from lists of tokens of the vocabulary.
- `vocabularyTokens` reads numbers as tokens of the vocabulary.
- `requestOfTokens` does the second and then the first. `tokensOfRequest` goes back.
- `requestOfTokens_some`, `requestOfTokens_eq`: what `requestOfTokens` is, case by case.
- `tokensOfRequest_requestOfTokens`: the built request's prompt and checked tokens are the given
  prompt and output, whatever the padding.
- `IntegerModel.greedy_positions`: the tokens of `greedyOutput`, position by position.
The file holds no statement about a model, a scheme or a verifier. `ReadsModel`
(Johnson/Road/Lane5SoundFour.lean) asks of a builder of requests that it builds what
`requestOfTokens` builds. The padding, the tokens behind the output in the window, is a third
argument: whoever builds the request chooses it.
A verifier that takes the padding from the proof must be sound for every padding. An honest prover
that sends none is complete only for windows in which token 0 follows the output; the condition
`CanServe` (VerifiableInference/CanServe.lean) reads that window.
-/
import IntegerModel.Reply
import VerifiableInference.Statements

set_option autoImplicit false

open Inst.Model

namespace IntegerModel

/-! ## 1. The request of three lists of tokens of the vocabulary -/

/-- Token 0. It fills the window after the padding. -/
def tokenZero : Token := ⟨0, by decide⟩

/-- The request that the verifier checks: a window of 1,024 tokens (the prompt, the output, the
padding, then token 0); r, the position of the prompt's last token; e = r + the output's length.
With 1,025 tokens in all, the last output token is outside the window, as y; otherwise y is token 0.
Padding beyond the window does not enter the request. `none`: the prompt or the output is empty, or
they have more than 1,025 tokens together. -/
def requestOf (prompt output padding : List Token) : Option Request :=
  if h : 0 < prompt.length ∧ 0 < output.length ∧ prompt.length + output.length ≤ ppref.T + 1 then
    some ⟨fun t => (prompt ++ output ++ padding).getD t.val tokenZero,
      (prompt ++ output).getD ppref.T tokenZero,
      ⟨prompt.length - 1, by have h1 := h.1; have h2 := h.2.1; have h3 := h.2.2; omega⟩,
      ⟨prompt.length - 1 + output.length,
          by have h1 := h.1; have h2 := h.2.1; have h3 := h.2.2; omega⟩⟩
  else none

/-- Position j of p ++ o, for j inside p. -/
theorem getD_app_left {α : Type} (p o : List α) (d : α) (j : ℕ) (h : j < p.length) :
    (p ++ o).getD j d = p[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h]

/-- Position p.length + j of p ++ o, for j inside o. -/
theorem getD_app_right {α : Type} (p o : List α) (d : α) (j : ℕ) (h : j < o.length) :
    (p ++ o).getD (p.length + j) d = o[j] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Where a request is built: the conditions on the lengths, the request's r and e, and its tokens
at the positions of the prompt and the output. -/
theorem requestOf_some {prompt output padding : List Token} {x : Request}
    (h : requestOf prompt output padding = some x) :
    (0 < prompt.length ∧ 0 < output.length ∧ prompt.length + output.length ≤ ppref.T + 1)
    ∧ x.r = prompt.length - 1 ∧ x.e = prompt.length - 1 + output.length
    ∧ ∀ j, j < prompt.length + output.length →
      x.tok j = ((prompt ++ output).getD j tokenZero).val := by
  unfold requestOf at h
  split at h
  · rename_i hc
    injection h with h
    subst h
    refine ⟨hc, rfl, rfl, fun j hj => ?_⟩
    unfold Instance.tok
    split
    · show ((prompt ++ output ++ padding).getD j tokenZero).val =
        ((prompt ++ output).getD j tokenZero).val
      have hl : j < (prompt ++ output).length := by rw [List.length_append]; exact hj
      rw [getD_app_left (prompt ++ output) padding tokenZero j hl, List.getD_eq_getElem _ _ hl]
    · rename_i hjT
      have e : j = ppref.T := by have h3 := hc.2.2; omega
      rw [e]
  · cases h

/-- The built request's prompt (`promptOf`, IntegerModel/Reply.lean) is the given prompt. -/
theorem promptOf_requestOf {prompt output padding : List Token} {x : Request}
    (h : requestOf prompt output padding = some x) : promptOf x = prompt := by
  obtain ⟨hc, hr, -, ht⟩ := requestOf_some h
  unfold promptOf firstToks
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, hr]
    have h1 := hc.1
    omega
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    apply Fin.ext
    show x.tok j = (prompt[j]).val
    rw [ht j (by omega), getD_app_left prompt output tokenZero j h2]

/-- The built request's checked tokens (`replyOf`, IntegerModel/Reply.lean) are the given output. -/
theorem replyOf_requestOf {prompt output padding : List Token} {x : Request}
    (h : requestOf prompt output padding = some x) : replyOf x = output := by
  obtain ⟨hc, hr, he, ht⟩ := requestOf_some h
  unfold replyOf
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, hr, he]
    omega
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    apply Fin.ext
    show x.tok (x.r + j + 1) = (output[j]).val
    have e : x.r + j + 1 = prompt.length + j := by have h1 := hc.1; rw [hr]; omega
    rw [e, ht (prompt.length + j) (by omega), getD_app_right prompt output tokenZero j h2]

/-- If `greedyOutput f ctx out.length = some out`, each token of `out` is f's result on `ctx`
followed by the tokens of `out` before it. -/
theorem greedy_positions (f : List Token → Option Token) : ∀ (out ctx : List Token),
    greedyOutput f ctx out.length = some out →
    ∀ (i : ℕ) (h : i < out.length), f (ctx ++ out.take i) = some out[i]
  | [], _, _, i, h => absurd h (Nat.not_lt_zero i)
  | y :: rest, ctx, hg, i, h => by
      have hg' : greedyOutput f ctx (rest.length + 1) = some (y :: rest) := hg
      rw [greedyOutput] at hg'
      cases hf : f ctx with
      | none => rw [hf] at hg'; cases hg'
      | some y' =>
        rw [hf] at hg'
        have hg2 : (greedyOutput f (ctx ++ [y']) rest.length).map (y' :: ·) = some (y :: rest) :=
          hg'
        cases hr : greedyOutput f (ctx ++ [y']) rest.length with
        | none => rw [hr] at hg2; cases hg2
        | some r =>
          rw [hr] at hg2
          have e : y' :: r = y :: rest := Option.some.inj hg2
          injection e with e1 e2
          subst e1; subst e2
          cases i with
          | zero => simpa using hf
          | succ i =>
            have := greedy_positions f r (ctx ++ [y']) hr i (Nat.lt_of_succ_lt_succ h)
            simpa [List.append_assoc] using this

end IntegerModel

namespace VerifiableInference

/-! ## 2. Numbers as tokens of the vocabulary -/

/-- The tokens as elements of the vocabulary; `none` if one of them is not below its size. -/
def vocabularyTokens : List Token → Option (List IntegerModel.Token)
  | [] => some []
  | token :: rest =>
      if h : token < Inst.Model.ppref.V then (vocabularyTokens rest).map (⟨token, h⟩ :: ·) else none

/-- Elements of the vocabulary, written as numbers, are read back. -/
theorem vocabularyTokens_map_val : ∀ tokens : List IntegerModel.Token,
    vocabularyTokens (tokens.map Fin.val) = some tokens
  | [] => rfl
  | token :: rest => by
      show (if h : token.val < Inst.Model.ppref.V then (vocabularyTokens (rest.map Fin.val)).map
          ((⟨token.val, h⟩ : IntegerModel.Token) :: ·) else none) = some (token :: rest)
      rw [dif_pos token.isLt, vocabularyTokens_map_val rest]
      rfl

/-- What `vocabularyTokens` gives is the same numbers. -/
theorem map_val_of_vocabularyTokens : ∀ (list : List Token) (tokens : List IntegerModel.Token),
    vocabularyTokens list = some tokens → tokens.map Fin.val = list
  | [], tokens, h => by
      have e : tokens = [] := (Option.some.inj h).symm
      rw [e]
      rfl
  | token :: rest, tokens, h => by
      have h' : (if h : token < Inst.Model.ppref.V then (vocabularyTokens rest).map
          ((⟨token, h⟩ : IntegerModel.Token) :: ·) else none) = some tokens := h
      by_cases hv : token < Inst.Model.ppref.V
      · rw [dif_pos hv] at h'
        cases hr : vocabularyTokens rest with
        | none => rw [hr] at h'; cases h'
        | some restTokens =>
          rw [hr] at h'
          have e : (⟨token, hv⟩ : IntegerModel.Token) :: restTokens = tokens := Option.some.inj h'
          rw [← e]
          show token :: restTokens.map Fin.val = token :: rest
          rw [map_val_of_vocabularyTokens rest restTokens hr]
      · rw [dif_neg hv] at h'
        cases h'

/-- If `vocabularyTokens` returns `none`, one of the numbers is not below the size of the
vocabulary. -/
theorem exists_large_of_vocabularyTokens_none : ∀ list : List Token, vocabularyTokens list = none →
    ∃ (position : ℕ) (h : position < list.length), ¬ list[position] < Inst.Model.ppref.V
  | [], h => by cases h
  | token :: rest, h => by
      have h' : (if h : token < Inst.Model.ppref.V then (vocabularyTokens rest).map
          ((⟨token, h⟩ : IntegerModel.Token) :: ·) else none) = none := h
      by_cases hv : token < Inst.Model.ppref.V
      · rw [dif_pos hv] at h'
        have hr : vocabularyTokens rest = none := by
          cases e : vocabularyTokens rest with
          | none => rfl
          | some restTokens =>
            rw [e] at h'
            cases h'
        obtain ⟨position, hp, hb⟩ := exists_large_of_vocabularyTokens_none rest hr
        exact ⟨position + 1, Nat.succ_lt_succ hp, hb⟩
      · exact ⟨0, Nat.succ_pos _, hv⟩

/-- Numbers that `vocabularyTokens` accepts are below the size of the vocabulary. -/
theorem lt_of_vocabularyTokens {list : List Token} {tokens : List IntegerModel.Token}
    (h : vocabularyTokens list = some tokens) : ∀ token ∈ list, token < Inst.Model.ppref.V := by
  intro token ht
  rw [← map_val_of_vocabularyTokens list tokens h] at ht
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 ht
  exact t.isLt

/-! ## 3. The request of a prompt, output tokens and padding, all as numbers -/

/-- The request that the verifier checks: a window of 1,024 tokens (the prompt, the output, the
padding, then token 0); r, the position of the prompt's last token; e = r + the output's length.
With 1,025 tokens in all, the last output token is y; otherwise y is token 0. `none`: a number in
one of the three lists is not below the size of the vocabulary, the prompt or the output is empty,
or they have more than 1,025 tokens together. -/
def requestOfTokens (x : List Token × List Token) (padding : List Token) :
    Option IntegerModel.Request :=
  match vocabularyTokens x.1, vocabularyTokens x.2, vocabularyTokens padding with
  | some prompt, some output, some pad => IntegerModel.requestOf prompt output pad
  | _, _, _ => none

/-- The prompt and the checked tokens of a request, as numbers. -/
def tokensOfRequest (r : IntegerModel.Request) : List Token × List Token :=
  ((IntegerModel.promptOf r).map Fin.val, (IntegerModel.replyOf r).map Fin.val)

/-- Where a request is built, the three lists are tokens of the vocabulary, and the request is
`requestOf` of them. -/
theorem requestOfTokens_some {x : List Token × List Token} {padding : List Token}
    {r : IntegerModel.Request} (h : requestOfTokens x padding = some r) :
    ∃ prompt output pad, vocabularyTokens x.1 = some prompt ∧ vocabularyTokens x.2 = some output ∧
      vocabularyTokens padding = some pad ∧
        IntegerModel.requestOf prompt output pad = some r := by
  unfold requestOfTokens at h
  cases h1 : vocabularyTokens x.1 with
  | none => rw [h1] at h; cases h
  | some prompt =>
    cases h2 : vocabularyTokens x.2 with
    | none => rw [h1, h2] at h; cases h
    | some output =>
      cases h3 : vocabularyTokens padding with
      | none => rw [h1, h2, h3] at h; cases h
      | some pad =>
        rw [h1, h2, h3] at h
        exact ⟨prompt, output, pad, rfl, rfl, rfl, h⟩

/-- On three lists of tokens of the vocabulary `requestOfTokens` is `requestOf`. -/
theorem requestOfTokens_eq {x : List Token × List Token} {padding : List Token}
    {prompt output pad : List IntegerModel.Token} (h1 : vocabularyTokens x.1 = some prompt)
    (h2 : vocabularyTokens x.2 = some output) (h3 : vocabularyTokens padding = some pad) :
    requestOfTokens x padding = IntegerModel.requestOf prompt output pad := by
  simp only [requestOfTokens, h1, h2, h3]

/-- The built request's prompt and checked tokens are the given prompt and output. -/
theorem tokensOfRequest_requestOfTokens {x : List Token × List Token} {padding : List Token}
    {r : IntegerModel.Request} (h : requestOfTokens x padding = some r) :
    tokensOfRequest r = x := by
  obtain ⟨prompt, output, pad, h1, h2, -, hs⟩ := requestOfTokens_some h
  exact Prod.ext
    ((congrArg (List.map Fin.val) (IntegerModel.promptOf_requestOf hs)).trans
      (map_val_of_vocabularyTokens _ _ h1))
    ((congrArg (List.map Fin.val) (IntegerModel.replyOf_requestOf hs)).trans
      (map_val_of_vocabularyTokens _ _ h2))

end VerifiableInference

#print axioms IntegerModel.requestOf_some
#print axioms IntegerModel.promptOf_requestOf
#print axioms IntegerModel.replyOf_requestOf
#print axioms IntegerModel.greedy_positions
#print axioms VerifiableInference.vocabularyTokens_map_val
#print axioms VerifiableInference.map_val_of_vocabularyTokens
#print axioms VerifiableInference.exists_large_of_vocabularyTokens_none
#print axioms VerifiableInference.lt_of_vocabularyTokens
#print axioms VerifiableInference.requestOfTokens_some
#print axioms VerifiableInference.requestOfTokens_eq
#print axioms VerifiableInference.tokensOfRequest_requestOfTokens
#print axioms IntegerModel.getD_app_left
#print axioms IntegerModel.getD_app_right
