-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Arrays/RequestResultLaws.lean

What "the result of the request is these output tokens" says
(`requestResult`, VerifiableInference/RequestResult.lean), at valid settings unless stated
otherwise.

* `requestForm_iff_requestOfTokens`: `RequestForm` holds exactly if the library builds a request
  of the prompt and the output.
* `canServe_and_modelOutput_iff`: `CanServe` holds and the output tokens are the model's exactly
  if the prompt and the output make a request whose result is these output tokens.
* `requestForm_of_requestResult`, at all settings: of the four conditions of `RequestForm` two
  follow from the result: if neither list is empty and the result is the output tokens, every token
  is in the vocabulary and there are at most 1,025 tokens.
* `requestResult_of_emptyPrompt`: the condition that the prompt is not empty does not follow.

How the main equivalence is proved. Both sides are compared with "the library builds the request,
and its relation holds on the request's window" (`IntegerModel.HoldsOnWindow`,
IntegerModel/Reply.lean): the left side by `IntegerModel.canServeModelOutput_iff`
(IntegerModel/ModelOutput.lean), the right side by part 1 of this file.
-/
import VerifiableInference.RequestResult
import IntegerModel.Arrays.SameModel
import IntegerModel.Readable.Facts
import IntegerModel.Readable.Reads

set_option autoImplicit false

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference

open IntegerTransformer
open Inst.Model IntegerModel.Readable IntegerModel.Runnable

/-! ## 1. The run on a request's window, in the library's terms -/

/-- Take from a table of N values, from place r on, as many entries as a given list has, all of them
inside the table. They are that list exactly if the table's value at r + k is the list's entry k,
for each k. -/
private theorem drop_take_eq_iff (g : ℕ → ℕ) (N r : ℕ) (l : List ℕ) (fits : r + l.length ≤ N) :
    (((List.range N).map g).drop r).take l.length = l ↔
      ∀ k (inList : k < l.length), g (r + k) = l[k] := by
  constructor
  · intro e k inList
    have h := congrArg (fun m => m[k]?) e
    simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_map, inList, if_true] at h
    have inTable : r + k < N := by omega
    simpa [inTable, inList] using h
  · intro e
    apply List.ext_getElem
    · simp
      omega
    · intro k h1 h2
      simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
      exact e k h2

section OnWindow
variable {settings : Settings} (valid : settingsAreValid settings = true)
  (weights : ModelWeights settings)

/-- The library's form of the settings and weights. -/
private abbrev committed : IntegerModel.Committed :=
  IntegerModel.committedOf (scalesOf settings) (lawful_scalesOf valid)
    (indexOfWeights valid weights)

/-- The settings, the lookup tables and the weights hold the numbers of their library form and pass
the model's own test of shapes (`Feeds`, IntegerModel/Readable/Tie.lean). -/
private theorem feeds_weights :
    Feeds (committed valid weights) settings lookupTables weights.val := by
  have h := feeds_weightsOfIndex valid (indexOfWeights valid weights)
  rw [weightsOfIndex_indexOfWeights] at h
  exact h

/-- The logits of the library's program on the window of a request. -/
private abbrev logitsAt (x : IntegerModel.Request) (t : ℕ) : Inst.Model.Vec :=
  lgK ppref (committed valid weights).settings.kap (committed valid weights).settings.nf
    (fun _ => tbRef) (committed valid weights).weights.val x.prompt t

/-- The choices of the run on a list of tokens that begins a window are the library's first arg-max
on that window, by position. -/
private theorem choices_of_list (ctx : List IntegerModel.Token) (hn : ctx.length ≤ ppref.T)
    (p : Fin ppref.T → Fin ppref.V)
    (hget : ∀ t (ht : t < ctx.length), ctx.get ⟨t, ht⟩ = p ⟨t, lt_of_lt_of_le ht hn⟩) :
    (trace settings lookupTables weights.val (ctx.map Fin.val).toArray).choices.toList
      = (List.range ctx.length).map fun t =>
          argTo (lgK ppref (committed valid weights).settings.kap
            (committed valid weights).settings.nf (fun _ => tbRef)
            (committed valid weights).weights.val p t) (ppref.V - 1) := by
  have hF := feeds_weights valid weights
  have e : (ctx.map Fin.val).toArray
      = toks { ppref with T := ctx.length } (fun i => ctx.get i) := toks_eq ctx
  rw [e, trace_choices { ppref with T := ctx.length } (good_ref _) ppref.T hn _ _ _ _ settings
    lookupTables weights.val (hF.same.withT _) (fun i => ctx.get i), tabl_toList]
  exact List.map_congr_left fun t ht =>
    congrArg (fun f => argTo f (ppref.V - 1))
      (IntegerModel.lgK_prefix ppref _ hn _ _ _ _ p (fun i => ctx.get i) hget
        (List.mem_range.1 ht))

/-- The choices of the run on a request's window are the library's first arg-max, by position. -/
private theorem choices_of_window (x : IntegerModel.Request) :
    (trace settings lookupTables weights.val
        ((IntegerModel.firstToks x 1024).map Fin.val).toArray).choices.toList
      = (List.range 1024).map fun t => argTo (logitsAt valid weights x t) (ppref.V - 1) := by
  have hlen : (IntegerModel.firstToks x 1024).length = 1024 := IntegerModel.firstToks_length x 1024
  have hT : ppref.T = 1024 := rfl
  have hn : (IntegerModel.firstToks x 1024).length ≤ ppref.T := by rw [hlen, hT]
  rw [choices_of_list valid weights (IntegerModel.firstToks x 1024) hn x.prompt
    (fun t ht => IntegerModel.firstToks_get x 1024 (le_of_eq hT.symm) t ht), hlen]

/-- The library's first arg-max is a given token exactly if that token has the largest logit and is
the least such. -/
private theorem argTo_eq_iff (f : Inst.Model.Vec) (a : ℕ) (small : a < ppref.V) :
    argTo f (ppref.V - 1) = a ↔ (∀ v < ppref.V, f v ≤ f a) ∧ ∀ v < a, f v < f a := by
  constructor
  · intro e
    obtain ⟨-, b1, b2⟩ := argTo_spec f (ppref.V - 1)
    rw [e] at b1 b2
    exact ⟨fun v hv => b1 v (Nat.le_sub_one_of_lt hv), b2⟩
  · rintro ⟨h1, h2⟩
    exact IntegerModel.argTo_unique f (ppref.V - 1) a (Nat.le_sub_one_of_lt small)
      (fun v hv => h1 v (lt_of_le_of_lt hv (Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le a) small)
        Nat.one_pos))) h2

/-- The library's program has a value on a request's window exactly if it runs there. -/
private theorem window_isSome_iff (m : IntegerModel.Committed) (x : IntegerModel.Request) :
    (IntegerModel.programNextToken m (IntegerModel.firstToks x 1024)).isSome = true ↔
      RunsK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt := by
  have hT : ppref.T = 1024 := rfl
  have hlen : (IntegerModel.firstToks x 1024).length = 1024 := IntegerModel.firstToks_length x 1024
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 h
    exact IntegerModel.runs_of_full m x.prompt (IntegerModel.firstToks x 1024) (hlen.trans hT.symm)
      (fun t _ ht' => (IntegerModel.firstToks_get x 1024 (le_of_eq hT.symm) t ht').symm)
      (IntegerModel.model_some hy).1.2.2
  · intro h
    exact IntegerModel.model_isSome_of_window m x.prompt (IntegerModel.firstToks x 1024)
      (by rw [hlen]; exact Nat.succ_pos _) (by rw [hlen, hT])
      (fun t ht => IntegerModel.firstToks_get x 1024 (le_of_eq hT.symm) t ht) h

/-- For a request that the library builds: the result is the output tokens exactly if the library's
relation holds on the request's window. -/
private theorem result_iff_holds {prompt output : List ℕ} {x : IntegerModel.Request}
    (built : requestOfTokens (prompt, output) [] = some x) :
    requestResult settings weights prompt output = some output ↔
      IntegerModel.HoldsOnWindow (committed valid weights).settings
        (committed valid weights).weights x := by
  obtain ⟨p, o, pad, hp, ho, hpad, hx⟩ := requestOfTokens_some built
  obtain rfl : [] = pad := Option.some.inj hpad
  obtain rfl : p.map Fin.val = prompt := map_val_of_vocabularyTokens prompt p hp
  obtain rfl : o.map Fin.val = output := map_val_of_vocabularyTokens output o ho
  have hT : ppref.T = 1024 := rfl
  obtain ⟨⟨h1, h2, h3⟩, hr, he, -⟩ := IntegerModel.requestOf_some hx
  rw [hT] at h3
  have window : IntegerModel.zeroFilledWindow (p.map Fin.val) (o.map Fin.val)
      = (IntegerModel.firstToks x 1024).map Fin.val := by
    rw [IntegerModel.zeroFilledWindow_map, IntegerModel.firstToks_requestOf hx]
  have form := IntegerModel.form_of_requestWellFormed (IntegerModel.requestWellFormed_requestOf hx)
  have reply : ∀ k (hk : k < o.length), x.w (x.r + k) = (o[k]).val := by
    intro k hk
    have e := IntegerModel.replyOf_requestOf hx
    have hk' : k < (IntegerModel.replyOf x).length := by rw [e]; exact hk
    have e2 : (IntegerModel.replyOf x)[k] = o[k] := List.getElem_of_eq e hk'
    rw [← e2]
    simp only [IntegerModel.replyOf, List.getElem_map, List.getElem_range]
  have fits : x.r + (o.map Fin.val).length ≤ 1024 := by
    rw [List.length_map]
    omega
  have rlen : (p.map Fin.val).length - 1 = x.r := by rw [List.length_map, hr]
  unfold requestResult
  dsimp only
  rw [window, modelNextToken_eq valid weights, Option.isSome_map,
    choices_of_window valid weights x, rlen]
  constructor
  · intro h
    split at h
    · rename_i hasValue
      have entries := (drop_take_eq_iff _ 1024 x.r _ fits).1 (Option.some.inj h)
      refine ⟨form, (window_isSome_iff _ x).1 hasValue, fun t rt te => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, t = x.r + k := ⟨t - x.r, by omega⟩
      have hk : k < o.length := by omega
      have e1 := entries k (by rw [List.length_map]; exact hk)
      rw [List.getElem_map, ← reply k hk] at e1
      exact (argTo_eq_iff _ _ (x.w_lt _)).1 e1
    · exact absurd h (by simp)
  · rintro ⟨-, runs, chosen⟩
    rw [if_pos ((window_isSome_iff _ x).2 runs)]
    refine congrArg some ((drop_take_eq_iff _ 1024 x.r _ fits).2 fun k hk' => ?_)
    have hk : k < o.length := by rw [List.length_map] at hk'; exact hk'
    rw [List.getElem_map, ← reply k hk]
    exact (argTo_eq_iff _ _ (x.w_lt _)).2 (chosen (x.r + k) (by omega) (by omega))

end OnWindow

/-! ## 2. The statements -/

/-- At valid settings a prompt and output tokens make a request exactly if `requestOfTokens`
(VerifiableInference/RequestOfTokens.lean) builds a request of them, with the empty list as the
prover's padding. -/
theorem requestForm_iff_requestOfTokens {settings : Settings}
    (valid : settingsAreValid settings = true) (prompt output : List Nat) :
    RequestForm settings prompt output ↔
      (requestOfTokens (prompt, output) []).isSome = true := by
  have hV : settings.vocabulary = ppref.V := vocabulary_eq valid
  have hT : ppref.T + 1 = 1025 := rfl
  constructor
  · rintro ⟨small, outputNotEmpty, promptNotEmpty, atMost⟩
    rw [hV] at small
    obtain ⟨p, hp⟩ := IntegerModel.vocabularyTokens_of_small prompt fun token member =>
      small token (List.mem_append_left _ member)
    obtain ⟨o, ho⟩ := IntegerModel.vocabularyTokens_of_small output fun token member =>
      small token (List.mem_append_right _ member)
    have lp : p.length = prompt.length := by
      rw [← map_val_of_vocabularyTokens prompt p hp, List.length_map]
    have lo : o.length = output.length := by
      rw [← map_val_of_vocabularyTokens output o ho, List.length_map]
    have e : requestOfTokens (prompt, output) [] = IntegerModel.requestOf p o [] := by
      unfold requestOfTokens
      rw [hp, ho]
      rfl
    rw [e]
    unfold IntegerModel.requestOf
    rw [dif_pos ⟨by rw [lp]; exact List.length_pos_iff.2 promptNotEmpty,
      by rw [lo]; exact List.length_pos_iff.2 outputNotEmpty, by rw [lp, lo, hT]; exact atMost⟩]
    rfl
  · intro h
    obtain ⟨x, built⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨p, o, pad, hp, ho, -, hx⟩ := requestOfTokens_some built
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := IntegerModel.requestOf_some hx
    have lp : p.length = prompt.length := by
      rw [← map_val_of_vocabularyTokens prompt p hp, List.length_map]
    have lo : o.length = output.length := by
      rw [← map_val_of_vocabularyTokens output o ho, List.length_map]
    rw [lp] at h1 h3
    rw [lo] at h2 h3
    refine ⟨fun token member => ?_, List.length_pos_iff.1 h2, List.length_pos_iff.1 h1, h3⟩
    rw [hV]
    exact (List.mem_append.1 member).elim (lt_of_vocabularyTokens hp token)
      (lt_of_vocabularyTokens ho token)

/-- **For a request, the result is the output tokens exactly if they are the model's and the request
can be served.** At valid settings, for all weights, prompts and output tokens, these two are
equivalent.
Left: the three conditions of `CanServe`, and each output token is the model's next token after the
prompt and the output tokens before it (the text of `IsModelOutput`,
VerifiableInference/Statements.lean, with `modelNextToken` as the model).
Right: the prompt and the output make a request, and its result is these output tokens. -/
theorem canServe_and_modelOutput_iff {settings : Settings}
    (valid : settingsAreValid settings = true) (weights : ModelWeights settings)
    (prompt output : List Nat) :
    (CanServe settings weights prompt output ∧
      ∀ position (inOutput : position < output.length),
        modelNextToken settings weights (prompt ++ output.take position)
          = some output[position]) ↔
    (RequestForm settings prompt output ∧
      requestResult settings weights prompt output = some output) := by
  have lawful := lawful_scalesOf valid
  have tie := settingsOf_scalesOf valid
  have left : (CanServe settings weights prompt output ∧
      ∀ position (inOutput : position < output.length),
        modelNextToken settings weights (prompt ++ output.take position)
          = some output[position]) ↔
      IntegerModel.CanServeModelOutput (scalesOf settings) (indexOfWeights valid weights).index
        prompt output := by
    unfold IntegerModel.CanServeModelOutput
    rw [canServe_iff lawful valid tie weights prompt output]
    simp only [modelNextToken_eq_nextToken_of_weights lawful valid tie weights]
  have bridge : ∀ x : IntegerModel.Request,
      Cm.PaperTrue (scalesOf settings).kap (scalesOf settings).nf (indexOfWeights valid weights) x ↔
        IntegerModel.HoldsOnWindow (committed valid weights).settings
          (committed valid weights).weights x := fun x =>
    (Cm.paper_iff _ _ _ x).symm.trans
      (IntegerModel.trueAt_iff_holdsOnWindow
        ⟨(scalesOf settings).w, (scalesOf settings).nf, AcceptancePolicy.exact⟩ _ x)
  rw [left, IntegerModel.canServeModelOutput_iff _ lawful]
  constructor
  · rintro ⟨x, built, holds⟩
    exact ⟨(requestForm_iff_requestOfTokens valid prompt output).2 (by rw [built]; rfl),
      (result_iff_holds valid weights built).2 ((bridge x).1 holds)⟩
  · rintro ⟨form, result⟩
    obtain ⟨x, built⟩ :=
      Option.isSome_iff_exists.1 ((requestForm_iff_requestOfTokens valid prompt output).1 form)
    exact ⟨x, built, (bridge x).2 ((result_iff_holds valid weights built).1 result)⟩

/-- If neither the prompt nor the output is empty and the result is the output tokens, then the
prompt and the output make a request: that every token is in the vocabulary, and that there are at
most 1,025 tokens, follows. -/
theorem requestForm_of_requestResult {settings : Settings} (weights : ModelWeights settings)
    (prompt output : List Nat) (promptNotEmpty : prompt ≠ []) (outputNotEmpty : output ≠ [])
    (isResult : requestResult settings weights prompt output = some output) :
    RequestForm settings prompt output := by
  have promptLength : 0 < prompt.length := List.length_pos_iff.2 promptNotEmpty
  have outputLength : 0 < output.length := List.length_pos_iff.2 outputNotEmpty
  unfold requestResult at isResult
  dsimp only at isResult
  split at isResult
  · rename_i hasValue
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hasValue
    obtain ⟨formed, isTokens, -, -⟩ := (model_eq_some settings lookupTables weights.val _ y).1 hy
    obtain ⟨-, -, -, -, -, -, size, below⟩ :=
      trace_shape settings lookupTables weights.val _ formed isTokens
    have windowLength : (IntegerModel.zeroFilledWindow prompt output).length = 1024 := by
      unfold IntegerModel.zeroFilledWindow
      rw [List.length_take, List.length_append, List.length_replicate]
      omega
    have windowSize : (IntegerModel.zeroFilledWindow prompt output).toArray.size = 1024 :=
      windowLength
    rw [windowSize] at size below
    have e := Option.some.inj isResult
    have lengths := congrArg List.length e
    have choicesLength : (trace settings lookupTables weights.val
        (IntegerModel.zeroFilledWindow prompt output).toArray).choices.toList.length = 1024 := size
    rw [List.length_take, List.length_drop, choicesLength] at lengths
    have atMost : prompt.length + output.length ≤ 1025 := by omega
    refine ⟨fun token member => ?_, outputNotEmpty, promptNotEmpty, atMost⟩
    rcases List.mem_append.1 member with inPrompt | inOutput
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem inPrompt
      have inWindow : prompt[j] ∈ IntegerModel.zeroFilledWindow prompt output := by
        have j1024 : j < 1024 := by omega
        apply List.mem_of_getElem? (i := j)
        unfold IntegerModel.zeroFilledWindow
        rw [List.append_assoc, List.getElem?_take_of_lt j1024, List.getElem?_append_left hj,
          List.getElem?_eq_getElem hj]
      by_contra large
      rw [modelNextToken_none_of_token weights _ ⟨_, inWindow, Nat.le_of_not_lt large⟩] at hasValue
      exact absurd hasValue (by simp)
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem inOutput
      have inRun : prompt.length - 1 + k < 1024 := by omega
      have e2 := List.getElem_of_eq e.symm hk
      rw [e2]
      simp only [List.getElem_take, List.getElem_drop, Array.getElem_toList]
      have b := below (prompt.length - 1 + k) inRun
      simpa [Array.entry, Array.getD, size, inRun] using b
  · exact absurd isResult (by simp)

/-- In `canServe_and_modelOutput_iff` the condition that the prompt is not empty cannot be left out.
At all valid settings there are weights at which the result of the empty prompt with the output of
one token 0 is that output, while the model has no value on the empty list, so that the output token
is not the model's. -/
theorem requestResult_of_emptyPrompt {settings : Settings}
    (valid : settingsAreValid settings = true) :
    ∃ weights : ModelWeights settings,
      requestResult settings weights [] [0] = some [0] ∧
        modelNextToken settings weights [] = none := by
  have lawful := lawful_scalesOf valid
  have tie := settingsOf_scalesOf valid
  have zero := IntegerModel.canServeModelOutput_atZeroWeights (scalesOf settings) lawful
  refine ⟨weightsOfIndex valid (Cm.Idx.ofIndex ScalesSanity.iZero), ?_, ?_⟩
  · have left :
        CanServe settings (weightsOfIndex valid (Cm.Idx.ofIndex ScalesSanity.iZero)) [0] [0] ∧
        ∀ position (inOutput : position < [0].length),
          modelNextToken settings (weightsOfIndex valid (Cm.Idx.ofIndex ScalesSanity.iZero))
            ([0] ++ [0].take position) = some [0][position] := by
      refine ⟨(canServe_weightsOfIndex_iff lawful valid tie _ _ _).2 ?_,
        fun position inOutput => ?_⟩
      · rw [Cm.index_ofIndex]
        exact zero.1
      · rw [modelNextToken_eq_nextToken lawful valid tie, Cm.index_ofIndex]
        exact zero.2 position inOutput
    have result := ((canServe_and_modelOutput_iff valid _ [0] [0]).1 left).2
    have zeros : ∀ n : ℕ, ([] ++ [0] ++ List.replicate n 0 : List ℕ).take n
        = ([0] ++ [0] ++ List.replicate n 0).take n := by
      intro n
      show (0 :: List.replicate n 0).take n = (0 :: 0 :: List.replicate n 0).take n
      rw [← List.replicate_succ, ← List.replicate_succ, List.take_replicate, List.take_replicate,
        Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    have window : IntegerModel.zeroFilledWindow [] [0] = IntegerModel.zeroFilledWindow [0] [0] :=
      zeros 1024
    rw [← result]
    unfold requestResult
    dsimp only
    rw [window]
    rfl
  · simp [modelNextToken, model, isPrompt]

end VerifiableInference

#print axioms VerifiableInference.requestForm_iff_requestOfTokens
#print axioms VerifiableInference.canServe_and_modelOutput_iff
#print axioms VerifiableInference.requestForm_of_requestResult
#print axioms VerifiableInference.requestResult_of_emptyPrompt
