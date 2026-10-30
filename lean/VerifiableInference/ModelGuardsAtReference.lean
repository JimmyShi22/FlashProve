-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/ModelGuardsAtReference.lean

Guards on the model function at the settings of the library's reference table of scales: a layer
counts, an earlier token counts, and a request at such weights meets `CanServe`; at other valid
weights no request does.

The guards of VerifiableInference/ModelGuards.lean show at all valid settings that
`modelNextToken` is not constant, at made-up weights all of whose layers are zero. Here the
library's made-up weights `wA` and `wZ` (Inst/Model/SanityAtt.lean) are carried to `modelNextToken`,
as `attentionWeights` and `zeroLayerWeights`.
* `modelNextToken_reads_layer`: on one prompt of 1,024 tokens the two answer 7 and 0.
* `modelNextToken_reads_earlier_token`: at `attentionWeights`, two prompts of 1,024 tokens with the
  same last token are answered 7 and 0.
* `canServe_atAttentionWeights`: at `attentionWeights` the first of these prompts, with the model's
  output of one token, meets `CanServe`.
* `canServe_nowhere_atHaltingWeights`: at other valid weights, `haltingWeights`, no prompt and
  output meet `CanServe`.

Limits. The weights are made up for these proofs, and there is one table of scales alone (at some
valid settings every layer adds nothing, by hand and no theorem:
VerifiableInference/ModelWeights.lean, at `weightsAreValid`). `wA` and `wZ` differ in two matrices
of layer 0, the value and the output projection. In `wA` the queries and keys are zero, so attention
is the plain mean over the positions so far; its feed-forward block and the layers 1 to 47 are zero.
So nothing here shows that the answer of `modelNextToken` reads queries, keys, the rotary tables,
any row of the exponential table but the first, a feed-forward block, the router, an expert, or a
layer above layer 0. At `haltingWeights` the queries of layer 0 enter through a range condition
alone, and no pair of weights here shows that. The two prompts of the second guard differ at all
1,023 earlier positions. The answer 0 is the one that the model gives when all logits are equal. In
the library's own types, not carried here: the router and the routed experts of layer 1
(`Cm.true_router`, `Cm.true_expert`, Cm/RelTrueExp.lean, whose head lists what has no guard at all).
That `wA` and `wZ` differ in layer 0 alone is stated of the library's tensors (three clauses of
`modelNextToken_reads_layer`); of the arrays it is said by reading. -/
import VerifiableInference.ModelGuards
import Cm.RelTrueExp

set_option autoImplicit false

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference

open Inst.Model Inst.Model.SanityAtt Inst.Model.SanityRef

/-- The request that is built from a window of 1,024 tokens and one output token, without padding,
is the library's request "the next token after these 1,024 tokens". -/
theorem requestOf_ofFn (window : Fin ppref.T → Fin ppref.V) (y : Fin ppref.V) :
    IntegerModel.requestOf (List.ofFn window) [y] [] = some (Instance.nextOf window y) := by
  have hl : (List.ofFn window).length = ppref.T := List.length_ofFn
  unfold IntegerModel.requestOf
  rw [dif_pos ⟨by rw [hl]; decide, Nat.succ_pos 0, by rw [hl]; exact le_refl _⟩]
  refine congrArg some ?_
  unfold Instance.nextOf
  rw [Instance.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext t
    rw [List.append_nil, IntegerModel.getD_app_left (List.ofFn window) [y] IntegerModel.tokenZero
      t.val (by rw [hl]; exact t.isLt)]
    simp
  · have h := IntegerModel.getD_app_right (List.ofFn window) [y] IntegerModel.tokenZero 0
      Nat.zero_lt_one
    rw [hl] at h
    exact h
  · exact Fin.ext (by show (List.ofFn window).length - 1 = ppref.T - 1; rw [hl])
  · exact Fin.ext (by show (List.ofFn window).length - 1 + 1 = ppref.T; rw [hl]; rfl)

/-- The request that is built from lists of numbers which are tokens, without padding, is the one
built from the tokens. -/
theorem requestOfTokens_map_val (prompt output : List IntegerModel.Token) :
    requestOfTokens (prompt.map Fin.val, output.map Fin.val) []
      = IntegerModel.requestOf prompt output [] :=
  requestOfTokens_eq (vocabularyTokens_map_val prompt) (vocabularyTokens_map_val output) rfl

/-- The settings of the library's reference table of scales. -/
def referenceSettings : IntegerTransformer.Settings :=
  settingsOf Cm.sRef

/-- `referenceSettings` are valid. -/
theorem referenceSettings_valid : settingsAreValid referenceSettings = true :=
  settingsAreValid_settingsOf Cm.lawful_sRef

/-- At the settings of the reference table of scales: if the library's program answers y after a
window of 1,024 tokens (`ModelIs`, Inst/Model/Program.lean), so does `modelNextToken`, at the arrays
of these tensors. -/
theorem modelNextToken_atReferenceSettings (tensors : Index ppref)
    (window : Fin ppref.T → Fin ppref.V) (y : Fin ppref.V)
    (h : ModelIs ppref tbRef tensors.val window y.val) :
    modelNextToken referenceSettings
        (weightsOfIndex referenceSettings_valid (Cm.Idx.ofIndex tensors))
        ((List.ofFn window).map Fin.val) = some y.val := by
  have holds : Cm.PaperTrue Cm.sRef.kap Cm.sRef.nf (Cm.Idx.ofIndex tensors)
      (Instance.nextOf window y) :=
    (Cm.paper_iff _ _ _ _).1 ((Cm.true_next tensors window y).2 h)
  have built : requestOfTokens ((List.ofFn window).map Fin.val, [y].map Fin.val) []
      = some (Instance.nextOf window y) :=
    (requestOfTokens_map_val (List.ofFn window) [y]).trans (requestOf_ofFn window y)
  have h0 := IntegerModel.isModelOutput_of_isTrueRequest Cm.sRef Cm.lawful_sRef
    (Cm.Idx.ofIndex tensors) built holds 0 Nat.zero_lt_one
  rw [List.take_zero, List.append_nil] at h0
  show modelNextToken (settingsOf Cm.sRef)
    (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) (Cm.Idx.ofIndex tensors))
    ((List.ofFn window).map Fin.val) = some y.val
  rw [modelNextToken_eq_nextToken Cm.lawful_sRef (settingsAreValid_settingsOf Cm.lawful_sRef) rfl]
  exact h0

/-- Under the same hypothesis the window with the one output token y meets `CanServe`. -/
theorem canServe_atReferenceSettings (tensors : Index ppref) (window : Fin ppref.T → Fin ppref.V)
    (y : Fin ppref.V) (h : ModelIs ppref tbRef tensors.val window y.val) :
    CanServe referenceSettings (weightsOfIndex referenceSettings_valid (Cm.Idx.ofIndex tensors))
      ((List.ofFn window).map Fin.val) [y.val] := by
  have holds : Cm.PaperTrue Cm.sRef.kap Cm.sRef.nf (Cm.Idx.ofIndex tensors)
      (Instance.nextOf window y) :=
    (Cm.paper_iff _ _ _ _).1 ((Cm.true_next tensors window y).2 h)
  have built : requestOfTokens ((List.ofFn window).map Fin.val, [y].map Fin.val) []
      = some (Instance.nextOf window y) :=
    (requestOfTokens_map_val (List.ofFn window) [y]).trans (requestOf_ofFn window y)
  exact (canServe_weightsOfIndex_iff Cm.lawful_sRef (settingsAreValid_settingsOf Cm.lawful_sRef) rfl
    _ _ _).2 (IntegerModel.canServeModelOutput_of_isTrueRequest Cm.sRef Cm.lawful_sRef
      (Cm.Idx.ofIndex tensors) built holds).1

/-- The library's window `pA`: token 0 at 1,023 positions, then token 1. -/
theorem tokens_zerosThenOne : (List.ofFn pA).map Fin.val = List.replicate 1023 0 ++ [1] := by
  decide +kernel

/-- The library's window `pB`: token 1 at all 1,024 positions. -/
theorem tokens_allOnes : (List.ofFn pB).map Fin.val = List.replicate 1024 1 := by
  decide +kernel

/-- Made-up weights whose layer 0 has an attention block that computes; by their definition all
other layers are zero (`wA`, Inst/Model/SanityAtt.lean). -/
def attentionWeights : ModelWeights referenceSettings :=
  weightsOfIndex referenceSettings_valid (Cm.Idx.ofIndex ⟨wA, wA_wf⟩)

/-- The same made-up weights with layer 0 zero too (`wZ`, Inst/Model/SanityAtt.lean). -/
def zeroLayerWeights : ModelWeights referenceSettings :=
  weightsOfIndex referenceSettings_valid (Cm.Idx.ofIndex ⟨wZ, wZ_wf⟩)

/-- Made-up valid weights at which a range condition of the program fails on every window of 1,024
tokens (`haltW`, Inst/Model/SanityRef.lean; the proof of `Cm.empty_language`, Cm/RelTrueExp.lean).
-/
def haltingWeights : ModelWeights referenceSettings :=
  weightsOfIndex referenceSettings_valid (Cm.Idx.ofIndex ⟨haltW, haltW_wf⟩)

/-- A layer counts. `attentionWeights` and `zeroLayerWeights` are read off the library's tensors
`wA` and `wZ`, which have the same embedding, the same output matrix and the same layers but for
layer 0 (there they differ in the value and output projections, by their definitions); they answer
one prompt of 1,024 tokens differently: 7 and 0. -/
theorem modelNextToken_reads_layer :
    wA.Emb = wZ.Emb ∧ wA.H = wZ.H ∧ (∀ L, L ≠ 0 → wA.layer L = wZ.layer L) ∧
      modelNextToken referenceSettings attentionWeights (List.replicate 1023 0 ++ [1]) = some 7 ∧
      modelNextToken referenceSettings zeroLayerWeights (List.replicate 1023 0 ++ [1])
        = some 0 := by
  rw [← tokens_zerosThenOne]
  exact ⟨rfl, rfl, fun _ hL => if_neg hL,
    modelNextToken_atReferenceSettings ⟨wA, wA_wf⟩ pA ⟨7, by decide⟩ model_wA_pA,
    modelNextToken_atReferenceSettings ⟨wZ, wZ_wf⟩ pA ⟨0, by decide⟩ model_wZ_pA⟩

/-- An earlier token counts. `attentionWeights` answer two prompts of 1,024 tokens with the same
last token, 1, differently: 7 and 0. -/
theorem modelNextToken_reads_earlier_token :
    modelNextToken referenceSettings attentionWeights (List.replicate 1023 0 ++ [1]) = some 7 ∧
      modelNextToken referenceSettings attentionWeights (List.replicate 1024 1) = some 0 := by
  rw [← tokens_zerosThenOne, ← tokens_allOnes]
  exact ⟨modelNextToken_atReferenceSettings ⟨wA, wA_wf⟩ pA ⟨7, by decide⟩ model_wA_pA,
    modelNextToken_atReferenceSettings ⟨wA, wA_wf⟩ pB ⟨0, by decide⟩ model_wA_pB⟩

/-- `CanServe` is met at weights with a layer whose attention block computes: at `attentionWeights`,
by the prompt of `modelNextToken_reads_layer` with the output of one token 7, which is the model's.
So the statements on completeness and on zero-knowledge are not empty at these weights. -/
theorem canServe_atAttentionWeights :
    CanServe referenceSettings attentionWeights (List.replicate 1023 0 ++ [1]) [7] ∧
      modelNextToken referenceSettings attentionWeights (List.replicate 1023 0 ++ [1])
        = some 7 := by
  rw [← tokens_zerosThenOne]
  exact ⟨canServe_atReferenceSettings ⟨wA, wA_wf⟩ pA ⟨7, by decide⟩ model_wA_pA,
    modelNextToken_atReferenceSettings ⟨wA, wA_wf⟩ pA ⟨7, by decide⟩ model_wA_pA⟩

/-- A window of 1,024 tokens with one more token behind it is its own window. -/
theorem windowOf_of_length (window : List IntegerModel.Token) (y : IntegerModel.Token)
    (h : window.length = 1024) : IntegerModel.windowOf window [y] = window := by
  unfold IntegerModel.windowOf
  rw [List.append_assoc, List.take_append_of_le_length (le_of_eq h.symm),
    List.take_of_length_le (le_of_eq h)]

/-- At a lawful table: if some prompt and output meet `IntegerModel.CanServeAtIndex` at an index,
some request is true at that index: the one that checks the model's one token after the zero-filled
window. -/
theorem exists_isTrueRequest_of_canServeAtIndex (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx)
    {prompt output : List ℕ} (h : IntegerModel.CanServeAtIndex s i.index prompt output) :
    ∃ x, Cm.PaperTrue s.kap s.nf i x := by
  obtain ⟨small, -, runs⟩ := h
  obtain ⟨p, hp⟩ := IntegerModel.vocabularyTokens_of_small prompt fun token member =>
    small token (List.mem_append_left _ member)
  obtain ⟨o, ho⟩ := IntegerModel.vocabularyTokens_of_small output fun token member =>
    small token (List.mem_append_right _ member)
  obtain rfl : p.map Fin.val = prompt := map_val_of_vocabularyTokens prompt p hp
  obtain rfl : o.map Fin.val = output := map_val_of_vocabularyTokens output o ho
  rw [IntegerModel.zeroFilledWindow_map, IntegerModel.nextToken_eq_programNextToken s hs,
    vocabularyTokens_map_val] at runs
  have runs' : ((IntegerModel.programNextToken (IntegerModel.committedOf s hs i)
      (IntegerModel.windowOf p o)).map Fin.val).isSome = true := runs
  rw [Option.isSome_map] at runs'
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 runs'
  have len : (IntegerModel.windowOf p o).length = 1024 := by
    unfold IntegerModel.windowOf
    rw [List.length_take, List.length_append, List.length_replicate]
    omega
  obtain ⟨x, -, holds⟩ := IntegerModel.isTrueRequest_of_isModelOutput_requestOf s hs i
    (prompt := IntegerModel.windowOf p o) (output := [y]) (List.cons_ne_nil _ _)
    (fun position hposition => by
      obtain rfl : position = 0 := Nat.lt_one_iff.1 hposition
      show IntegerModel.programNextToken _ (IntegerModel.windowOf p o ++ []) = some y
      rw [List.append_nil]
      exact hy)
    (by rw [windowOf_of_length _ y len]; exact runs')
  exact ⟨x, holds⟩

/-- At the settings of the reference table of scales there are valid weights at which no prompt and
output meet `CanServe`: `haltingWeights`, at whose index no request is true (`Cm.empty_language`,
Cm/RelTrueExp.lean). At these weights the statement on completeness says nothing, and the one on
zero-knowledge speaks of the commitment alone. -/
theorem canServe_nowhere_atHaltingWeights (prompt output : List Token) :
    ¬ CanServe referenceSettings haltingWeights prompt output := fun h =>
  let ⟨x, holds⟩ := exists_isTrueRequest_of_canServeAtIndex Cm.sRef Cm.lawful_sRef _
    ((canServe_weightsOfIndex_iff Cm.lawful_sRef (settingsAreValid_settingsOf Cm.lawful_sRef) rfl
      _ _ _).1 h)
  Cm.empty_language x ((Cm.paper_iff _ _ _ _).2 holds)

end VerifiableInference

#print axioms VerifiableInference.referenceSettings_valid
#print axioms VerifiableInference.requestOf_ofFn
#print axioms VerifiableInference.requestOfTokens_map_val
#print axioms VerifiableInference.modelNextToken_atReferenceSettings
#print axioms VerifiableInference.canServe_atReferenceSettings
#print axioms VerifiableInference.canServe_atAttentionWeights
#print axioms VerifiableInference.windowOf_of_length
#print axioms VerifiableInference.exists_isTrueRequest_of_canServeAtIndex
#print axioms VerifiableInference.canServe_nowhere_atHaltingWeights
#print axioms VerifiableInference.tokens_zerosThenOne
#print axioms VerifiableInference.tokens_allOnes
#print axioms VerifiableInference.modelNextToken_reads_layer
#print axioms VerifiableInference.modelNextToken_reads_earlier_token
