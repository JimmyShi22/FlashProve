-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Arrays/SameModel.lean

`modelNextToken` (VerifiableInference/ModelWeights.lean) and `IntegerModel.nextToken`
(IntegerModel/ModelOutput.lean) are the same function, on every list of numbers. Both are
`IntegerTransformer.model`, at two forms of arrays for one table of scales and one index: the second
form keeps the table's shifts of router and routed expert in the dense layers and fills their
routers and routed experts with zeros; by reading, and no theorem, it does not pass the tests of
VerifiableInference/ModelWeights.lean.
The theorems take a lawful table of scales, valid settings, and
`tie : settingsOf scales = settings`. Two uses: a table with its settings (`tie := rfl`), and
settings with their table (`tie := settingsOf_scalesOf valid`).
`modelNextToken_eq_nextToken`, `modelNextToken_eq_nextToken_of_weights`: at the weights of an index,
and at given weights.
`canServe_weightsOfIndex_iff`, `canServe_iff`: so `CanServe` (VerifiableInference/CanServe.lean) is
`IntegerModel.CanServeAtIndex`.
-/
import IntegerModel.Arrays.OfIndex
import VerifiableInference.CanServe
import IntegerModel.ModelOutput

set_option autoImplicit false

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference

open Inst.Model

/-- At a lawful table of scales and an index: a function on lists of numbers that agrees with the
library's model function on lists of tokens, and is `none` on a list with a number that is no token,
is `IntegerModel.nextToken` at that table and the tensors of that index. -/
theorem eq_nextToken (next : List ℕ → Option ℕ) (scales : Cm.Scales) (lawful : scales.Lawful)
    (index : Cm.Idx)
    (onTokens : ∀ tokens : List IntegerModel.Token, next (tokens.map Fin.val)
      = (IntegerModel.programNextToken (IntegerModel.committedOf scales lawful index)
          tokens).map Fin.val)
    (onOthers : ∀ tokens : List ℕ, (∃ token ∈ tokens, ppref.V ≤ token) → next tokens = none)
    (tokens : List ℕ) : next tokens = IntegerModel.nextToken scales index.index tokens := by
  rw [IntegerModel.nextToken_eq_programNextToken scales lawful]
  cases h : vocabularyTokens tokens with
  | some list =>
      have e : list.map Fin.val = tokens := map_val_of_vocabularyTokens tokens list h
      rw [← e]
      exact onTokens list
  | none =>
      obtain ⟨position, hp, hb⟩ := exists_large_of_vocabularyTokens_none tokens h
      exact onOthers tokens ⟨tokens[position], List.getElem_mem hp, Nat.le_of_not_lt hb⟩

section
variable {scales : Cm.Scales} (lawful : scales.Lawful) {settings : IntegerTransformer.Settings}
  (valid : settingsAreValid settings = true) (tie : settingsOf scales = settings)
include lawful tie

/-- At the weights of an index, on every list of numbers. -/
theorem modelNextToken_eq_nextToken (index : Cm.Idx) (tokens : List ℕ) :
    modelNextToken settings (weightsOfIndex valid index) tokens
      = IntegerModel.nextToken scales index.index tokens := by
  subst tie
  exact eq_nextToken _ scales lawful index (modelNextToken_atScales scales lawful index)
    (fun tokens large => modelNextToken_none_of_token _ tokens large) tokens

/-- At given weights and their matrix of digits, on every list of numbers. -/
theorem modelNextToken_eq_nextToken_of_weights (weights : ModelWeights settings)
    (tokens : List ℕ) :
    modelNextToken settings weights tokens
      = IntegerModel.nextToken scales (indexOfWeights valid weights).index tokens := by
  have h := modelNextToken_eq_nextToken lawful valid tie (indexOfWeights valid weights) tokens
  rw [weightsOfIndex_indexOfWeights] at h
  exact h

/-- Under `lawful`, `valid` and `tie` of this section, `CanServe` at the weights of an index is
`IntegerModel.CanServeAtIndex` at the table and the tensors of that index. -/
theorem canServe_weightsOfIndex_iff (index : Cm.Idx) (prompt output : List ℕ) :
    CanServe settings (weightsOfIndex valid index) prompt output
      ↔ IntegerModel.CanServeAtIndex scales index.index prompt output := by
  unfold CanServe IntegerModel.CanServeAtIndex
  rw [vocabulary_eq valid, modelNextToken_eq_nextToken lawful valid tie]

/-- Under `lawful`, `valid` and `tie` of this section, `CanServe` at given weights is
`IntegerModel.CanServeAtIndex` at the table and the tensors of their matrix of digits. -/
theorem canServe_iff (weights : ModelWeights settings) (prompt output : List ℕ) :
    CanServe settings weights prompt output
      ↔ IntegerModel.CanServeAtIndex scales (indexOfWeights valid weights).index prompt output := by
  unfold CanServe IntegerModel.CanServeAtIndex
  rw [vocabulary_eq valid, modelNextToken_eq_nextToken_of_weights lawful valid tie]

end

end VerifiableInference
