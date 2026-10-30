-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Arrays/OfIndex.lean

Weights as arrays compared with the index of the argument system, a matrix of digits (`Cm.Idx`,
Cm/RelBase.lean), and settings compared with the library's tables of scales (`Cm.Scales`,
Cm/Rel2.lean).
`scalesOf`, `settingsOf`: from settings to a table of scales and back. Valid settings give a lawful
table, a lawful table gives valid settings, and at valid settings
`settingsOf (scalesOf settings) = settings`. So the valid settings are exactly the settings of
lawful tables (`settingsAreValid_iff`), and different valid settings have different tables
(`scalesOf_injective`). The other round trip does not give every table back (an argument, no theorem
states it): a table has 72 numbers more, of which IntegerModel/Arrays/OfTensors.lean tells.
`weightsOfIndex`, at valid settings: the weights that a matrix of digits holds, as arrays.
`indexOfWeights`, at valid settings: a matrix of digits that holds the given weights, with 0 at
every entry at which no byte of a weight lies (by a reading of `Layout.matrixOf`,
Inst/Model/MatrixOf.lean; no theorem).
`weightsOfIndex_indexOfWeights`: its weights are the given ones. By a reading of the layout
(Cm/RelBase.lean), and no theorem, `weightsOfIndex` is not one to one. Which indices have the same
weights: IntegerModel/Arrays/SameTensors.lean.
`modelNextToken_weightsOfIndex`, `modelNextToken_atScales`, `modelNextToken_eq`: at valid settings
(or at the settings of a lawful table), on every list of tokens, `modelNextToken` equals the
library's model function at the table of the settings and the index of the weights
(`IntegerModel.programNextToken`, IntegerModel/Reply.lean).
`modelNextToken_none_of_token`: on a list with a number that is no token it is `none`.
An error common to the two functions is not detected by their equality.
`exists_valid_settings`, `nonempty_modelWeights`: there are valid settings, and weights at each.
-/
import IntegerModel.Arrays.ToTensors
import IntegerModel.TrueRequest
import Cm.Rel2Guards

set_option autoImplicit false

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference

open Inst.Model IntegerModel.Readable IntegerModel.Runnable Back

/-! ## 1. Settings and tables of scales -/

/-- A table of scales for the given settings (`ppBack`, IntegerModel/Arrays/ToTensors.lean). -/
def scalesOf (settings : IntegerTransformer.Settings) : Cm.Scales :=
  ⟨(ppBack settings).w, (ppBack settings).nf⟩

/-- The settings of a table of scales: the sizes of the model and the table's numbers, but for the
72 that the model does not read (`settingsArraysOf`, IntegerModel/Arrays/OfTensors.lean). -/
def settingsOf (scales : Cm.Scales) : IntegerTransformer.Settings :=
  settingsArraysOf ppref ⟨scales.w, scales.nf, AcceptancePolicy.exact⟩

/-- Valid settings give a lawful table. -/
theorem lawful_scalesOf {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) : (scalesOf settings).Lawful :=
  (Cm.lawful_iff _).2 (lawful_ppBack valid)

/-- A lawful table gives valid settings. -/
theorem settingsAreValid_settingsOf {scales : Cm.Scales} (lawful : scales.Lawful) :
    settingsAreValid (settingsOf scales) = true :=
  settingsAreValid_arrays _ lawful.toPP

/-- From valid settings to a table and back: the same settings. -/
theorem settingsOf_scalesOf {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) : settingsOf (scalesOf settings) = settings :=
  settings_back valid

/-- The valid settings are exactly the settings of lawful tables. -/
theorem settingsAreValid_iff (settings : IntegerTransformer.Settings) :
    settingsAreValid settings = true
      ↔ ∃ scales : Cm.Scales, scales.Lawful ∧ settingsOf scales = settings := by
  constructor
  · intro valid
    exact ⟨scalesOf settings, lawful_scalesOf valid, settingsOf_scalesOf valid⟩
  · rintro ⟨scales, lawful, rfl⟩
    exact settingsAreValid_settingsOf lawful

/-- Different valid settings have different tables. -/
theorem scalesOf_injective {settings settings' : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (valid' : settingsAreValid settings' = true)
    (equal : scalesOf settings = scalesOf settings') : settings = settings' := by
  rw [← settingsOf_scalesOf valid, equal, settingsOf_scalesOf valid']

/-- There are valid settings: those of the library's reference table. -/
theorem exists_valid_settings :
    ∃ settings : IntegerTransformer.Settings, settingsAreValid settings = true :=
  ⟨settingsOf Cm.sRef, settingsAreValid_settingsOf Cm.lawful_sRef⟩

/-! ## 2. Weights and matrices of digits -/

section Maps
variable {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
include valid

/-- The weights that a matrix of digits holds, as arrays. -/
def weightsOfIndex (index : Cm.Idx) : ModelWeights settings :=
  ⟨weightsArraysOf ppref index.weights, by
    have h := weightsAreValid_arrays (ppBack settings) (lawful_ppBack valid) index.weights
      index.index.property
    rw [settings_back valid] at h
    exact h⟩

/-- A matrix of digits that holds the given weights, with 0 wherever no byte of a weight lies (by a
reading of `Layout.matrixOf`, Inst/Model/MatrixOf.lean; no theorem). -/
def indexOfWeights (weights : ModelWeights settings) : Cm.Idx :=
  Cm.Idx.ofIndex ⟨weightsTo weights.val, wf_weightsTo valid weights.property⟩

/-- At valid settings, the weights that the matrix of given weights holds are the given ones. By a
reading of the layout, and no theorem, only this round trip holds: from a matrix to weights and
back, the tensors are kept (`index_indexOfWeights`, IntegerModel/Arrays/SameTensors.lean), not every
entry of the matrix. -/
theorem weightsOfIndex_indexOfWeights (weights : ModelWeights settings) :
    weightsOfIndex valid (indexOfWeights valid weights) = weights := by
  apply Subtype.ext
  show weightsArraysOf ppref (indexOfWeights valid weights).weights = weights.val
  unfold indexOfWeights
  rw [Cm.weights_ofIndex]
  exact weights_back valid weights.property

/-- At valid settings there are weights. -/
theorem nonempty_modelWeights : Nonempty (ModelWeights settings) :=
  ⟨weightsOfIndex valid (Cm.Idx.ofIndex ScalesSanity.iZero)⟩

end Maps

/-! ## 3. The model function -/

/-- For every lawful table of scales and every index: at the table's settings and the index's
weights, `modelNextToken` is the library's model function at that table and index, on every list of
tokens. -/
theorem modelNextToken_atScales (scales : Cm.Scales) (lawful : scales.Lawful) (index : Cm.Idx)
    (tokens : List IntegerModel.Token) :
    modelNextToken (settingsOf scales)
        (weightsOfIndex (settingsAreValid_settingsOf lawful) index) (tokens.map Fin.val)
      = (IntegerModel.programNextToken (IntegerModel.committedOf scales lawful index)
          tokens).map Fin.val :=
  model_eq_programNextToken _ _ _ _
    (feeds_arrays (IntegerModel.committedOf scales lawful index)) tokens

/-- On a list with a number that is no token, `modelNextToken` is `none`. With the theorems on lists
of tokens this fixes it on every list of numbers: at valid settings the vocabulary's size is that of
the type `IntegerModel.Token`. -/
theorem modelNextToken_none_of_token {settings : IntegerTransformer.Settings}
    (weights : ModelWeights settings) (tokens : List ℕ)
    (large : ∃ token ∈ tokens, settings.vocabulary ≤ token) :
    modelNextToken settings weights tokens = none := by
  obtain ⟨token, member, le⟩ := large
  obtain ⟨position, hp, rfl⟩ := List.getElem_of_mem member
  refine model_none_of_token _ _ _ _ fun a => Nat.not_lt.2 le ?_
  exact a position (by rw [List.size_toArray]; exact hp)

section Model
variable {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
include valid

/-- At valid settings the vocabulary's size is that of the type `IntegerModel.Token`. -/
theorem vocabulary_eq : settings.vocabulary = ppref.V :=
  (valid_numbers valid).2.2.2.2.2.2.2.2.2.1

/-- At valid settings, the arrays of an index hold the numbers of the library's committed model at
the table of the settings and that index. -/
theorem feeds_weightsOfIndex (index : Cm.Idx) :
    Feeds (IntegerModel.committedOf (scalesOf settings) (lawful_scalesOf valid) index) settings
      lookupTables (weightsOfIndex valid index).val := by
  have h := feeds_arrays
    (IntegerModel.committedOf (scalesOf settings) (lawful_scalesOf valid) index)
  have e : settingsArraysOf ppref
      (IntegerModel.committedOf (scalesOf settings) (lawful_scalesOf valid) index).settings
        = settings := settings_back valid
  rw [e] at h
  exact h

/-- For all valid settings and every index: at the index's weights, `modelNextToken` is the
library's model function at the table of the settings and that index, on every list of tokens. -/
theorem modelNextToken_weightsOfIndex (index : Cm.Idx) (tokens : List IntegerModel.Token) :
    modelNextToken settings (weightsOfIndex valid index) (tokens.map Fin.val)
      = (IntegerModel.programNextToken
          (IntegerModel.committedOf (scalesOf settings) (lawful_scalesOf valid) index)
          tokens).map Fin.val :=
  model_eq_programNextToken _ _ _ _ (feeds_weightsOfIndex valid index) tokens

/-- For all valid settings and all weights: `modelNextToken` is the library's model function at the
table of the settings and the matrix of the weights, on every list of tokens. -/
theorem modelNextToken_eq (weights : ModelWeights settings) (tokens : List IntegerModel.Token) :
    modelNextToken settings weights (tokens.map Fin.val)
      = (IntegerModel.programNextToken
          (IntegerModel.committedOf (scalesOf settings) (lawful_scalesOf valid)
            (indexOfWeights valid weights))
          tokens).map Fin.val := by
  have h := modelNextToken_weightsOfIndex valid (indexOfWeights valid weights) tokens
  rw [weightsOfIndex_indexOfWeights] at h
  exact h

end Model

end VerifiableInference
