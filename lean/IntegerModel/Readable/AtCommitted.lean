-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Readable/AtCommitted.lean: `IntegerTransformer.model`
(IntegerModel/Model.lean) at the arrays made from settings and weights of the library.
`modelOf m`: that function at the arrays of IntegerModel/Readable/Exists.lean.
`modelOf_eq`: it gives the answers of `IntegerModel.programNextToken m` (IntegerModel/Reply.lean).
`isReply_iff_model`: "the reply is the model's" means that the request covers at least one token and
that `modelOf m`, applied token by token after the request's context
(IntegerModel/Readable/Tie.lean: `greedy`), returns the checked tokens.
-/
import IntegerModel.Readable.Exists

set_option autoImplicit false

namespace IntegerModel.Readable

open Inst.Model

/-- `IntegerTransformer.model` at the arrays made from the settings and weights of `m` and from the
five fixed tables. -/
def modelOf (m : IntegerModel.Committed) : Array ℕ → Option ℕ := IntegerTransformer.model
    (settingsArrays ppref m.settings) (tablesArrays ppref) (weightsArrays ppref m.weights.val)

theorem modelOf_eq (m : IntegerModel.Committed) (ctx : List IntegerModel.Token) : modelOf m
    (nums ctx) = (IntegerModel.programNextToken m ctx).map fun y => y.val :=
  model_eq_programNextToken m _ _ _ (feeds_of m) ctx

/-- `IsReply` in terms of `modelOf`, for every `m` and every request. -/
theorem isReply_iff_model (m : IntegerModel.Committed) (x : IntegerModel.Request) :
    IntegerModel.IsReply m x ↔ x.r < x.e ∧ greedy (modelOf m) (nums (IntegerModel.promptOf x))
        (x.e - x.r) = some (vals (IntegerModel.replyOf x)) :=
  isReply_iff_greedy m _ _ _ (feeds_of m) x

end IntegerModel.Readable
