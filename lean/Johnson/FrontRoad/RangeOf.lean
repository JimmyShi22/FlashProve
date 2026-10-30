-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/RangeOf.lean: the matrix of given weights is in range. The library's map from
weights to the committed matrix (FlashProve.backThe, Johnson/Goal/Conditions/BindsAtThe.lean) has,
at all settings and all weights, its values in the set of matrices that hold an index (Flat.InRange,
Johnson/Flat/LedgerClaim.lean).
Terms and the limits that go with any quote: Spec.lean.

What this file proves.
  inRange_matrixOf  the matrix of an index holds an index (Flat.holds_matrixOf,
                    Johnson/Flat/ThreeFull.lean).
  inRange_backO     if the settings are valid, the matrix of given weights is in range.
  inRange_backThe   at all settings, backThe Z s w is in range.

Limits. The theorems say that the map's values are in the range. Nothing is said on whether the
premises of index privacy can hold on that range, and nothing on hiding. At settings that are not
valid, backThe returns one fixed matrix for all weights.

How it fits. A statement of index privacy on a range ok of indices says nothing of an index outside
it. At the shell frontAt at the built description the inner indices are matrices and the outer
indices are weights. Where the map idx is backThe and the range is Flat.InRange, every weight's
index is in the range. So the premise range of LeftToAsk (AtDescription.lean) holds there, and a
statement on that range is about all weights, with the limit above on settings that are not valid
(AtWeights.lean, Joined.lean).
-/
import Johnson.Goal.Conditions.BindsAtThe

set_option autoImplicit false

noncomputable section

namespace OnBytes.FrontRoad
open VerifiableInference VerifiableInference.OnPublicFiles Inst.Model

/-- The matrix of an index is in range: it holds that index. -/
theorem inRange_matrixOf (i : Cm.Idx) : Flat.InRange (Flat.matrixOf i) :=
  ⟨i, Flat.holds_matrixOf i⟩

/-- If the settings are valid, the matrix of given weights (backO) is in range. -/
theorem inRange_backO {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (w : ModelWeights settings) :
    Flat.InRange (VerifierAndGoals.Fit.backO valid w) :=
  inRange_matrixOf _

/-- At all settings and all weights, backThe Z s w is in range. At settings that are not valid it is
one fixed matrix. -/
theorem inRange_backThe (Z : VerifierAndGoals.PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) :
    Flat.InRange (FlashProve.backThe Z s w) := by
  unfold FlashProve.backThe
  split
  · exact inRange_backO _ w
  · exact inRange_matrixOf _

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.inRange_backThe
