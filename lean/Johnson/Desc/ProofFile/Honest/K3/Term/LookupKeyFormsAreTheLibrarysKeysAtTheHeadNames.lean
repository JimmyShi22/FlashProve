-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtTheHeadNames.lean: one definition, for the
helpers of LookupKeyFormsAreTheLibrarysKeysAtTheHead.lean: which segment of the library's H.segH
(OnBytes/Tie/Pv/Lookup/Ends/H.lean) a key of the output head's kind is. A WORKING FILE.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.Kinds.HeadIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc.Kinds.Head (PlaceKey)

/-- Which segment of the library's key vector a key of the output head's kind is. -/
def segmentName : PlaceKey → String
  | .inl .remLow => "NF"
  | .inl .remHigh => "NFH"
  | .inl .clamp => "CNF"
  | .inl .digits => "ROW"
  | .inr .marginTop => "HD0"
  | .inr .marginMid => "HD1"
  | .inr .marginLow => "HD2"
  | .inr .tableA => "HE0"
  | .inr .tableB => "HE1"

end ProofFile.Honest.K3.Term
