-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/OneSlotAt.lean: where a one-chain description's written rounds are the library's
written constant frFmt | srFmt (evaluated at the public files of two stored sets that this text
does not tie to the release, in a file of evaluations that is not named here), its typed rounds'
data ARE the library's dsFull | dsSmall (two theorems). A third: the typed stored
openings are the untyped ones field by field (these were held by value against frD.xs | srD.xs, in
the same file of evaluations). By unfolding.
-/
import Johnson.Desc.Link.OneSlotTyped
import OnBytes.Flat.LinkSibAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
variable {Xi : Type}

theorem dsOf_full (F : OneChainFileDescription Xi) (file : String) (h : F.roundsOf file = .ok OnBytes.Slice.frFmt) :
    F.dsOf file = .ok OnBytes.Flat.dsFull := by
  unfold OneChainFileDescription.dsOf
  rw [h]
  rfl

theorem dsOf_small (F : OneChainFileDescription Xi) (file : String) (h : F.roundsOf file = .ok OnBytes.Slice.srFmt)
    :
    F.dsOf file = .ok OnBytes.Flat.dsSmall := by
  unfold OneChainFileDescription.dsOf
  rw [h]
  rfl

/-- The typed openings are the untyped ones, field by field. -/
theorem xsTyped_fields (F : OneChainFileDescription Xi) :
    F.xsTyped.map (fun o => (o.round, o.which, o.from_, o.count)) = F.xsOf := by
  unfold OneChainFileDescription.xsTyped OneChainFileDescription.xsOf
  simp [List.map_flatMap, Function.comp_def]

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.dsOf_full
#print axioms VerifiableInference.Desc.dsOf_small
#print axioms VerifiableInference.Desc.xsTyped_fields
