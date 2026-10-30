-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- Statement and proof read once.
/-
ON PUBLIC DATA ALONE.
Johnson/Desc/ProofFile/Honest/K3/Term/PaddingRowsAtAttentionAreTheLibrarys.lean: the honest side of
the kind "lookup" (K3): at each of the twelve groups' attention, in the goals' scope, the row that a
call's padding keys hold is the padding value of the library's table (`PadEq`,
Johnson/Road/Lane5KvAll.lean). One theorem, by `padEq_in_scope`
(Johnson/HonestTrace/Joint/K3PadEqAttention.lean). It is a premise of
`lookupKeyFormsAreTheLibrarysKeysAtAttention`, wanted wherever a call has fewer keys in use than
places. Nothing on any property.
-/
import Johnson.Road.Lane5KvAll
import Johnson.HonestTrace.FullPlanes
import Johnson.Goal.Meaning.AttScope
import Johnson.Goal.Meaning.AttNumsScope
import Johnson.HonestTrace.Joint.K3PadEqAttention

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term

/-- **The verifier's padding rows at attention are the library's padding values**, in the goals'
scope. -/
theorem paddingRowsAtAttentionAreTheLibrarys
    {publicFiles : VerifierAndGoals.PublicFiles} {parameters : Inst.Model.ScalesAndPolicy} {layoutFile : Option ByteArray}
    {publicPart : OnBytes.Model.Verify.Public}
    (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart)
    {group : Nat} (groupBelowTwelve : group < 12) :
    OnBytes.Road.L5.PadEq (OnBytes.Road.Hd.shapeA publicPart group)
      (OnBytes.HonestTrace.fsAt publicPart group) :=
  OnBytes.Road.L5.PadAtAttention.padEq_in_scope inScope filesRead publicPartMade groupBelowTwelve


end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.paddingRowsAtAttentionAreTheLibrarys
