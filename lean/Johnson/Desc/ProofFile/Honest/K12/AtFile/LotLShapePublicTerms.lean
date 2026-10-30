-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapePublicTerms.lean

It states no goal. No property of the protocol is claimed.

WHAT THE FIRST CHAIN's LAST CODE SWITCH SENDS, AS FUNCTIONS
OF THE REQUEST's SHAPE (AND THE CODES). Three definitions with code; no theorem.

  `targetOfShape`       where the last switch leads
  `maskNoticeOfShape`   the fresh mask's announcement
  `treesOfFinish`       the trees of the sending of the two

Limits. Definitions. That a state's frame has this target is LotLShapePublic.lean's. Nothing on completeness, soundness
or hiding.
-/
import Johnson.Desc.Own.Trees
import OnBytes.Iop.Req

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.LotL
open OnBytes (OracleNotice TreeLay SwitchTarget Codes foldMaskNotice ioppFoldShape reqGroups)
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc (Own.treesMade)

/-- Where the last switch leads, off the request's shape. -/
def targetOfShape (shape : ReqShape) : SwitchTarget :=
  ((reqGroups shape).getD shape.link.length {}).target

/-- The fresh mask's announcement, off the request's shape. -/
def maskNoticeOfShape (shape : ReqShape) : OracleNotice :=
  foldMaskNotice (ioppFoldShape
    { code := shape.code, maskCode := shape.maskCode
      k := ((reqGroups shape).getD shape.link.length {}).k
      h := ((reqGroups shape).getD shape.link.length {}).h } {})

/-- The trees of the last switch's sending. -/
def treesOfFinish (shape : ReqShape) (codes : Codes) : Option TreeLay :=
  Own.treesMade codes
    #[⟨(targetOfShape shape).shape, (targetOfShape shape).leafClass⟩, maskNoticeOfShape shape]

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.targetOfShape
#print axioms ProofFile.Honest.K12.LotL.maskNoticeOfShape
#print axioms ProofFile.Honest.K12.LotL.treesOfFinish
