-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaProofs.lean: the proof of the statement of Cb/Ld/LdKappa.lean.

Main names:
  `ldKappa`: one bound κ on the round errors of the five lists (statement and hypotheses:
    Cb/Ld/LdKappa.lean; by Cb/Ld/LdKappaObj.lean, Cb/Ld/LdKappaTow.lean, Cb/Req1/LdReqRefZk.lean).

The five lists: told in the head of Cb/Ld/LdKappa.lean, under "Why:".

Limits: what is said and what is not: the head of Cb/Ld/LdKappa.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappa

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

/-- "Every round's error of the request, as a probability, is at most κ" (`P.r.Below κ`) goes along
an equation between packs. -/
theorem ldKappa_pack {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (P P' : LdReqPack F E) (e : P = P') (κ : ℝ≥0∞) (h : P'.r.Below κ) : P.r.Below κ := e ▸ h

theorem ldKappa : Spec.ldKappa := by
  intro F E _ _ _ _ _ Kc p Z L R core first a₁ more hm b Ls T qφ q κ h hK
  have hR : Z.R.r.Below κ :=
    ldKappa_pack Z.R.toLdObjD.pack _ h.reqIs κ
      (ldReqRefK_reqBelow F E Kc R _ first a₁ more hm b Ls T κ
        (((ldSeg_below_named E Kc κ).1 _ first).2 h.req.bFirst) h.req.bMore
        (ldReqRefFinal_nums E Kc _ _ _ Ls κ h.req.bSegs)
        (ldSegRefAll_below E Kc _ T.A T.St₁ T.fz T.Az κ h.req.bTail) h.req.bLast)
  exact ldKappa_objR Z.R κ hK.wf hK.lin (ldKappa_pre _ Z.tw₁ κ h.p₁.isT hK.t₁.bridge hK.t₁.tow)
    (ldKappa_pre _ Z.tw₂ κ h.p₂.isT hK.t₂.bridge hK.t₂.tow)
    (ldKappa_pre _ Z.tw₃ κ h.p₃.isT hK.t₃.bridge hK.t₃.tow) hK.link
    (ldKappa_pre _ Z.twK κ h.pK.isT hK.tK.bridge hK.tK.tow) hR hK.linB
    (ldKappa_pre _ Z.tw₁B κ h.p₁B.isT hK.t₁B.bridge hK.t₁B.tow)
    (ldKappa_pre _ Z.tw₂B κ h.p₂B.isT hK.t₂B.bridge hK.t₂B.tow)
    (ldKappa_pre _ Z.tw₃B κ h.p₃B.isT hK.t₃B.bridge hK.t₃B.tow)

end Cb
