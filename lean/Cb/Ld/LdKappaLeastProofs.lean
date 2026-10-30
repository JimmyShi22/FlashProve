-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaLeastProofs.lean: the proofs of the three statements of Cb/Ld/LdKappaLeast.lean.

Main names (statements and hypotheses: Cb/Ld/LdKappaLeast.lean):
  `ldKappa_conv`: the way back from the five lists to the records (by Cb/Ld/LdKappaConvObj.lean,
    Cb/Ld/LdKappaConv.lean).
  `ldKappa_iff`: the records against the five lists, both ways.
  `ldKappaU_conv`: the way back for the record `Z.HypRefU`.

The records and the five lists: told in the head of Cb/Ld/LdKappaLeast.lean.

Limits: what is said and what is not: the head of Cb/Ld/LdKappaLeast.lean.
-/
import Cb.Ld.LdKappaLeast
import Cb.Ld.LdKappaProofs
import Cb.Ld.LdKappaConvObj
import Cb.Ld.LdLayDTopProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

theorem ldKappa_packTo {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (P P' : LdReqPack F E) (e : P = P') (κ : ℝ≥0∞) (h : P.r.Below κ) : P'.r.Below κ := e ▸ h

theorem ldKappa_conv : Spec.ldKappa_conv := by
  intro F E _ _ _ _ _ Kc p Z L R core first a₁ more hm b Ls T qφ q κ' κ h hB
  obtain ⟨hW, hL, h1, h2, h3, hK, hKc, hR, hBt, b1, b2, b3⟩ := ldKappaConv_objR Z.R κ hB
  obtain ⟨r1, r2, r3, r4, r5⟩ :=
    ldKappaConv_req R _ first a₁ more hm b Ls T κ (ldKappa_packTo Z.R.toLdObjD.pack _ h.reqIs κ hR)
  refine ⟨{ h with
            req :=
              { h.req with bFirst := r1, bMore := r2, bSegs := r3, bTail := r4, bLast := r5 } },
    ?_⟩
  exact
    { wf := hW, lin := hL
      t₁ := ⟨(ldKappaConv_pre _ Z.tw₁ κ h.p₁.isT h1).1, (ldKappaConv_pre _ Z.tw₁ κ h.p₁.isT h1).2⟩
      t₂ := ⟨(ldKappaConv_pre _ Z.tw₂ κ h.p₂.isT h2).1, (ldKappaConv_pre _ Z.tw₂ κ h.p₂.isT h2).2⟩
      t₃ := ⟨(ldKappaConv_pre _ Z.tw₃ κ h.p₃.isT h3).1, (ldKappaConv_pre _ Z.tw₃ κ h.p₃.isT h3).2⟩
      link := hK
      tK := ⟨(ldKappaConv_pre _ Z.twK κ h.pK.isT hKc).1, (ldKappaConv_pre _ Z.twK κ h.pK.isT hKc).2⟩
      linB := hBt
      t₁B :=
        ⟨(ldKappaConv_pre _ Z.tw₁B κ h.p₁B.isT b1).1, (ldKappaConv_pre _ Z.tw₁B κ h.p₁B.isT b1).2⟩
      t₂B :=
        ⟨(ldKappaConv_pre _ Z.tw₂B κ h.p₂B.isT b2).1, (ldKappaConv_pre _ Z.tw₂B κ h.p₂B.isT b2).2⟩
      t₃B :=
        ⟨(ldKappaConv_pre _ Z.tw₃B κ h.p₃B.isT b3).1, (ldKappaConv_pre _ Z.tw₃B κ h.p₃B.isT b3).2⟩ }

theorem ldKappa_iff :
    Spec.ldKappa_iff := fun F E _ _ _ _ _ Kc p Z L R core first a₁ more hm b Ls T qφ q κ' κ h =>
  ⟨fun hk => ldKappa F E Kc p Z L R core first a₁ more hm b Ls T qφ q κ hk.1 hk.2,
    fun hB => ldKappa_conv F E Kc p Z L R core first a₁ more hm b Ls T qφ q κ' κ h hB⟩

theorem ldKappaU_conv : Spec.ldKappaU_conv := by
  intro F E Fp _ _ _ _ _ _ _ _ Kc p _ Z _ L R core first b Ls T qφ q κ' κ V p₀ plR h hB
  obtain ⟨h1, h2⟩ := ldKappa_conv F E Kc p Z L R core first first.tgt (.nil first.tgt)
    (LdProg.all_nilK _ _) b Ls T qφ q κ' κ
    (ldObjRefU_hyp F E Fp Kc p Z L R core first b Ls T qφ q κ' V p₀ plR h) hB
  exact ⟨{ h with
           req :=
             { h.req with
               bFirst := h1.req.bFirst, bSegs := h1.req.bSegs,
               bTail := h1.req.bTail, bLast := h1.req.bLast } },
    h2⟩

end Cb
