-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDTopProofs.lean: the proofs of Cb/Ld/LdLayDTop.lean's three statements: applications of
`Cb.ldReqRefLay_data`, of `Cb.ldReqStdAny`, and of the lemmas under `Cb.ldObjRefT_hyp` and
`Cb.ldObjRefT_langs`. What is said and what is not: the head of Cb/Ld/LdLayDTop.lean.

Main names (statements and hypotheses: Cb/Ld/LdLayDTop.lean):
  `ldReqRefU`: from `LdReqRefDU` to `LdReqRefDSA`.
  `ldObjRefU_hyp`: from `Z.HypRefU` to `Z.HypRef`.
  `ldObjRefU_langs`: the two languages, from `Z.HypRefU`.
-/
import Cb.Ld.LdLayDTop
import Cb.Ld.LdLayDProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

theorem ldReqRefU : Spec.ldReqRefU := by
  intro F E Kc _ _ _ _ _ pp _ R core first b L T qφ q κ h
  obtain ⟨l1, l2, l3⟩ := ldReqRefLay_data
    F E Kc pp R _ first b L T LdLayQ.ok LdLayQ.ok_sound h.duty.model h.std.2.1 h.std.2.2 h.layD
  exact
    { duty := h.duty, std := h.std, deg := h.deg, ev := h.ev, tie := h.tie, own := h.own
      lay := l1, layT := l2, layB := l3
      fmt := h.fmt
      bFirst := h.bFirst, bSegs := h.bSegs, bTail := h.bTail, bLast := h.bLast }

theorem ldObjRefU_hyp :
    Spec.ldObjRefU_hyp := fun F E Fp _ _ _ _ _ _ _ _ Kc p _ Z _ L R core first b Ls T qφ q κ V p₀ plR h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, reqIs := h.reqIs, wfOK := ldWfE_okStd F E Fp Z.Zw V p L h.wfS,
    sndOK := h.sndOK, own₀ := h.own₀
    req := ldReqStdAny F E Kc p R core first b Ls T qφ q κ
      (ldReqRefU F E Kc p R core first b Ls T qφ q κ h.req)
    pl := ldRefPlan_hyp F E Kc Z.R R p₀ plR h.onIs h.places h.pl₁, pK := h.pK, p₁ := h.p₁,
      p₂ := h.p₂, p₃ := h.p₃, p₁B := h.p₁B, p₂B := h.p₂B, p₃B := h.p₃B }

theorem ldObjRefU_langs :
    Spec.ldObjRefU_langs := fun _ _ _ _ _ _ _ _ _ _ _ _ _ Z _ _ R _ _ _ _ _ _ _ _ _ _ _ h =>
  ldLangs_at Z.R.W.Cf R.Cf (congrArg LdReqPack.Cf h.reqIs) h.req.duty.langs

end Cb
