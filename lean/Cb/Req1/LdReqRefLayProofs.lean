-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefLayProofs.lean: the proofs of the statements of Cb/Req1/LdReqRefLay.lean. By the
rules move by move (Cb/Req1/LdSegCarry.lean), through a segment with one group
(Cb/Req1/LdSegWholeAfter.lean, Cb/Req1/LdSegCarryClose.lean), through the closed body
(Cb/Req1/LdSegRefTenLook.lean: `ldSegRefX_out`), one statement of Cb/Req1/LdReqRefZk.lean
(`ldReqRefK_after`), and `ldReqRefZkP` (Cb/Req1/LdReqRefZkP.lean).
Terms: lean/GLOSSARY.md.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldReqRefLay` can be met
   together. -/
import Cb.Req1.LdReqRefLay

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

theorem ldReqRefLay_new : Spec.ldReqRefLay_new := by
  intro E Kc _ _ I a S g h Y
  show ((S.K.seg S.l S.Qc).pre S.entry rfl).After Y g
  rw [ldReqRefK_after]
  exact ldSegAfter_new E Kc _ S.K.R.c1 _ S.K.kinds S.l S.Qc _ g h.1 h.2

theorem ldReqRefLay_after : Spec.ldReqRefLay_after := by
  intro E Kc _ _ I a b L base
  induction L with
  | nil => intro g h; rw [LdRefL.Laid] at h; rw [LdRefL.segs, LdSegs.After]; exact h
  | snoc L S ih =>
      intro g h
      rw [LdRefL.Laid] at h
      rw [LdRefL.segs, LdSegs.After]
      rcases h with h | ⟨g', hg', hc⟩
      · exact ldReqRefLay_new E Kc _ _ S g h _
      · exact hc _ (ih g' hg')

theorem ldReqRefLay_mono : Spec.ldReqRefLay_mono := by
  intro E Kc _ _ I A pp X X' hX ⟨hne, W, F, κ, RdL, h1, h2, h3, h4⟩
  exact ⟨hne, W, F, κ, RdL, h1, h2,
    { h3 with lk := hX _ h3.lk, f0 := hX _ h3.f0, f := fun i hi => hX _ (h3.f i hi) },
    { h4 with
      passL := { h4.passL with inBase := hX _ h4.passL.inBase },
      passT := { h4.passT with inBase := hX _ h4.passT.inBase } }⟩

theorem ldReqRefLay_segs : Spec.ldReqRefLay_segs := by
  intro E Kc _ _ I a b L pp base
  induction L with
  | nil => intro _; rw [LdRefL.ZkP]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.Lay] at h
      rw [LdRefL.ZkP]
      exact ⟨ih h.1,
        ldReqRefLay_mono E Kc _ S.A pp _ _
          (fun f ⟨g, hg, he⟩ => he _ (ldReqRefLay_after E Kc _ _ _ L base g hg)) h.2⟩

theorem ldReqRefLay_enters : Spec.ldReqRefLay_enters := by
  intro E Kc _ _ I a S g K' kc' put' h Y hY
  unfold LdRefS.entry
  exact segCarry_step a S.A.V.Fp.s0 S.f S.g S.m S.back Y g K' kc' put' hY h

theorem ldReqRefLay_cross : Spec.ldReqRefLay_cross := by
  intro E Kc _ _ pp _ I a S _ W F κ own Mk _ _ val RdN RrN g' hA hG hF hq hM hL hO hT
    c1 c2 c3 c4 c5 c6 hE Y hY
  show ((S.K.seg S.l S.Qc).pre S.entry rfl).After Y _
  rw [ldReqRefK_after]
  exact segWide_segOne _ S.K.R.c1 _ S.K.kinds S.l S.Qc _ W.Rd2 W.Rr2 (S.A.own2 own) Mk
    (S.A.val2 val) RdN RrN c1 c2 c3 c4 c5 c6
    (ldSegRefX_out E Kc pp _ S.A W F κ _ own Mk val S.K.St₁ S.K.fz S.K.Az hA hG hF
      ⟨hE Y hY, hq.quiet, hq.send1, hq.send3⟩ hM hL hO hT)

theorem ldReqRefLay : Spec.ldReqRefLay := by
  intro F E Kc _ _ _ _ _ pp _ R a first a₁ more hm b L T Rd Rr hL hT hn hZ hTie
    hO hRd zL zT ⟨g, hg, hB⟩
  exact ldReqRefZkP F E Kc pp R a first a₁ more hm b L T Rd Rr hL hT hn hZ hTie hO
    hRd (ldReqRefLay_segs E Kc _ _ _ L pp _ zL)
    (ldReqRefLay_mono E Kc _ T.A pp _ _
      (fun f ⟨g, hg, he⟩ => he _ (ldReqRefLay_after E Kc _ _ _ L _ g hg)) zT)
    (hB _ (ldReqRefLay_after E Kc _ _ _ L _ g hg))

end Cb
