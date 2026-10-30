-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/Kinds/Send.lean.
A KNOW-ONLY LEMMA FOR EACH KIND OF MOVE. THE KIND «send» (LdSendD, Cb/Req1/LdSegKit.lean:153-192).
D3 LdSendD.HypK: four of Hyp's seven fields: none names d.D. K1 LdSendD.goodK. It also serves
LdSeg.snd and LdReq.first (LdSendD's outside any move).
«know» reads fair, list, evades (the library's own ldSendFam_into); isLocal reads laws
(ldSendFam_isLocal); the renaming is sigSum_step (no premise).
NO THIN DEFINITION OR PREMISE names a bundle, an honest side, a joint's exact relation or core. THE
CONTROLS AND EXAMPLES DO.

-/
import Cb.Thin.Kinds.Rules
import Cb.Req1.LdSegProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain

/-- D3. Four of `LdSendD.Hyp`'s seven fields, to the letter. -/
structure LdSendD.HypK {E Kc : Type} [Field E] {a : LdStage E Kc} (d : LdSendD a) : Prop where
  laws   : ∀ i, (d.N.om i).C.Laws
  fair   : d.Sd.Fair
  list   : ∀ i, (d.N.om i).ListLE (d.L i)
  evades : ∀ i, (d.N.om i).Evades

/-- K1. -/
theorem LdSendD.goodK {E Kc : Type} [Field E] {a : LdStage E Kc} (d : LdSendD a) (h : d.HypK) :
    d.link.GoodK :=
  (goodK_iff d.link).2
    (goodK₀_cf_in _ (a.S.over a.A) ((a.S.sum d.N).over (a.S.grow d.N a.A d.bk)) _ _
      (goodK₀_post (ldSendFam d.N d.Sd (a.St × a.S.Smp) (a.E₀.prod a.S.ext)) (a.S.over a.A)
        (d.N.over (d.N.pull (a.S.over a.A) (a.S.backN d.N d.bk))).cf
        ((a.S.sum d.N).over (a.S.grow d.N a.A d.bk)).cf
        (fun _ _ w => a.S.backN d.N d.bk (d.N.msgs w.1) w.2) d.link.ext
        (ldSendFamErr d.N d.Sd d.L, (0, ())) (a.S.mergeX d.N a.St) (a.S.mergeE d.N a.E₀)
        (fun _ w => a.S.splitW d.N d.Wp' w)
        ⟨⟨d.N.pt d.Sd⟩, ldSendFam_isLocal d.N d.Sd _ _ h.laws, fun _ _ _ _ _ => trivial,
          ldSendFam_into E d.N d.Sd Kc _ _ _ _ (a.S.over a.A) (a.S.backN d.N d.bk) d.L h.fair
            h.list h.evades⟩
        (stepK_of_step (sigSum_step E a.S d.N Kc a.St a.Wp d.Wp' a.E₀ a.A d.bk))
        fun _ _ _ _ _ => rfl))

/-! ## The controls -/

/-- (c1) the old Hyp gives HypK, by projections alone. -/
theorem LdSendD.hypK_of_hyp {E Kc : Type} [Field E] {a : LdStage E Kc} (d : LdSendD a)
    (h : d.Hyp) : d.HypK :=
  ⟨h.laws, h.fair, h.list, h.evades⟩

/-- (c2) ONE PROPOSITION, field by field: the same reduction, joints, extractor, list of errors. -/
example {E Kc : Type} [Field E] {a : LdStage E Kc} (d : LdSendD a) (h : d.Hyp) :
    (d.goodT h).know = (d.goodK (d.hypK_of_hyp h)).know := rfl
example {E Kc : Type} [Field E] {a : LdStage E Kc} (d : LdSendD a) (h : d.Hyp) :
    (d.goodT h).onOut = (d.goodK (d.hypK_of_hyp h)).onOut := rfl
example {E Kc : Type} [Field E] {a : LdStage E Kc} (d : LdSendD a) (h : d.Hyp) :
    (d.goodT h).isLocal = (d.goodK (d.hypK_of_hyp h)).isLocal := rfl
example {E Kc : Type} [Field E] {a : LdStage E Kc} (d : LdSendD a) (h : d.Hyp) :
    (d.goodT h).point = (d.goodK (d.hypK_of_hyp h)).point := rfl

end Cb

#check @Cb.LdSendD.goodK
#print Cb.LdSendD.HypK
