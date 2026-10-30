-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendFreshProofs.lean: the proofs of the statements of Cb/Ld/LdSendFresh.lean.
-/
import Cb.Ld.LdSendFresh
import Ior.KnowCollRulesMaskFrame
import Prob.LawKit
import Prob.LawEquiv

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (E : Type) [Field E]

theorem own_pad_of_uniform [Fintype E] : Spec.own_pad_of_uniform E :=
  fun _ _ _ _ _ _ _ h s w w' M M' k₀ k₀' => (h s w M k₀).trans (h s w' M' k₀').symm

omit [Field E] in
/-- a function of the sender's coins, in parts -/
theorem map_unif_own {N : Sig E} {W W' : Type} {D : N.Sender W W'} {Mb : Type} [Fintype Mb]
    [Nonempty Mb] (U : D.Own Mb) {γ : Type} (f : D.Mk → γ) :
    (unif D.Mk).map f =
      (unif (Mb × U.M0)).bind fun a => (unif U.Pd).map fun η => f (U.mk' a.1 a.2 η) := by
  rw [← map_unif_equiv U.κ.symm, PMF.map_comp, map_unif_prod]
  rfl

theorem own_blind : Spec.own_blind E := by
  classical
  intro N W W' D Mb _ _ U Sd Kc rd put hU s w w'
  rw [map_unif_own E U, map_unif_own E U]
  exact congrArg _ (funext fun a => hU.pad s w w' a.1 a.1 a.2 a.2)

theorem ldSendFam_fresh : Spec.ldSendFam_fresh E := by
  classical
  intro N Sd X W W' E₀ D t Ri Mb _ _ U Kc rd put hU hZ x y w _ ρ _ T hT
  obtain ⟨s, u, u'⟩ := ρ
  obtain ⟨body, hbody⟩ := hU.lay
  let sn : D.Mk × D.Nn.Rnd → View (ldSendFam N Sd X E₀) × (X × N.Smp) × Kc :=
    (ldSendFamHon Sd X E₀ D).seen (fun v => rd (N.msgs v.1) v.2) w x (s, u, u') T
  let G' : (Mb × U.M0) × (U.Pd × D.Nn.Rnd) → View (ldSendFam N Sd X E₀) × (X × N.Smp) × Kc :=
    fun a => sn (U.mk' a.1.1 a.1.2 a.2.1, a.2.2)
  let F' : ((Mb × Mb) × U.M0) × (U.Pd × D.Nn.Rnd) →
      View (ldSendFam N Sd X E₀) × (X × N.Smp) × Kc := fun a =>
    ((sn (U.mk' a.1.1.1 a.1.2 a.2.1, a.2.2)).1,
      (sn (U.mk' a.1.1.1 a.1.2 a.2.1, a.2.2)).2.1,
      put a.1.1.2 (sn (U.mk' a.1.1.1 a.1.2 a.2.1, a.2.2)).2.2)
  have hk : ∀ k : D.Mk, U.mk' (U.κ k).1.1 (U.κ k).1.2 (U.κ k).2 = k := fun k =>
    U.κ.symm_apply_apply k
  have hk' : ∀ M k₀ η, U.κ (U.mk' M k₀ η) = ((M, k₀), η) := fun M k₀ η => U.κ.apply_symm_apply _
  let eR : D.Mk × D.Nn.Rnd ≃ (Mb × U.M0) × (U.Pd × D.Nn.Rnd) :=
    { toFun := fun c => ((U.κ c.1).1, ((U.κ c.1).2, c.2))
      invFun := fun a => (U.mk' a.1.1 a.1.2 a.2.1, a.2.2)
      left_inv := fun c => Prod.ext (hk c.1) rfl
      right_inv := fun a => by
        show ((U.κ (U.mk' a.1.1 a.1.2 a.2.1)).1, ((U.κ (U.mk' a.1.1 a.1.2 a.2.1)).2, a.2.2)) = a
        rw [hk'] }
  let eL : (D.Mk × D.Nn.Rnd) × Mb ≃ ((Mb × Mb) × U.M0) × (U.Pd × D.Nn.Rnd) :=
    { toFun := fun a => ((((U.κ a.1.1).1.1, a.2), (U.κ a.1.1).1.2), ((U.κ a.1.1).2, a.1.2))
      invFun := fun b => ((U.mk' b.1.1.1 b.1.2 b.2.1, b.2.2), b.1.1.2)
      left_inv := fun a => Prod.ext (Prod.ext (hk a.1.1) rfl) rfl
      right_inv := fun b => by
        show ((((U.κ (U.mk' b.1.1.1 b.1.2 b.2.1)).1.1, b.1.1.2),
              (U.κ (U.mk' b.1.1.1 b.1.2 b.2.1)).1.2),
            ((U.κ (U.mk' b.1.1.1 b.1.2 b.2.1)).2, b.2.2)) = b
        rw [hk'] }
  have key : ∀ a : (Mb × Mb) × U.M0, ((unif (U.Pd × D.Nn.Rnd)).map fun b => F' (a, b)) =
      (unif (U.Pd × D.Nn.Rnd)).map fun b => G' ((a.1.2, a.2), b) := by
    rintro ⟨⟨Mo, M⟩, k₀⟩
    obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq _ _ (hU.pad s w w Mo M k₀ k₀)
    refine map_unif_prod_congr σ _ _ fun η => ?_
    obtain ⟨e₂, he₂⟩ := (hides_iff_equiv _ D.Nn (N.budT t)).1
      hZ (ldSendFamSet N Sd T) hT (D.put w (U.mk' Mo k₀ η)) (D.put w (U.mk' M k₀ (σ η)))
    refine map_unif_reindex e₂ _ _ fun r => ?_
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact ldSendFam_view_congr N Sd X E₀ T _ _
        (congrArg (fun a : N.Answ => (((), (a, ())) : Plains (N.sh Sd))) (hσ η))
        fun q hq => eq_of_heq (Sigma.mk.inj (he₂ r q hq)).2
    · show (x, fun a => (Sd.sd a s, D.ans Sd s w (U.mk' Mo k₀ η) a)) =
        (x, fun a => (Sd.sd a s, D.ans Sd s w (U.mk' M k₀ (σ η)) a))
      rw [hσ η]
    · show put M (rd (D.upM (D.put w (U.mk' Mo k₀ η))) (D.rest w)) =
        rd (D.upM (D.put w (U.mk' M k₀ (σ η)))) (D.rest w)
      rw [hbody, hbody, hU.over]
  have hh : (unif ((Mb × Mb) × U.M0)).map (fun a => (a.1.2, a.2)) = unif (Mb × U.M0) :=
    map_unif_prodMap (Prod.snd : Mb × Mb → Mb) (id : U.M0 → U.M0) map_snd_unif (PMF.map_id _)
  have hL : (unif ((D.Mk × D.Nn.Rnd) × Mb)).map
        (fun a => ((sn a.1).1, (sn a.1).2.1, put a.2 (sn a.1).2.2)) =
      (unif (((Mb × Mb) × U.M0) × (U.Pd × D.Nn.Rnd))).map F' := by
    rw [← map_unif_equiv eL, PMF.map_comp]
    refine congrArg (fun f => (unif ((D.Mk × D.Nn.Rnd) × Mb)).map f) (funext fun a => ?_)
    show _ = ((sn (U.mk' (U.κ a.1.1).1.1 (U.κ a.1.1).1.2 (U.κ a.1.1).2, a.1.2)).1,
        (sn (U.mk' (U.κ a.1.1).1.1 (U.κ a.1.1).1.2 (U.κ a.1.1).2, a.1.2)).2.1,
        put a.2 (sn (U.mk' (U.κ a.1.1).1.1 (U.κ a.1.1).1.2 (U.κ a.1.1).2, a.1.2)).2.2)
    rw [hk]
  have hR : (unif (D.Mk × D.Nn.Rnd)).map sn = (unif ((Mb × U.M0) × (U.Pd × D.Nn.Rnd))).map G' := by
    rw [← map_unif_equiv eR, PMF.map_comp]
    refine congrArg (fun f => (unif (D.Mk × D.Nn.Rnd)).map f) (funext fun c => ?_)
    show sn c = sn (U.mk' (U.κ c.1).1.1 (U.κ c.1).1.2 (U.κ c.1).2, c.2)
    rw [hk]
  show (unif ((D.Mk × D.Nn.Rnd) × Mb)).map
      (fun a => ((sn a.1).1, (sn a.1).2.1, put a.2 (sn a.1).2.2)) =
    (unif (D.Mk × D.Nn.Rnd)).map sn
  rw [hL, hR,
    map_unif_bind_factor F' (fun a => (a.1.2, a.2))
      (fun a => (unif (U.Pd × D.Nn.Rnd)).map fun b => G' (a, b)) key,
    hh, map_unif_prod]

omit [Field E] in
theorem msgs_join (S N : Sig E) (a : S.Wit) (b : N.Wit) :
    (S.sum N).msgs (S.join N (T := OMsg.Wit) a b) =
      S.join N (T := OMsg.Msg) (S.msgs a) (N.msgs b) := by
  funext i
  cases i <;> rfl

theorem ldSendSig_fresh : Spec.ldSendSig_fresh E := by
  intro S N Sd St Wp Wp' E₀ D t Ri Mb _ _ U Kc rd put hU hZ
  refine fresh_post _ _ _ _ _ _ _ _ _ _ (ldSendFamHon Sd (St × S.Smp) (E₀.prod S.ext) D) Ri _
    (S.mergeX N St) (S.mergeE N E₀) (S.mergeW N St Wp') Kc Kc
    (fun v => rd (S.join N (T := OMsg.Msg) (S.msgs v.2.1) (N.msgs v.1), v.2.2))
    (fun v => rd ((S.sum N).msgs v.1, v.2))
    (fun a => ((a.1.1.1, S.join N (T := OMsg.Smp) a.1.1.2 a.1.2), a.2)) Mb put put ?_
    (fun _ _ _ => rfl)
    (ldSendFam_fresh E N Sd (St × S.Smp) (S.Wit × Wp) (S.Wit × Wp') (E₀.prod S.ext) D t Ri Mb U Kc
      (fun m w' => rd (S.join N (T := OMsg.Msg) (S.msgs w'.1) m, w'.2)) put hU hZ)
  intro xo wo
  show ((xo.1.1, S.join N (T := OMsg.Smp) xo.1.2 xo.2),
      rd ((S.sum N).msgs (S.join N (T := OMsg.Wit) wo.2.1 wo.1), wo.2.2)) = _
  rw [msgs_join]

theorem sigChain_send_masked : Spec.sigChain_send_masked E := by
  intro S N Sd Kc St St' Wp Wp' Wp'' E₀ E₀' A bk D L t R H B ext P d Dm U hC
    hF hL hE hD hZ hU g hm hcl
  have g₁ := ldSendSig_chain
    E S N Sd Kc St Wp Wp' E₀ A bk D L t hC hF hL hE hD (own_blind E N _ _ D Dm.Mk U Sd _ _ _ hU) hZ
  have fr :=
    ldSendSig_fresh E S N Sd St Wp Wp' E₀ D t (S.over A).cf.rel Dm.Mk U Dm.Kc Dm.kc Dm.put hU hZ
  have g₂ : GoodM (R.keep (S.sum N).Smp (S.sum N).ext) ((S.sum N).liftH H)
      ((S.sum N).over (S.grow N A bk)) ((S.sum N).over B)
      (fun a τ w => (w.1, ext ((S.sum N).msgs w.1) (a.1.1, a.2.1) τ w.2))
      (P.keep (S.sum N).Smp (S.sum N).ext)
      ((Dm.keep (S.sum N).Smp (S.sum N).ext).mapW fun w => ((S.sum N).msgs w.1, w.2)) :=
    { base := sigLift_goodB E (S.sum N) Kc St St' Wp' Wp'' E₀ E₀' R H (S.grow N A bk) B ext P g
      mm :=
        mm_mapW _ _ _ _ _ _ _ _ _ _ _ _ _ (mm_keep _ _ _ _ _ _ _ _ _ (S.sum N).Smp (S.sum N).ext hm)
      claim := fun x y w h => hcl x.1 y.1 ((S.sum N).msgs w.1, w.2) h.2.2 }
  exact goodT_seq_masked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _
    ((Dm.keep (S.sum N).Smp (S.sum N).ext).mapW fun w => ((S.sum N).msgs w.1, w.2)) g₁ fr
    (goodM_cf _ _ _ _ _ _ _ _ _ _ _ _ _ _ g₂)

end

section
variable (E : Type) [Field E] [Fintype E]

theorem send_psc_goodT : Spec.send_psc_goodT E := by
  intro S N Sd Y Kc Wp Wp' E₀ A0 bk msg₀ msg O D L t d U hC hF hL hE hD hZ hV hDg hI hO hU hcl
  have heq : S.grow N (Y.baseIn A0 msg₀) bk = Y.baseIn (S.grow N A0 bk) fun w => msg w.1 := by
    show IOR.Rels.mk _ _ _ _ = IOR.Rels.mk _ _ _ _
    congr 1
    · funext x y w
      exact propext (and_congr Iff.rfl (hcl x w.1 w.2))
    · funext a w
      exact propext (and_congr Iff.rfl (hcl a.1 w.1 w.2))
  refine sigChain_send_masked E S N Sd Kc (E × Y.St) Y.Out Wp Wp' Wp' E₀ E₀ (Y.baseIn A0 msg₀) bk D
    L t (Y.psc E₀) (Y.hon E₀ fun w => msg w.1) (Y.baseOut (S.grow N A0 bk) fun w => msg w.1)
    (fun _ _ _ wp => wp) (Y.nums E₀ Kc) d (Y.maskData E₀ (fun w : (S.sum N).Msg × Wp' => msg w.1) O)
    U hC hF hL hE hD hZ hU ?_ (psc_mm E Y E₀ _ _ O hV hDg hO) ?_
  · rw [heq]
    exact psc_goodAt E Y E₀ (S.sum N).Msg Wp' Kc (S.grow N A0 bk) msg hV hDg hI
  · intro x y w h
    exact PscPar.sumHolds_cut hO x (msg w.1) ((hcl x w.1 w.2).1 h.2)

theorem send_psc_our_goodT :
    Spec.send_psc_our_goodT
      E := fun S N Sd T Kc Wp Wp' E₀ A0 bk msg₀ msg Rd D L t d U hC hF hL hE hD hZ hV hX hY hI hO hU hcl =>
  send_psc_goodT E S N Sd T.par Kc Wp Wp' E₀ A0 bk msg₀ msg (T.own Rd) D L t d U hC hF hL hE hD hZ
    ((psc_our_ok E T).1 hV) (psc_our_deg E T hX hY) ((psc_our_ok E T).2 hI) (psc_our_own E T Rd hO)
    hU fun x m wp' => ((psc_our_sum E T x _).trans (hcl x m wp')).trans (psc_our_sum E T x _).symm

end
end Cb
