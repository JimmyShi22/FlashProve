-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendFreshVisProofs.lean: the proofs of the statements of Cb/Ld/LdSendFreshVis.lean.
-/
import Cb.Ld.LdSendFreshVis
import Cb.Ld.LdSendFreshProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (E : Type) [Field E]

theorem ldSendFam_freshV : Spec.ldSendFam_freshV E := by
  classical
  intro N Sd X W W' E₀ D t Ri Mb _ _ U Rv Kc vis rd put hU x y w _ ρ _ T hT
  obtain ⟨s, u, u'⟩ := ρ
  obtain ⟨body, hbody⟩ := hU.lay
  let sn : D.Mk × D.Nn.Rnd → View (ldSendFam N Sd X E₀) × (X × N.Smp) × Kc :=
    (ldSendFamHon Sd X E₀ D).seen
      (fun v => rd (N.msgs v.1) (vis fun a => (v.1 a).2) v.2) w x (s, u, u') T
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
    obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq _ _ (hU.pad s w Mo M k₀)
    refine map_unif_prod_congr σ _ _ fun η => ?_
    obtain ⟨e₂, he₂⟩ := hU.hid (ldSendFamSet N Sd T) hT w Mo M k₀ η (σ η)
    refine map_unif_reindex e₂ _ _ fun r => ?_
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact ldSendFam_view_congr N Sd X E₀ T _ _
        (congrArg (fun a : N.Answ => (((), (a, ())) : Plains (N.sh Sd))) (hσ η))
        fun q hq => (he₂ r).1 q hq
    · show (x, fun a => (Sd.sd a s, D.ans Sd s w (U.mk' Mo k₀ η) a)) =
        (x, fun a => (Sd.sd a s, D.ans Sd s w (U.mk' M k₀ (σ η)) a))
      rw [hσ η]
    · show put M (rd (D.upM (D.put w (U.mk' Mo k₀ η))) (vis (D.upR r)) (D.rest w)) =
        rd (D.upM (D.put w (U.mk' M k₀ (σ η)))) (vis (D.upR (e₂ r))) (D.rest w)
      rw [hbody, hbody, hU.over, (he₂ r).2]
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

theorem ldSendSig_freshV : Spec.ldSendSig_freshV E := by
  intro S N Sd St Wp Wp' E₀ D t Ri Mb _ _ U Rv Kc vis rd put hU
  exact fresh_post _ _ _ _ _ _ _ _ _ _ (ldSendFamHon Sd (St × S.Smp) (E₀.prod S.ext) D) Ri _
    (S.mergeX N St) (S.mergeE N E₀) (S.mergeW N St Wp') Kc Kc
    (fun v => rd (N.msgs v.1) (vis fun a => (v.1 a).2) v.2)
    (fun v =>
      rd (N.msgs (S.right N (T := OMsg.Wit) v.1))
        (vis fun a => (S.right N (T := OMsg.Wit) v.1 a).2) (S.left N (T := OMsg.Wit) v.1, v.2))
    (fun a => ((a.1.1.1, S.join N (T := OMsg.Smp) a.1.1.2 a.1.2), a.2)) Mb put put
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ldSendFam_freshV E N Sd (St × S.Smp) (S.Wit × Wp) (S.Wit × Wp') (E₀.prod S.ext)
      D t Ri Mb U Rv Kc vis rd put hU)

theorem lawsV_of_laws : Spec.lawsV_of_laws E := by
  intro N W W' D Mb U Sd t Kc rd put hU hZ
  obtain ⟨body, hb⟩ := hU.lay
  refine ⟨hU.over,
    ⟨fun w k₀ _ => body w k₀, fun w M k₀ η _ => hb w M k₀ η⟩,
    fun s w M M' k₀ => hU.pad s w w M M' k₀ k₀,
    fun T hT w M M' k₀ η η' => ?_⟩
  obtain ⟨e, he⟩ := (hides_iff_equiv _ D.Nn (N.budT t)).1
    hZ T hT (D.put w (U.mk' M k₀ η)) (D.put w (U.mk' M' k₀ η'))
  exact ⟨e, fun r => ⟨fun p hp => eq_of_heq (Sigma.mk.inj (he r p hp)).2, rfl⟩⟩

omit [Field E] in
theorem splitAt_symm_self {ι : Type} [DecidableEq ι] {β : ι → Type} (o : ι)
    (x : β o) (f : ∀ j : {j // j ≠ o}, β j) :
    (Equiv.piSplitAt o β).symm (x, f) o = x := by
  simp [Equiv.piSplitAt]

omit [Field E] in
theorem splitAt_symm_ne {ι : Type} [DecidableEq ι] {β : ι → Type} (o : ι) (x : β o)
    (f : ∀ j : {j // j ≠ o}, β j) (a : ι) (h : a ≠ o) :
    (Equiv.piSplitAt o β).symm (x, f) a = f ⟨a, h⟩ := by
  simp [Equiv.piSplitAt, h]

section OfMem
variable {E} {N : Sig E} {W W' : Type} (mem : ∀ a, (N.om a).Sender W Unit) (rest : W → W')
  (w0 : W) (o : N.O) {Mb Mo Pd : Type} [Fintype Mo] [Nonempty Mo] [Fintype Pd]
  [Nonempty Pd] (κo : (mem o).Mk ≃ (Mb × Mo) × Pd)

omit [Field E] in
theorem ofMemOwn_self (M : Mb) (k₀ : Mo × ∀ a : {a // a ≠ o}, (mem a).Mk) (η : Pd) :
    (Sig.Sender.ofMemOwn mem rest w0 o κo).mk' M k₀ η o = κo.symm ((M, k₀.1), η) :=
  splitAt_symm_self (β := fun a => (mem a).Mk) o _ _

omit [Field E] in
theorem ofMemOwn_ne (M : Mb) (k₀ : Mo × ∀ a : {a // a ≠ o}, (mem a).Mk)
    (η : Pd) (a : N.O) (h : a ≠ o) :
    (Sig.Sender.ofMemOwn mem rest w0 o κo).mk' M k₀ η a = k₀.2 ⟨a, h⟩ :=
  splitAt_symm_ne (β := fun a => (mem a).Mk) o _ _ a h

end OfMem

omit [Field E] in
theorem ofMem_hid : Spec.ofMem_hid E := by
  classical
  intro N W W' mem rest w0 o Mb Mo Pd _ _ _ _ κo t hZ T hT w M M' k₀ η η'
  obtain ⟨Xs, hc, hX⟩ := hT o
  let To : Finset (N.om o).C.NP :=
    T.preimage (fun p : (N.om o).C.NP => (⟨o, p⟩ : Σ a, (N.om a).C.NP))
      fun _ _ _ _ hxy => eq_of_heq (Sigma.mk.inj hxy).2
  have hTo : (N.om o).C.budT (t o) To := ⟨Xs, hc, fun p hp => hX p (Finset.mem_preimage.1 hp)⟩
  obtain ⟨eo, heo⟩ := (hides_iff_equiv (N.om o).nat (mem o).N ((N.om o).C.budT (t o))).1
    hZ To hTo ((mem o).put w (κo.symm ((M, k₀.1), η))) ((mem o).put w (κo.symm ((M', k₀.1), η')))
  let e : (∀ a, (mem a).N.Rnd) ≃ ∀ a, (mem a).N.Rnd :=
    (Equiv.piSplitAt o fun a => (mem a).N.Rnd).trans
      ((eo.prodCongr (Equiv.refl _)).trans (Equiv.piSplitAt o fun a => (mem a).N.Rnd).symm)
  have e_self : ∀ r : ∀ a, (mem a).N.Rnd,
    e r o = eo (r o) := fun r => splitAt_symm_self (β := fun a => (mem a).N.Rnd) o _ _
  have e_ne : ∀ (r : ∀ a, (mem a).N.Rnd) a, a ≠ o → e r a = r a := fun r a h =>
    splitAt_symm_ne (β := fun a => (mem a).N.Rnd) o _ _ a h
  refine ⟨e, fun (r : ∀ a, (mem a).N.Rnd) => ⟨fun p hp => ?_, funext fun a => ?_⟩⟩
  · obtain ⟨a, q⟩ := p
    show (mem a).N.enc
        ((mem a).put w ((Sig.Sender.ofMemOwn mem rest w0 o κo).mk' M k₀ η a)) (r a) q =
      (mem a).N.enc
        ((mem a).put w ((Sig.Sender.ofMemOwn mem rest w0 o κo).mk' M' k₀ η' a)) (e r a) q
    by_cases h : a = o
    · subst h
      rw [ofMemOwn_self, ofMemOwn_self, e_self]
      exact eq_of_heq (Sigma.mk.inj (heo (r a) q (Finset.mem_preimage.2 hp))).2
    · rw [ofMemOwn_ne mem rest w0 o κo M k₀ η a h,
        ofMemOwn_ne mem rest w0 o κo M' k₀ η' a h, e_ne r a h]
  · show (mem a).upR (e r a) = (mem a).upR (r a)
    rw [e_ne r a a.2]

theorem ofMem_pad : Spec.ofMem_pad E := by
  classical
  intro N W W' mem rest w0 o Mb Mo Pd _ _ _ _ κo Sd h s w M M' k₀
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq _ _ (h (Sd.sd o s) w M M' k₀.1)
  refine map_unif_reindex σ _ _ fun η => funext fun a => ?_
  show (mem a).ans (Sd.sd a s) w ((Sig.Sender.ofMemOwn mem rest w0 o κo).mk' M k₀ η a) =
    (mem a).ans (Sd.sd a s) w ((Sig.Sender.ofMemOwn mem rest w0 o κo).mk' M' k₀ (σ η) a)
  by_cases ha : a = o
  · subst ha
    rw [ofMemOwn_self, ofMemOwn_self]
    exact hσ η
  · rw [ofMemOwn_ne mem rest w0 o κo M k₀ η a ha, ofMemOwn_ne mem rest w0 o κo M' k₀ (σ η) a ha]

end
end Cb
