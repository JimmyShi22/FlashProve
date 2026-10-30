-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqStdLayAt.lean: a wide fact behind the first standard sending, in the letters of a
coming block: its own type of masks, its own places; and, under the hypotheses below, the wide fact
passes a step that computes a further witness.

Theorems: rules of the framework; no protocol.
Wide facts: `LdStage.wideFact` (Cb/Req1/LdSegCarry.lean); `Honest.Fresh`:
Ior/KnowCollRulesMask.lean; `ldReqBase`: Cb/Req1/LdReqRefNil.lean; `d.StdAt`, for a sending
`d : LdSendD a`: Cb/Req1/LdReqStdLay.lean; `After`: Cb/Req1/LdReq.lean.
Cb/Req1/LdReqStdLayVis.lean lays down, under the hypotheses of its statement
(`Spec.ldReqStdLay_baseMany`), behind a standard first sending, the wide fact of masks at free
entries pl : I → free entries, with the mask values I → E. A coming block has a type of mask values
of its own (the letters of a chain of sumchecks), which is such a vector only up to a bijection ve.

Main names:
  `fresh_reMk`: general: "given all that a run shows the masks are uniform" (exactly:
    `Honest.Fresh`, Ior/KnowCollRulesMask.lean) does not depend on how the mask values are named:
    along any bijection `e : Mk' ≃ Mk`.
  `baseMany_at`: `d.StdAt ..`, `Y.OK d.t`, fr injective ⇒ behind the sending: the wide fact with the
    block's mask values Mk, ve : Mk ≃ (Ix → E), own entries `plOwn at'`, values `plVal at' ve`
    (Cb/Req1/LdSegRefAllZkWide.lean), for at' x = the free entry fr x among all open entries; the
    reading forgets all pads and all encoding randomness of the new family (old part arbitrary).
  `stepW_wide`: under `hb`: the wide fact passes the step of Cb/Ld/LdStepW.lean (a step without
    rounds) (explicit part mapped; further witness computed by "up"), if "up" is the same at
    messages that agree on the entries of the wide reading that are not own.

Limits: no instance here.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqStdLayVis
import Cb.Req1.LdSegRefAllZkWide
import Cb.Req1.LdSegRefLastLay
import Cb.Ld.LdStepW

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- Under the hypotheses below, freshness does not depend on how the mask values are named. -/
theorem fresh_reMk {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} {Wi Wo : Type}
    (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop)
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop) {Kf : Type} (kc : Wo → Kf)
    (Mk Mk' : Type) [Fintype Mk] [Nonempty Mk] [Fintype Mk'] [Nonempty Mk'] (e : Mk' ≃ Mk)
    (put : Mk → Kf → Kf) (h : H.Fresh Ri bud kc Mk put) :
    H.Fresh Ri bud kc Mk' fun M => put (e M) := by
  intro x y w hw ρ hρ T hT
  rw [← h x y w hw ρ hρ T hT,
    ← map_unif_equiv (Equiv.prodCongr (Equiv.refl H.Coin) e), PMF.map_comp]
  rfl

section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- Behind the first standard sending, in the letters of a coming block. -/
theorem baseMany_at (a : LdStage E Kc) (d : LdSendD a) (Y : d.N.StdL F)
    (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
    (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp)
    (hStd : d.StdAt F Y dat rst bk₀ w0) (hY : Y.OK d.t) (Ix : Type) [Fintype Ix]
    (fr : Ix → Σ a, Y.Fr a) (hfr : Function.Injective fr) (RdOld : a.S.Ent → Prop)
    (RrOld : a.S.O → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (ve : Mk ≃ (Ix → E))
    (at' : Ix → (a.S.sum d.N).Ent)
    (hat : ∀ x, at' x = ⟨.inr (Y.entF (fr x)).1, (Y.entF (fr x)).2⟩) :
    ldReqBase d (.nil _)
      (d.tgt.wideFact (a.S.sumP d.N RdOld Y.NoPad) (a.S.sumO d.N RrOld fun _ => False) (plOwn at')
        Mk (plVal at' fun M => ve M)) := by
  classical
  have h0 := ldReqStdLay_baseMany F E Kc a d Y dat rst bk₀ w0 Ix fr RdOld RrOld hStd hfr hY
  unfold ldReqBase at h0 ⊢
  rw [LdProg.After] at h0 ⊢
  have h1 := fresh_reMk d.link.H a.J.rels.rel d.link.P.bud _ (Ix → E) Mk ve _ h0
  have hinj : Function.Injective fun x => Y.entF (fr x) := fun x x' e => hfr (Y.entF_injective e)
  have hinj' : Function.Injective at' := fun x x' e => by
    rw [hat, hat] at e
    have e1 : (Y.entF (fr x)).1 = (Y.entF (fr x')).1 := Sum.inr_injective (congrArg Sigma.fst e)
    exact hinj (Sigma.ext e1 (Sigma.mk.inj e).2)
  have e := LdStage.wideFact_ext d.tgt (a.S.sumP d.N RdOld Y.NoPad)
    (a.S.sumO d.N RrOld fun _ => False) (a.S.sumP d.N (fun _ => False) (Y.ownP fr)) (plOwn at') Mk
    (fun M => a.S.sumV d.N (fun _ => 0) (Y.valP fr (ve M))) (plVal at' fun M => ve M)
    (fun n => by
      obtain ⟨o, j⟩ := n
      rcases o with o | o
      · exact ⟨fun h => h.elim,
          fun ⟨x, hx⟩ => by rw [hat] at hx; exact absurd (congrArg Sigma.fst hx) Sum.inr_ne_inl⟩
      · constructor
        · rintro ⟨x, hx⟩
          exact ⟨x, by rw [hat, ← hx]⟩
        · rintro ⟨x, hx⟩
          rw [hat] at hx
          have e1 : (Y.entF (fr x)).1 = o := Sum.inr_injective (congrArg Sigma.fst hx)
          exact ⟨x, (Sigma.ext e1 (Sigma.mk.inj hx).2).symm⟩)
    (fun M n hn => by
      obtain ⟨o, j⟩ := n
      rcases o with o | o
      · exact hn.elim
      · obtain ⟨x, hx⟩ := hn
        have hx' : (⟨o, j⟩ : d.N.Ent) = Y.entF (fr x) := hx
        have e2 : (⟨.inr o, j⟩ : (a.S.sum d.N).Ent) = at' x := by rw [hat, ← hx']
        show Function.extend (fun i => Y.entF (fr i)) (ve M) (fun _ => 0) ⟨o, j⟩ =
          Function.extend at' (ve M) (fun _ => 0) ⟨.inr o, j⟩
        rw [hx', e2, hinj.extend_apply, hinj'.extend_apply])
  rw [← e]
  exact h1

end

section
variable {E Kc : Type} [Field E] [Fintype E] (S : Sig E) {St St' Wp Wp' : Type} {E₀ : ExtSpec}
  (A : Rels Kc St E₀ (S.Msg × Wp)) (A' : Rels Kc St' E₀ (S.Msg × Wp')) (f : St → St')
  (up : St → S.Msg × Wp → Wp') (dn : St × E₀.Str → S.Msg × Wp' → Wp)

/-- Under the hypotheses below, the wide fact passes the step. -/
theorem stepW_wide (base : MaskFact (S.Wit × Wp) → Prop) (Rd : S.Ent → Prop) (Rr : S.O → Prop)
    (own : S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → S.Ent → E)
    (hb : base ((⟨S, St, E₀, Wp, A⟩ : LdStage E Kc).wideFact Rd Rr own Mk val))
    (hu : ∀ st (m m' : S.Msg) wp, S.Alike Rd own m m' → up st (m', wp) = up st (m, wp)) :
    (ldStepW S A A' f up dn).After
      base ((⟨S, St', E₀, Wp', A'⟩ : LdStage E Kc).wideFact Rd Rr own Mk val) :=
  ldStepW_after S A A' f up dn base _ _ _ _ hb fun st w w' M e => by
    obtain ⟨h1, -, h3⟩ :=
      segWide_alike (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc) Rd Rr own Mk val w w' M e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg (fun z => z.2.1) e
    refine Prod.ext e1 (Prod.ext e2 ?_)
    show up st (S.msgs w'.1, w'.2) = up st (S.msgs w.1, w.2)
    rw [h3]
    exact hu st _ _ _ h1

end
end Cb
