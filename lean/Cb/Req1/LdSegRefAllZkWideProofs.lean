-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefAllZkWideProofs.lean: the statements of Cb/Req1/LdSegRefAllZkWide.lean, proved.

The front's facts follow from wide facts by Cb/Req1/LdSegFrontRefWideProofs.lean; "quiet" from
readings by unfolding the letters of a sumcheck's item and by what a wide fact's overwriting leaves
alone (Cb/Req1/LdSegCarry.lean).
What each statement says, and the limits: the head of Cb/Req1/LdSegRefAllZkWide.lean.
-/
import Cb.Req1.LdSegRefAllZkWide
import Cb.Req1.LdSegFrontRefWideProofs
import Cb.Ld.LdPscZkProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain

theorem ldSegRefW_fresh : Spec.ldSegRefW_fresh := fun _ _ _ A _ c base _ _ h hf => h A c base hf

theorem plVal_at {N Ix Mk E : Type} [Zero E] (at' : Ix → N) (ve : Mk → Ix → E)
    (h : Function.Injective at') (M : Mk) (i : Ix) :
    plVal at' ve M (at' i) = ve M i :=
  h.extend_apply _ _ i

theorem ldSegRefW_quietP : Spec.ldSegRefW_quietP := by
  classical
  intro E Kc _ _ T S E₀ Wp A0 msg Rd J' msg' Rd' hN w w' M hw y hy
  refine hN _ _ (fun j hj hi => ?_) y hy
  have e : (T.own Rd).cut (msg (S.msgs w'.1)) j =
      (T.own Rd).put M ((T.own Rd).cut (msg (S.msgs w.1))) j := congrFun hw j
  have e1 : ∀ m : T.J → E, (T.own Rd).cut m j = m j := fun m => if_pos hj
  rw [e1, PscPar.put_off M _ j fun i h => hi i h.symm, e1] at e
  exact e

theorem ldSegRefW_quietW :
    Spec.ldSegRefW_quietW := fun _ _ _ _ a Rd Rr own Mk _ _ val _ _ _ h w w' M hw j hj =>
  h _ _ (segWide_alike a Rd Rr own Mk val w w' M hw).1 j hj

theorem ldSegRefW_front : Spec.ldSegRefW_front := by
  intro E Kc _ _ pp I A W F P X hX hF hL h0 hS hN hI
  have fP : ∀ (T : PscOur E)
          (A0 : Rels Kc T.St I.C.E0 (A.Xa.Q.D.S.Msg × (I.C.PIdx × (A.W₁ × A.Gh))))
          (msg : A.Xa.Q.D.S.Msg → T.J → E) (RdT : T.J → Prop)
          (at' : PIdx T.par.fmt ⊕ T.A → A.Xa.Q.D.S.Ent),
        T.OwnOur RdT → LdRefP.At W msg RdT (T.own RdT).at at' →
        X (A.V.Fp.s0.wideFact W.Rd W.Rr (plOwn at') (T.own RdT).Mk
            (plVal at' fun M => Sum.elim M.1 M.2)) →
        X (frFact Kc T A.Xa.Q.D.S I.C.E0 (I.C.PIdx × (A.W₁ × A.Gh)) A0 msg RdT) := by
    intro T A0 msg RdT at' hO hA hx
    refine hX _ _ (fun B c base hc => ?_) hx
    exact frontWide_psc E Kc B A.V.Fp.s0 c base W.Rd W.Rr (plOwn at') T A0 msg RdT _ at' hO.inj
      hO.own hA.p1 hA.p2 (fun i => ⟨i, rfl⟩) hA.rd (fun M i => plVal_at at' _ hA.inj M i) hc
  refine ⟨?_,
    fP _ _ _ _ _ hF.own0 h0 hI.s0,
    ldSegRefW_quietP E Kc _ _ _ _ _ _ _ _ _ _ hN.n0L,
    fun i hi => fP _ _ _ _ _ (hF.own i hi) (hS i hi) (hI.s i hi),
    fun i hi => ldSegRefW_quietP E Kc _ _ _ _ _ _ _ _ _ _ (hN.nSL i hi),
    fun i hi => ldSegRefW_quietP E Kc _ _ _ _ _ _ _ _ _ _ (hN.nS0 i hi),
    fun i hi j hj => ldSegRefW_quietP E Kc _ _ _ _ _ _ _ _ _ _ (hN.nSS i hi j hj)⟩
  refine hX _ _ (fun B c base hc => ?_) hI.lk
  exact frontWide_lkp E Kc A.Xa.Q.D.S I.C.E0 _ A.V.Fp _ _ A.V.Fp.s0.A B c base W.Rd W.Rr
    (plOwn P.atL) F.Dt F.RdK F.Cc _ P.atL hF.lk.places
    (fun i =>
      hF.lk.inRd _
        (Or.inr (((ldLkpPl2_asm E A.V.Fp.A I.C.E0 A.Xa.Q.D.S.Msg _ Kc A.V.Fp.msg F.RdK
              F.Dt hF.lk.places).1.2 _).1 ⟨i, rfl⟩)))
    hL.p1 hL.p2 (fun i => ⟨i, rfl⟩) hL.rd (fun M i => plVal_at P.atL _ hL.inj M i) hc

theorem ldSegRefW_pass : Spec.ldSegRefW_pass := fun E Kc _ _ _ A W _ _ own Mk _ _ val hx hB h1 h3 =>
  ⟨hx, ⟨ldSegRefW_quietW E Kc A.Xa.Q.D.s0 W.Rd W.Rr own Mk val _ _ _ hB.lk,
      ldSegRefW_quietW E Kc A.Xa.Q.D.s0 W.Rd W.Rr own Mk val _ _ _ hB.s0,
      fun j hj => ldSegRefW_quietW E Kc A.Xa.Q.D.s0 W.Rd W.Rr own Mk val _ _ _ (hB.s j hj)⟩,
    h1, h3⟩

theorem ldSegRefAll_zkAtW : Spec.ldSegRefAll_zkAtW := by
  intro E Kc _ _ pp I A hne W F P κ RdL X hX hG hF hL h0 hS hN hI hW
  exact ⟨hne, W, F, κ, RdL, hG, hF,
    ldSegRefW_front E Kc pp I A W F P X hX hF hL h0 hS hN hI,
    ⟨hW.maskL, hW.rdL, hW.inL, hW.wideL,
      ldSegRefW_pass E Kc I A W F X _ _ _ hW.factL hW.blL hW.s1L hW.s3L, hW.ownT, hW.inT, hW.wideT,
      ldSegRefW_pass E Kc I A W F X _ _ _ hW.factT hW.blT hW.s1T hW.s3T, hW.apart⟩⟩

end Cb
