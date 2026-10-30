-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemandTProofs.lean: the proofs of the statements of Cb/Ld/LdLinCloseDemandT.lean
(the plan with two splittings in the order of a batch: the whole closing).
Named tools: `LdLinC.step_ok`; `LdTc.frontC_ok` (under the hypotheses of its statement: a chain in
order, then a front whose splittings' masks are fresh, is in order).
Nothing is defined here.

Main names (statements and hypotheses: Cb/Ld/LdLinCloseDemandT.lean):
  `ldLinAlt_chain`, `ldLinAlt_tail`: the generic part, for any closing Q of the test.
  `ldLinPtT_behind`: `T.Q` in order after the core and the step.
  `ldLinPtT_demand`: its demand within what the three sendings bear.
  `ldLinPtT_tail`: the test with this closing as a tail.
-/
import Cb.Ld.LdLinCloseDemandT

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- a chain in order, then a front whose splittings' masks are fresh.
(not all hypotheses are named here: see the statement below) -/
theorem LdTc.frontC_ok {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type}
    {x y : FSt S E₀ Wp Unit} (p : Front x y) {Z : Joint Unit} (c₀ : Chain Unit Z x.stage.J)
    (Rd : S.Ent → Prop) (Rr : S.O → Prop) (h₀ : c₀.Ok) (hp : p.prog.Hyp)
    (hz : p.ZkOK Rd Rr (fun g => (c₀.append (.one x.stage.idLink)).FreshFor g.kc g.Mk g.put)) :
    (c₀.append (LdTc.frontC p)).Ok :=
  (ok_append Unit _ _ _ c₀ (LdTc.frontC p)).2
    ⟨h₀, front_okFrom E Unit S E₀ Wp x y p Z _ c₀ (.one x.stage.idLink) Rd Rr h₀
        ((Chain.okFrom_one c₀ _).2 (Or.inl x.stage.idLink_goodT)) hp hz⟩

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

open Classical in
theorem ldLinAlt_chain : Spec.ldLinAlt_chain E ι κ J Y := by
  intro C on0 εf Sn qa Q fq hF hpy hS hSays hQ hq
  have hT := ldLinPre_step_cf E ι κ J Y C Q.St Q.base fq hSays
  have hp := pieceTr_pure Unit _ _ _ _ _ _ C.P.j6.cf (C.S.over Q.base).cf (C.stepF fq) C.toE
    (C.stepM fq) (fun _ w => C.back w) (C.P.q5 Sn qa) Q.q
    ⟨hT.isLocal, hT.acc, hT.onOut, hT.keeps, hT.know⟩ hq
  exact ⟨ldChain_okFrom_append (C.P.chain on0 Sn εf) (C.chain fq Q.base) Q.c
      ((Chain.okFrom_one (C.P.chain on0 Sn εf) _).2 (Or.inl hp.good)) hQ.1,
    sidesCT_append Unit _ _ _ (C.chain fq Q.base) Q.c (C.P.q5 Sn qa) Q.q
      ((Chain.sidesC_one _ _ _).2
        (sideC_of_side _ _ _ _ _ _ _ _ _ _ _ ⟨hp.noHid, hp.noTie, hp.bears⟩)) hQ.2⟩

open Classical in
theorem ldLinAlt_tail : Spec.ldLinAlt_tail E ι κ J Y := by
  intro C on0 εf Sn qa d Q fq hF hpy hS hSays hQ hq
  obtain ⟨h1, h2⟩ := ldLinAlt_chain E ι κ J Y C on0 εf Sn qa Q fq hF hpy hS hSays hQ hq
  exact ldLinC_tail C.P on0 εf Sn qa d (C.cZ Q fq) hF hpy hS h1 h2

/-- For nonempty ι, under `hF`, `hpy`, `hS`, `hSays`: core and step are a chain in order (`Ok`). -/
theorem LdLinC.step_ok (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop)
    (εf : ℕ) (Sn : C.P.Snd) {Stq : Type} (Bq : IOR.Rels Unit Stq C.E₀ (C.S.Msg × C.Wpa))
    (fq : C.St6 → Stq) (hF : C.P.FoldErr on0 εf) (hpy : Function.Injective C.P.D.py)
    (hS : Sn.OK) (hSays : C.Says Bq fq) :
    ((C.P.chain on0 Sn εf).append (C.chain fq Bq)).Ok := by
  classical
  have hT := ldLinPre_step_cf E ι κ J Y C Stq Bq fq hSays
  have hp := pieceTr_pure Unit _ _ _ _ _ _ C.P.j6.cf (C.S.over Bq).cf (C.stepF fq) C.toE
    (C.stepM fq) (fun _ w => C.back w) (fun _ => True) (fun _ => True)
    ⟨hT.isLocal, hT.acc, hT.onOut, hT.keeps, hT.know⟩ fun _ _ => trivial
  exact (ok_append Unit _ _ _ (C.P.chain on0 Sn εf) (C.chain fq Bq)).2
    ⟨(ok_of_allT Unit _ _ _).1 (ldLinC_allT C.P on0 εf Sn hF hpy hS),
      (Chain.okFrom_one (C.P.chain on0 Sn εf) _).2 (Or.inl hp.good)⟩

theorem ldLinPtT_behind : Spec.ldLinPtT_behind E ι κ J Y := by
  intro C p T on0 εf Sn Rd₁ Rr₁ Rd₂ Rr₂ hF hpy hS hr hA hP hK h₁ h₂ h₃ h₄ hQ' r0 r1 f0 f1
  obtain ⟨hy₁, hy₂⟩ := ldLinPt_hyp E ι κ J Y C p _ T.Q'.base hP hK
  obtain ⟨z₁, z₂⟩ := ldLinPt_zk E ι κ J Y C p _ T.Q'.base
  have hz₁ := z₁ Rd₁ Rr₁
    (fun g =>
      ((T.c₀ on0 εf Sn).append (.one (p.x₁ T.Q'.base).stage.idLink)).FreshFor g.kc g.Mk g.put)
    r0 f0
  have hz₂ := z₂ Rd₂ Rr₂
    (fun g =>
      ((T.c₂ on0 εf Sn).append (.one (p.x₂ T.Q'.base).stage.idLink)).FreshFor g.kc g.Mk g.put)
    r1 f1
  -- the chains in front are in order
  have k₀ : (T.c₀ on0 εf Sn).Ok :=
    LdLinC.step_ok E ι κ J Y C on0 εf Sn _ _ hF hpy hS
      (ldLinPt_says E ι κ J Y C p _ T.Q'.base T.fa hr hA)
  have k₁ : (T.c₁ on0 εf Sn).Ok :=
    LdTc.frontC_ok (p.front₁ T.Q'.base) (T.c₀ on0 εf Sn) Rd₁ Rr₁ k₀ hy₁ hz₁
  have g₁ := (ldChain_link E C.S T.D₁ _ C.Wpa C.E₀ (LdTc.cons T.D₂ T.Q₂ T.d₂ T.d₂').base T.d₁ T.d₁'
    (fun _ => True) (fun _ => True) h₁ fun _ _ => trivial).1
  have g₂ := (ldChain_link E p.S₁ T.D₂ _ C.Wpa C.E₀ T.Q₂.base T.d₂ T.d₂' (fun _ => True)
    (fun _ => True) h₂ fun _ _ => trivial).1
  have k₂ : (T.c₂ on0 εf Sn).Ok :=
    (Chain.ok_snoc _ _).2 ⟨(Chain.ok_snoc _ _).2 ⟨k₁, Or.inl g₁⟩, Or.inl g₂⟩
  -- the instance's tests are in order by themselves
  have q₃ : T.Q₃.OK :=
    ldChain_cons E p.S₂ C.E₀ C.Wpa T.D₃ _ T.d₃ T.d₃' h₃
      (ldChain_cons E p.S₃ C.E₀ C.Wpa T.D₄ T.Q' T.d₄ T.d₄' h₄ hQ')
  have b₂ : T.Q₂.OkBehind (T.c₂ on0 εf Sn) :=
    ldAlt_front E p.S₂ C.E₀ C.Wpa (p.x₂ T.Q'.base) T.Q₃ (p.front₂ T.Q'.base) _ (T.c₂ on0 εf Sn)
      Rd₂ Rr₂ k₂ hy₂ (ldLinPt_sd E ι κ J Y C p _ T.Q'.base (fun _ => True) T.Q₃.q).2 hz₂
      (ldAlt_of_ok E p.S₂ C.E₀ C.Wpa T.Q₃ _ _ q₃)
  have b₂' : T.Q₂.OkBehind
      (((T.c₁ on0 εf Sn).snoc (T.D₁.link (LdTc.cons T.D₂ T.Q₂ T.d₂ T.d₂').base T.d₁ T.d₁')).snoc
        (T.D₂.link T.Q₂.base T.d₂ T.d₂')) := b₂
  have b₁ : T.Q₁.OkBehind (T.c₁ on0 εf Sn) :=
    ldAlt_cons E C.S C.E₀ C.Wpa T.D₁ (LdTc.cons T.D₂ T.Q₂ T.d₂ T.d₂')
      T.d₁ T.d₁' _ (T.c₁ on0 εf Sn) h₁
      (ldAlt_cons E p.S₁ C.E₀ C.Wpa T.D₂ T.Q₂ T.d₂ T.d₂' _
        ((T.c₁ on0 εf Sn).snoc (T.D₁.link (LdTc.cons T.D₂ T.Q₂ T.d₂ T.d₂').base T.d₁ T.d₁')) h₂ b₂')
  exact ldAlt_front E C.S C.E₀ C.Wpa (p.x₁ T.Q'.base) T.Q₁ (p.front₁ T.Q'.base) _ (T.c₀ on0 εf Sn)
    Rd₁ Rr₁ k₀ hy₁ (ldLinPt_sd E ι κ J Y C p _ T.Q'.base T.Q₁.q (fun _ => True)).1 hz₁ b₁

omit [Fintype ι] [Nonempty ι] in
open Classical in
theorem ldLinPtT_demand : Spec.ldLinPtT_demand E ι κ J Y := by
  intro C p T Sn qa q₀ ba b' hQ hqa hA hW hU hO V hV
  exact ldDemand_lin E ι κ J Y C Sn qa q₀ ba _ hqa hA hW hU hO V
    (ldDemand_cons E C.S C.E₀ C.Wpa T.D₁ _ T.d₁ T.d₁' q₀ _
      (ldDemand_cons E p.S₁ C.E₀ C.Wpa T.D₂ T.Q₂ T.d₂ T.d₂' q₀ _
        (ldDemand_cons E p.S₂ C.E₀ C.Wpa T.D₃ _ T.d₃ T.d₃' q₀ _
          (ldDemand_cons E p.S₃ C.E₀ C.Wpa T.D₄ T.Q' T.d₄ T.d₄' q₀ b' hQ)))
      V hV)

theorem ldLinPtT_tail : Spec.ldLinPtT_tail E ι κ J Y := by
  intro C p T on0 εf Sn qa d q₀ ba b' Rd₁ Rr₁ Rd₂ Rr₂ hF hpy hS hr hA hP hK h₁ h₂ h₃ h₄ hQ' r0 r1
    f0 f1 hq hqa i1 i2 i3 i4
  exact ldLinAlt_tail E ι κ J Y C on0 εf Sn qa d T.Q (C.fqT T.fa) hF hpy hS
    (ldLinPt_says E ι κ J Y C p _ T.Q'.base T.fa hr hA)
    (ldLinPtT_behind E ι κ J Y C p T on0 εf Sn Rd₁ Rr₁ Rd₂ Rr₂ hF hpy hS hr hA hP hK h₁
      h₂ h₃ h₄ hQ' r0 r1 f0 f1)
    (ldLinPtT_demand E ι κ J Y C p T Sn qa q₀ ba b' hq hqa i1 i2 i3 i4)

end
end Cb
