-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanPBProofs.lean: the proofs of the statements of Cb/Ld/LdLinClosePlanPB.lean.

Main names (statements and hypotheses: Cb/Ld/LdLinClosePlanPB.lean):
  `ldRun_out`: what a whole test's reduction hands on
  `ldLinPpB_same`: the links of the closing for a batch
  `ldLinPpB_act`: the acting parts of both shared tests
  `ldLinPpB_kb`: knowledge soundness of the closing, from the key `C.P.key6`
  `ldLinPpB_know`: `KnowB` of the test for linear constraints for at most N instances, for the
    vectors that share the encoded index and its record, on the statements with the condition
    `(C.P.j0 on0).on`; what is extracted is a witness of `(C.P.j0 on0).relR`
-/
/- Limits: no theorem of this library states that the hypotheses of `ldLinPpB_know` can be met
   together. -/
import Cb.Ld.LdLinClosePlanPB
import Cb.Ld.LdLinClosePlanPProofs
import Cb.Ld.LdFrontOnProofs
import Cb.Ld.LdAltBProofs
import Ior.FrameProofs
import Ior.SeqProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldRun_out : Spec.ldRun_out := by
  intro E _ _ S D St₀ Wp E₀ A₀ d d' a τ b hb
  obtain ⟨h1, h2⟩ := IOR.red_out_eq_some.1 hb
  refine Prod.ext ?_ (h2.trans rfl)
  have h1' : (((D.T.R.out
            (ldBrNx D.G D.kp D.Sb D.Z St₀ (ldBrF D.G D.kp D.Sb St₀ a.1)
              (drawn (Tr.fst (s := (ldBridge D.G D.kp D.Sb D.Z St₀ E₀).shape) τ))).1
            ((ldBrG D.G D.kp E₀).map a.2).1
            (Tr.fst (s := D.T.R.shape)
              (Tr.snd (s := (ldBridge D.G D.kp D.Sb D.Z St₀ E₀).shape) τ))).map
          fun xo => (xo, D.outX a.1)).bind
        fun x₃ => some x₃.2) = some b.1 := h1
  cases hT : D.T.R.out
      (ldBrNx D.G D.kp D.Sb D.Z St₀ (ldBrF D.G D.kp D.Sb St₀ a.1)
        (drawn (Tr.fst (s := (ldBridge D.G D.kp D.Sb D.Z St₀ E₀).shape) τ))).1
      ((ldBrG D.G D.kp E₀).map a.2).1
      (Tr.fst (s := D.T.R.shape) (Tr.snd (s := (ldBridge D.G D.kp D.Sb D.Z St₀ E₀).shape) τ)) with
  | none => rw [hT] at h1'; cases h1'
  | some v => rw [hT] at h1'; exact (Option.some.inj h1').symm


section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Nonempty ι] in
theorem ldLinPpB_same : Spec.ldLinPpB_same E ι κ J Y := fun C _ T cA' same' =>
  ldLinB_cZ_same E ι κ J Y C (T.QA cA' same') (C.fqP T.fa)

omit [Fintype ι] [Nonempty ι] in
theorem ldLinPpB_act : Spec.ldLinPpB_act E ι κ J Y := by
  intro C p T x x' y y' hSh hk
  have h6 : x.2 = x'.2 := congrArg (fun k => k.2) hk
  have h5 : (x.1.2, y.2) = (x'.1.2, y'.2) := congrArg (fun k => k.1.2) hk
  have h4 : x.1.1.2 = x'.1.1.2 := congrArg (fun k => k.1.1.2) hk
  have h3 : (x.1.1.1.2, y.1.2) = (x'.1.1.1.2, y'.1.2) := congrArg (fun k => k.1.1.1.2) hk
  have h2 : x.1.1.1.1.2 = x'.1.1.1.1.2 := congrArg (fun k => k.1.1.1.1.2) hk
  have h1 : x.1.1.1.1.1.1.2 = x'.1.1.1.1.1.1.2 := congrArg (fun k => k.1.1.1.1.1) hk
  have hs : C.sh (C.toSt x) = C.sh (C.toSt x') := by
    show (((x.1.1.1.1.1.1.2, x.1.1.1.1.2), x.1.1.2), x.2) =
      (((x'.1.1.1.1.1.1.2, x'.1.1.1.1.2), x'.1.1.2), x'.2)
    rw [h1, h2, h4, h6]
  have hσ : ∀ o, C.isSh o → C.toSmp x o = C.toSmp x' o := by
    rintro ((o | a) | a) ho
    · exact ho.elim
    · exact congrFun (congrArg Prod.fst h3) a
    · exact congrFun (congrArg Prod.fst h5) a
  have hw : ∀ o, C.isSh o → (C.toE.map y).2 o = (C.toE.map y').2 o := by
    rintro ((o | a) | a) ho
    · exact ho.elim
    · exact congrFun (congrArg Prod.snd h3) a
    · exact congrFun (congrArg Prod.snd h5) a
  funext u
  refine Prod.ext ?_ ?_
  · refine ldRunAct_congr E (C.Brc ⊕ Unit) _ C.S p.GU (fun _ => C.Sh6) C.E₀ _ _ ?_
      (fun o ho => hσ o (hSh o (Or.inl ho))) (fun o ho => hw o (hSh o (Or.inl ho)))
    show ((Sum.elim (C.tgRC (C.sh (C.toSt x))) fun _ => (0 : E) - u),
        Sum.elim (fun _ => C.sh (C.toSt x)) fun _ => C.sh (C.toSt x)) =
      ((Sum.elim (C.tgRC (C.sh (C.toSt x'))) fun _ => (0 : E) - u),
        Sum.elim (fun _ => C.sh (C.toSt x')) fun _ => C.sh (C.toSt x'))
    rw [hs]
  · refine ldRunAct_congr E Unit _ p.S₁ p.G₂ (fun _ => C.Sh6) C.E₀ _ _ ?_
      (fun o ho => hσ o.1 (hSh o.1 (Or.inr ho))) (fun o ho => hw o.1 (hSh o.1 (Or.inr ho)))
    show oneClaim (u, C.sh (C.toSt x)) = oneClaim (u, C.sh (C.toSt x'))
    rw [hs]

omit [Nonempty ι] in
theorem ldLinPpB_kb : Spec.ldLinPpB_kb E ι κ J Y := by
  intro C p T cA' same' N hSh hrest hA hP hK hD₁ hD₂ hD₃ hQ'
  have hSays : C.Says (p.x₁ T.Q'.base).A (C.fqP T.fa) :=
    ldLinPp_says E ι κ J Y C p T.Q'.St T.Q'.base T.fa hrest hA
  have hT := ldLinPre_step_cf E ι κ J Y C _ _ (C.fqP T.fa) hSays
  -- the rest, the third test, the second, the first
  have q3 : (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃').KB N (ldKeyU _) :=
    ldPlanB_cons_local E p.S₂ C.E₀ C.Wpa T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃' N (ldKeyU _) (ldKeyU _)
      (fun _ => ()) hD₃ hQ' fun _ _ _ _ => rfl
  have q2 : (LdTcA.consSh T.D₂ (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃') T.d₂ T.d₂').KB
      N T.kA₂ :=
    ldPlanB_cons_shared E p.S₁ C.E₀ C.Wpa T.D₂ _ T.d₂ T.d₂' N T.kA₂ (ldKeyU _) id (fun _ _ => ())
      hD₂ q3 (fun _ => rfl) fun _ _ _ _ => rfl
  have q1 : (LdTcA.consSh T.D₁
        (LdTcA.consSh T.D₂ (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃') T.d₂ T.d₂')
        T.d₁ T.d₁').KB
      N T.kA₁ :=
    ldPlanB_cons_shared E C.S C.E₀ C.Wpa T.D₁
        (LdTcA.consSh T.D₂ (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃') T.d₂ T.d₂') T.d₁ T.d₁'
        N T.kA₁ T.kA₂ Prod.fst (fun k _ => Prod.snd k) hD₁ q2 (fun _ => rfl) fun a τ b hb => by
      rw [ldRun_out E C.S T.D₁ _ _ _ _ T.d₁ T.d₁' a τ b hb]
      rfl
  -- the front
  have qF : (T.front.cA true).KB N T.kAx T.kA₁ :=
    frontB_kb E C.S C.E₀ C.Wpa _ _ T.front true N T.kAx T.kA₁
      (ldLinPp_hyp E ι κ J Y C p T.Q'.St T.Q'.base hP hK)
      (frontOn_keys E C.S C.E₀ C.Wpa p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU _ (p.Ar₁ T.Q'.base) p.Rs₀
        inferInstance ⟨_, p.base₁ T.Q'.base⟩ _ N T.kAx T.kA₁ (fun k u => k u) fun _ _ => rfl)
  have q0 : (T.QA cA' same').KB N T.kAx :=
    ldAltB_front E C.S C.E₀ C.Wpa (p.x₁ T.Q'.base) (T.QAt cA' same') T.front
      (T.front.cA true) _ N T.kAx T.kA₁ qF q1
  -- the step without rounds in front
  refine chainA_kb_append Unit _ _ _ (ChainA.one (C.link (C.fqP T.fa) (T.QA cA' same').Q.base).lo)
    (T.QA cA' same').cA N C.P.key6 T.kAx ldKeyT ((ChainA.kb_one _ N _ _).2 ⟨?_, ?_⟩) q0
  · refine knowB_conseq _ _ _ _ _ _ _ _ N _ _ _ _ _ _ _ _ _ _
      (knowB_local _ _ _ _ _ _ (C.link (C.fqP T.fa) (T.QA cA' same').Q.base).R RAnn.allLocal
        (fun _ => rfl) N (fun _ => True) _ _ _ _ ?_)
      (fun _ _ => trivial) (fun _ h => h) (fun _ _ _ w => w) (fun _ _ w => w)
    rintro ⟨x, y⟩ _ b w hb hw
    obtain rfl := Option.some.inj hb
    exact hT.know x y _ w trivial rfl hw
  · intro a ha τ j j' b b' hb hb'
    obtain ⟨⟨x, y⟩, haj, h2⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨⟨x', y'⟩, haj', h2'⟩ := Option.bind_eq_some_iff.mp hb'
    obtain rfl := Option.some.inj h2
    obtain rfl := Option.some.inj h2'
    exact ldLinPpB_act E ι κ J Y C p T x x' y y' hSh (ha j j' _ _ haj haj')

theorem ldLinPpB_know :
    Spec.ldLinPpB_know E ι κ J
      Y := fun C p T cA' same' N on0 εf Sn d hF hpy hS hSh hrest hA hP hK hD₁ hD₂ hD₃ hQ' =>
  ldLinB_close E ι κ J Y C on0 εf N Sn d (T.QA cA' same') (C.fqP T.fa) hF hpy hS
    (ldLinPpB_kb E ι κ J Y C p T cA' same' N hSh hrest hA hP hK hD₁ hD₂ hD₃ hQ')

end
end Cb
