-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanPVProofs.lean: the proofs of the statements of Cb/Ld/LdLinClosePlanPV.lean (the
honest side, for a batch, of the plan with the one shared splitting). Nothing is defined here that a
statement reads.

Main names (statements and hypotheses: Cb/Ld/LdLinClosePlanPV.lean):
  `ldLinPV_tie`: the step without rounds and the core's tie
  `ldLinPV_plan`: the honest side of the three tests and the rest
  `ldLinPV_all`: see its statement in Cb/Ld/LdLinClosePlanPV.lean
  `ldLinPV_std`: see its statement in Cb/Ld/LdLinClosePlanPV.lean
-/
import Cb.Ld.LdLinClosePlanPV
import Cb.Ld.LdLinClosePlanPProofs
import Cb.Ld.LdLinCloseVLinProofs
import Cb.Ld.LdFrontOnProofs
import Cb.Ld.LdAltBProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- At a shared oracle message o (`ho`) where W has the shared part's pair (`h`), the message of W
is `C.shMsg s o`. -/
theorem LdLinC.shMsg_of (C : LdLinC E ι κ J Y) (d : C.S.Wit) (s : C.P.Sh6) (W : C.S.Wit) (o : C.S.O)
    (ho : C.isSh o) (h : W o = C.witS d s o) : C.S.msgs W o = C.shMsg s o := by
  show (W o).1 = _
  rw [h]
  rcases o with ((a | a) | a) | a
  · exact ho.elim
  · exact ho.elim
  · rfl
  · rfl

omit [Fintype ι] [Nonempty ι] in
theorem ldLinPV_tie : Spec.ldLinPV_tie E ι κ J Y := by
  intro C p T tie' x₀ y₀ Sn qa N s x y w hSh hP h hcar
  obtain ⟨⟨⟨⟨⟨⟨-, hrec⟩, hpt⟩, hσU, hyU, hwU⟩, hloc⟩, hσO, hyO, hwO⟩, hζ⟩ := h
  have hs : C.sh (C.toSt x) = C.shS s := by
    show (((x.1.1.1.1.1.1.2, x.1.1.1.1.2), x.1.1.2), x.2) =
      (((s.1.1.1.1.1.2, s.1.1.1.1.2), s.1.1.2), s.2)
    rw [hrec, hpt, hloc, hζ]
  have hB : ∀ o : C.S.O, C.isSh o →
      C.toSmp x o = C.smpS x₀ s o ∧
      (C.toE.map y).2 o = C.yrep y₀ s o ∧
      (C.toW w).1 o = C.witS T.d₁.1 s o := by
    intro o ho
    rcases o with ((a | a) | a) | a
    · exact ho.elim
    · exact ho.elim
    · exact ⟨congrFun hσU a, congrFun hyU a, congrFun hwU a⟩
    · exact ⟨congrFun hσO a, congrFun hyO a, congrFun hwO a⟩
  have hm : ∀ o, C.isSh o → C.S.msgs (C.toW w).1 o = C.shMsg s o := fun o ho =>
    LdLinC.shMsg_of E ι κ J Y C T.d₁.1 s _ o ho (hB o ho).2.2
  have hsg : splitVal p.k₀ p.fO (C.S.msgs (C.toW w).1) (C.sh (C.toSt x)) = T.sg s := by
    unfold LdLinPpT.sg splitVal
    rw [hs]
    have e1 : p.GO.msg (C.S.msgs (C.toW w).1) = p.GO.msg (C.shMsg s) :=
      funext fun n => congrFun (hm n.1.1 (hSh _ (Or.inr n.1.2))) n.2
    have e2 : p.k₀.val (C.S.msgs (C.toW w).1) = p.k₀.val (C.shMsg s) :=
      congrFun (hm p.k₀.o (hSh _ (Or.inr p.k₀.h₁))) p.k₀.j
    rw [e1, e2]
  refine ⟨⟨?_, ?_⟩, ⟨?_, hB⟩, ⟨?_, fun o ho => hB o.1 ho⟩, hcar⟩
  · exact ldSpV_reads C p.Rs₀ s (C.toW w).1 (fun a j hn => hP.rsSh _ hn)
      (fun a j hn => hP.rsSh _ hn) (fun a => congrFun hwU a) fun a => congrFun hwO a
  · show ((0 : E), (C.shS s, C.shS s)) = (0, (C.sh (C.toSt x), C.sh (C.toSt x)))
    rw [hs]
  · show ((Sum.elim (C.tgRC (C.sh (C.toSt x))) fun _ =>
          0 - splitVal p.k₀ p.fO (C.S.msgs (C.toW w).1) (C.sh (C.toSt x)),
        Sum.elim (fun _ => C.sh (C.toSt x)) fun _ => C.sh (C.toSt x)) :
        (C.Brc ⊕ Unit → E) × (C.Brc ⊕ Unit → C.Sh6)) = T.cl₁ s
    rw [hsg, hs]
    rfl
  · show oneClaim (splitVal p.k₀ p.fO (C.S.msgs (C.toW w).1) (C.sh (C.toSt x)), C.sh (C.toSt x)) =
      T.cl₂ s
    rw [hsg, hs]
    rfl

omit [Fintype ι] [Nonempty ι] in
theorem ldLinPV_plan : Spec.ldLinPV_plan E ι κ J Y := by
  intro C p T N q₀ b' tie' x₀ y₀ cA' same' xB xC yE QV' hSh hD₁ hD₂ hD₃ hQ'
  have her₀ : (QFam.each q₀ : QFam C.E₀ N).Her := (qfam_her C.E₀ C.E₀ N).1 q₀
  have hQ₃ := ldPlanV_cons_local E p.S₂ C.E₀ C.Wpa N T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃'
    ⟨C.P.Sh6, T.tie₃ tie', T.qB₂ N q₀ b'⟩ tie' (T.qB₃ N q₀ b') QV' hD₃ hQ' (fun _ _ _ h => h.2)
    (ldRunV_bears_local E p.S₂ T.D₃ _ _ C.E₀ T.Q'.base T.d₃ T.d₃' N _ _ hD₃
      (ldDemandV_local E p.S₂ T.D₃ _ _ C.E₀ T.Q'.base T.d₃ T.d₃' N (fun a => C.isSh a.1.1)
        (QFam.each q₀) b' (RoundSplits.allLocal _) hD₃))
    (ldDemandV_her E p.S₃ C.E₀ N _ (QFam.each q₀) b' her₀)
  have hQ₂ := ldPlanV_cons_shared E p.S₁ C.E₀ C.Wpa N T.D₂
    (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃') T.d₂ T.d₂'
    ⟨C.P.Sh6, T.tie₂ tie' x₀ y₀, T.qB₁ N q₀ b'⟩ C.P.Sh6 (T.tie₃ tie') (T.qB₂ N q₀ b')
    (T.rep₂ x₀ xC) (fun s a => C.yrep y₀ s a.1) id yE _ hD₂ hQ₃
    (fun x y w h => by
      obtain ⟨⟨h1, h2⟩, -⟩ := h.2
      refine ⟨?_,
        p.G₂.wit_congr _ _ fun o ho => (h2 o (hSh _ (Or.inr ho))).2.2,
        fun a => (h2 a.1 (hSh _ (Or.inr a.2))).2.1⟩
      rw [h1]
      exact p.G₂.claims_congr _ _ _ fun o ho => (h2 o (hSh _ (Or.inr ho))).1)
    (fun _ _ _ h => h.2.2)
    (ldRunV_bears_shared E p.S₁ T.D₂ _ _ C.E₀ _ T.d₂ T.d₂' N _ _ hD₂
      (ldDemandV_shared E p.S₁ T.D₂ _ _ C.E₀ _ T.d₂ T.d₂' N (fun a => C.isSh a.1) (QFam.each q₀)
        (T.D₃.needV N (fun a => C.isSh a.1.1) b') hD₂))
    (ldDemandV_her E p.S₂ C.E₀ N _ (QFam.each q₀) _ her₀)
  exact ldPlanV_cons_shared E C.S C.E₀ C.Wpa N T.D₁
    (LdTcA.consSh T.D₂ (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃') T.d₂ T.d₂') T.d₁ T.d₁'
    ⟨C.P.Sh6, T.tie₁ tie' x₀ y₀, T.qB₀ N q₀ b'⟩ C.P.Sh6 (T.tie₂ tie' x₀ y₀) (T.qB₁ N q₀ b')
    (T.rep₁ x₀ xB) (C.yrep y₀) id yE _ hD₁ hQ₂
    (fun x y w h => by
      obtain ⟨⟨h1, h2⟩, -⟩ := h.2
      refine ⟨?_,
        p.GU.wit_congr _ _ fun o ho => (h2 o (hSh _ (Or.inl ho))).2.2,
        fun a => (h2 a.1 (hSh _ (Or.inl a.2))).2.1⟩
      rw [h1]
      exact p.GU.claims_congr _ _ _ fun o ho => (h2 o (hSh _ (Or.inl ho))).1)
    (fun _ _ _ h => h.2.2)
    (ldRunV_bears_shared E C.S T.D₁ _ _ C.E₀ _ T.d₁ T.d₁' N _ _ hD₁
      (ldDemandV_shared E C.S T.D₁ _ _ C.E₀ _ T.d₁ T.d₁' N C.isSh (QFam.each q₀)
        (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b')) hD₁))
    (ldDemandV_her E p.S₁ C.E₀ N _ (QFam.each q₀) _ her₀)

theorem ldLinPV_all : Spec.ldLinPV_all E ι κ J Y := by
  intro C p T N q₀ b' tie' x₀ y₀ cA' same' xB xC yE QV' Sn qa ba on0 εf sh₀ hSh hP hK hrest hA hD₁
    hD₂ hD₃ hQ' hcar hqa h1 h2 h3 h4 hF
  have her₀ : (QFam.each q₀ : QFam C.E₀ N).Her := (qfam_her C.E₀ C.E₀ N).1 q₀
  have herB : (T.qB₀ N q₀ b').Her := ldDemandV_her E C.S C.E₀ N _ (QFam.each q₀) _ her₀
  have hSays : C.Says (p.x₁ T.Q'.base).A (C.fqP T.fa) :=
    ldLinPp_says E ι κ J Y C p _ T.Q'.base T.fa hrest hA
  obtain ⟨g, hH⟩ := ldLinVS_good E ι κ J Y C _ (p.x₁ T.Q'.base).A (C.fqP T.fa) hSays
  have hstep : ((C.link (C.fqP T.fa) (T.QA cA' same').Q.base).loV
      N (C.P.V6 Sn qa N) (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b')).PV :=
    linkLoV_pv Unit _ _ (C.link (C.fqP T.fa) (p.x₁ T.Q'.base).A) N (C.P.V6 Sn qa N)
      (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b') g hH
      (fun x y w _ _ h _ =>
        ldLinPV_tie E ι κ J Y C p T tie' x₀ y₀ Sn qa N w.1 x y w.2 hSh hP h.2 (hcar x y w h))
      (ldLinVS_bears E ι κ J Y C _ (p.x₁ T.Q'.base).A (C.fqP T.fa) N _ _
        (ldDemandV_step E ι κ J Y C _ (p.x₁ T.Q'.base).A (C.fqP T.fa) Sn qa N q₀ ba _
          (RoundSplits.allLocal _) hqa h1 h2 h3 h4)) herB
  have hplan :=
    ldLinPV_plan E ι κ J Y C p T N q₀ b' tie' x₀ y₀ cA' same' xB xC yE QV' hSh hD₁ hD₂ hD₃ hQ'
  have hfront : (T.cVf N q₀ b' tie' x₀ y₀).OkFromV
      ((C.P.chainV Sn qa N on0 εf).snoc
        ((C.link (C.fqP T.fa) (p.x₁ T.Q'.base).A).loV
          N (C.P.V6 Sn qa N) (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b'))) :=
    frontOn_sh E C.S C.E₀ C.Wpa p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU _ (p.Ar₁ T.Q'.base) p.Rs₀
      inferInstance ⟨_, p.base₁ T.Q'.base⟩ T.fF N C.P.Sh6 (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b') T.rd
      (0, (sh₀, sh₀)) (T.tie₁ tie' x₀ y₀) _ _ _ (ldLinPp_hyp E ι κ J Y C p _ T.Q'.base hP hK) herB
      (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hF
  have hQV : (T.QV N q₀ b' tie' x₀ y₀ cA' same' xB xC QV').OkBehindV
      ((C.P.chainV Sn qa N on0 εf).snoc
        ((C.link (C.fqP T.fa) (T.QA cA' same').Q.base).loV
          N (C.P.V6 Sn qa N) (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b'))) :=
    ldAltV_front E C.S C.E₀ C.Wpa N (p.x₁ T.Q'.base)
      (LdTcA.consSh T.D₁
        (LdTcA.consSh T.D₂ (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃') T.d₂ T.d₂') T.d₁ T.d₁')
      T.front (T.front.cA true) (frontB_forget E _ _ _ _ _ T.front true)
      ⟨C.P.Sh6, T.tieF tie' x₀ y₀, T.qB₀ N q₀ b'⟩
      ⟨C.P.Sh6, T.tie₁ tie' x₀ y₀, T.qB₀ N q₀ b'⟩ (T.cVf N q₀ b' tie' x₀ y₀)
      (frontOn_forget E C.S C.E₀ C.Wpa p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU _ (p.Ar₁ T.Q'.base)
        p.Rs₀ inferInstance ⟨_, p.base₁ T.Q'.base⟩ T.fF N C.P.Sh6 (T.tieF tie' x₀ y₀)
        (T.qB₀ N q₀ b') T.rd (T.tie₁ tie' x₀ y₀))
      (T.QVt N q₀ b' tie' x₀ y₀ cA' same' xB xC QV') _ _
      ((C.P.chainV Sn qa N on0 εf).snoc
        ((C.link (C.fqP T.fa) (p.x₁ T.Q'.base).A).loV
          N (C.P.V6 Sn qa N) (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b')))
      hfront (frontB_coh E _ _ _ _ _ T.front true)
      (ldAltV_of_ok E C.S C.E₀ C.Wpa N _ _ _ _ _ _ hplan)
  obtain ⟨a1, a2, a3⟩ := ldAltV_cZ E ι κ J Y C N (T.QA cA' same') (C.fqP T.fa) (C.P.V6 Sn qa N)
    (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b') (T.QV N q₀ b' tie' x₀ y₀ cA' same' xB xC QV') _ _
    (C.P.chainV Sn qa N on0 εf) hstep hQV
  have hsame := ldLinV_cZ_same E ι κ J Y C N (T.QA cA' same') (C.fqP T.fa) (C.P.V6 Sn qa N)
    (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b') (T.QV N q₀ b' tie' x₀ y₀ cA' same' xB xC QV')
  exact ⟨a1, a2, a3, hsame.1, hsame.2⟩

end

theorem ldLinPV_std (F E ι κ J Y : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] :
    Spec.ldLinPV_std F E ι κ J Y := by
  intro C p T N q₀ b' tie' x₀ y₀ cA' same' xB xC yE QV' Ts LW LU LO tW tU tO n₀ qa ba on0 εf sh₀ x₄
    y₄ hSh hP hK hrest hA hD₁ hD₂ hD₃ hQ' hcar hqa h1 h2 h3 h4 hPl hW hU hO hk hR
  exact ldLinPV_all E ι κ J Y C p T N q₀ b' tie' x₀ y₀ cA' same' xB xC yE QV'
    (Ts.snd LW LU LO tW tU tO) qa ba on0 εf sh₀ hSh hP hK hrest hA hD₁ hD₂ hD₃
    hQ' hcar hqa h1 h2 h3 h4
    (ldSpV_fresh F E ι κ J Y C Ts LW LU LO tW tU tO on0 εf N qa x₄ y₄ p.GO p.GU p.k₀
      p.Rs₀ _ _ n₀ _ (C.fqP T.fa) (p.x₁ T.Q'.base).A (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b')
      hPl hW hU hO hk (hk ▸ hP.rs₀K) hR)

end Cb
