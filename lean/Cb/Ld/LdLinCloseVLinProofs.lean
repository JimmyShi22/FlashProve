-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseVLinProofs.lean: the proofs of the statements of Cb/Ld/LdLinCloseVLin.lean (the
closing of the test for linear constraints in a batch, at the plan without a splitting: the honest
side). An assembly.

How the proofs go:
`ldLinVL_tie`: the step re-brackets and lays the rows' targets and states (`C.fq`); each clause of
the tie over the one signature follows from clauses of the core's tie. `ldLinVL_act`: the rows that
a test takes in read the samples of its members only, its prover the members' pairs only; all
members of the first group are shared (the hypothesis `p.Shared`), and the tie says what the shared
part holds of these.

Main names (statements and hypotheses: Cb/Ld/LdLinCloseVLin.lean):
  `ldLinVL_tie`: the step without rounds and the core's tie.
  `ldLinVL_act`: the first test's acting part on tied statements.
  `ldLinVL_plan`: `OK` of the honest side of the plan.
  `ldLinVL_all`: all that the whole test asks of its closing on the honest side of a batch.

Limits: what the head of Cb/Ld/LdLinCloseVLin.lean lists as not said is not said here either.
-/
import Cb.Ld.LdLinCloseVLin

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the rows that a test takes in read the samples of its members only -/
theorem Grp.claims_congr {E : Type} {S : Sig E} (G : Grp S) {B : Type} {Sb : B → Type}
    (x : (B → E) × (∀ b, Sb b)) (σ σ' : S.Smp) (h : ∀ o, G.mem o → σ o = σ' o) :
    G.claims x σ = G.claims x σ' := by
  refine Prod.ext (funext fun ν => ?_) (funext fun ν => ?_)
  · cases ν with
    | inl b => rfl
    | inr as =>
      show (σ as.1.1).2 as.2 = (σ' as.1.1).2 as.2
      rw [h as.1.1 as.1.2]
  · cases ν with
    | inl b => rfl
    | inr as =>
      show (σ as.1.1).1 = (σ' as.1.1).1
      rw [h as.1.1 as.1.2]

/-- the members' pairs -/
theorem Grp.wit_congr {E : Type} {S : Sig E} (G : Grp S)
    (w w' : S.Wit) (h : ∀ o, G.mem o → w o = w' o) : G.wit w = G.wit w' := by
  refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
  · show (w n.1.1).1 n.2 = (w' n.1.1).1 n.2
    rw [h n.1.1 n.1.2]
  · show (w n.1.1).2 n.2 = (w' n.1.1).2 n.2
    rw [h n.1.1 n.1.2]

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Fintype ι] [Nonempty ι] in
theorem ldLinVL_tie : Spec.ldLinVL_tie E ι κ J Y := by
  intro C St' fa Sn qa N s x y w h
  obtain ⟨⟨⟨⟨⟨⟨-, hrec⟩, hpt⟩, hσU, hyU, hwU⟩, hloc⟩, hσO, hyO, hwO⟩, hζ⟩ := h
  have hs : C.sh (C.toSt x) = C.shS s := by
    show (((x.1.1.1.1.1.1.2, x.1.1.1.1.2), x.1.1.2), x.2) =
      (((s.1.1.1.1.1.2, s.1.1.1.1.2), s.1.1.2), s.2)
    rw [hrec, hpt, hloc, hζ]
  refine ⟨?_,
    fun a => ⟨congrFun hσU a, congrFun hyU a, congrFun hwU a⟩,
    fun a => ⟨congrFun hσO a, congrFun hyO a, congrFun hwO a⟩⟩
  show (C.tg₁ (C.sh (C.toSt x)), fun _ => C.sh (C.toSt x)) = _
  rw [hs]

omit [Fintype ι] [Nonempty ι] in
theorem ldLinVL_act : Spec.ldLinVL_act E ι κ J Y := by
  intro C p T x₀ y₀ s x y w hSh ⟨h1, hU, hO⟩
  refine ⟨?_, p.G₁.wit_congr _ _ fun o ho => ?_, fun a => ?_⟩
  · rw [h1]
    refine p.G₁.claims_congr _ _ _ fun o ho => ?_
    rcases hSh o ho with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact (hU a).1
    · exact (hO a).1
  · rcases hSh o ho with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact (hU a).2.2
    · exact (hO a).2.2
  · obtain ⟨o, ho⟩ := a
    rcases hSh o ho with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact (hU a).2.1
    · exact (hO a).2.1

omit [Fintype ι] [Nonempty ι] in
theorem ldLinVL_plan : Spec.ldLinVL_plan E ι κ J Y := by
  intro C p T N q₀ b' tie' cA' same' x₀ y₀ QV' hSh hD₁ hD₂ hQ'
  have her₀ : (QFam.each q₀ : QFam C.E₀ N).Her := (qfam_her C.E₀ C.E₀ N).1 q₀
  have hQ₁ := ldPlanV_cons_local E p.S₁ C.E₀ C.Wpa N T.D₂ ⟨T.Q', cA', same'⟩ T.d₂ T.d₂'
    ⟨C.P.Sh6, T.tie₁ tie', T.qB₁ N q₀ b'⟩ tie' (p.qB₂ N q₀ b') QV' hD₂ hQ' (fun _ _ _ h => h.2)
    (ldRunV_bears_local E p.S₁ T.D₂ _ _ C.E₀ T.Q'.base T.d₂ T.d₂' N _ _ hD₂
      (ldDemandV_local E p.S₁ T.D₂ _ _ C.E₀ T.Q'.base T.d₂ T.d₂' N (fun a => C.isSh a.1)
        (QFam.each q₀) b' (RoundSplits.allLocal _) hD₂))
    (ldDemandV_her E p.S₂ C.E₀ N _ (QFam.each q₀) b' her₀)
  exact ldPlanV_cons_shared E C.S C.E₀ C.Wpa N T.D₁
    (LdTcA.consLo T.D₂ ⟨T.Q', cA', same'⟩ T.d₂ T.d₂') T.d₁ T.d₁'
    ⟨C.P.Sh6, T.tie₀ tie', T.qB₀ N q₀ b'⟩ C.P.Sh6 (T.tie₁ tie') (T.qB₁ N q₀ b')
    (fun s => (T.repX x₀ s, T.repW s)) (C.yrep y₀.2) id y₀.1 _ hD₁ hQ₁
    (fun x y w h => ldLinVL_act E ι κ J Y C p T x₀ y₀.2 w.1 x y w.2 hSh h.2.1)
    (fun _ _ _ h => h.2.2)
    (ldRunV_bears_shared E C.S T.D₁ _ _ C.E₀ _ T.d₁ T.d₁' N _ _ hD₁
      (ldDemandV_shared E C.S T.D₁ _ _ C.E₀ _ T.d₁ T.d₁' N C.isSh (QFam.each q₀)
        (T.D₂.needV N (fun a => C.isSh a.1) b') hD₁))
    (ldDemandV_her E p.S₁ C.E₀ N _ (QFam.each q₀) _ her₀)

theorem ldLinVL_all : Spec.ldLinVL_all E ι κ J Y := by
  intro C p T N q₀ b' tie' cA' same' x₀ y₀ QV' Sn qa ba hSh hrest hA hD₁ hD₂
    hQ' hcar hqa h1 h2 h3 h4
  have her₀ : (QFam.each q₀ : QFam C.E₀ N).Her := (qfam_her C.E₀ C.E₀ N).1 q₀
  have hSays : C.Says T.Q.base T.fq := ldLinPlan_says E ι κ J Y C p _ T.Q'.base T.fa hrest hA
  obtain ⟨g, hH⟩ := ldLinVS_good E ι κ J Y C _ T.Q.base T.fq hSays
  have hstep : ((C.link T.fq (T.QA cA' same').Q.base).loV
      N (C.P.V6 Sn qa N) (T.tie₀ tie') (T.qB₀ N q₀ b')).PV :=
    linkLoV_pv Unit _ _ (C.link T.fq T.Q.base) N (C.P.V6 Sn qa N) (T.tie₀ tie') (T.qB₀ N q₀ b') g hH
      (fun x y w _ _ h _ => ⟨ldLinVL_tie E ι κ J Y C _ T.fa Sn qa N w.1 x y w.2 h.2, hcar x y w h⟩)
      (ldLinVS_bears E ι κ J Y C _ T.Q.base T.fq N _ _
        (ldDemandV_step E ι κ J Y C _ T.Q.base T.fq Sn qa N q₀ ba _
          (RoundSplits.allLocal _) hqa h1 h2 h3 h4))
      (ldDemandV_her E C.S C.E₀ N _ (QFam.each q₀) _ her₀)
  have hplan := ldLinVL_plan E ι κ J Y C p T N q₀ b' tie' cA' same' x₀ y₀ QV' hSh hD₁ hD₂ hQ'
  have hsame := ldLinV_cZ_same E ι κ J Y C N (T.QA cA' same') T.fq (C.P.V6 Sn qa N) (T.tie₀ tie')
    (T.qB₀ N q₀ b') (T.QV N q₀ b' tie' cA' same' x₀ QV')
  refine ⟨fun Z VZ c₀ =>
      (ldLinV_cZ_ok E ι κ J Y C N (T.QA cA' same') T.fq (C.P.V6 Sn qa N) (T.tie₀ tie')
        (T.qB₀ N q₀ b') (T.QV N q₀ b' tie' cA' same' x₀ QV') Z VZ c₀ hstep hplan).1,
    ?_, hQ'.2.2, hsame.1, hsame.2⟩
  exact (ldLinV_cZ_ok E ι κ J Y C N (T.QA cA' same') T.fq (C.P.V6 Sn qa N) (T.tie₀ tie')
    (T.qB₀ N q₀ b') (T.QV N q₀ b' tie' cA' same' x₀ QV') (C.P.J0 fun _ _ => True)
    (C.P.V0 qa N fun _ _ => True) (C.P.chainV Sn qa N (fun _ _ => True) 0) hstep hplan).2.1

end
end Cb
