-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollRulesFrameProofs.lean: proofs of the statements of Ior/KnowCollRulesFrame.lean, each
proved as it is stated there.

Main names (statements and hypotheses: Ior/KnowCollRulesFrame.lean):
  `goodB_mapW`: the general change of joints on one IOR.
  `goodB_beside`, `goodT_beside`: see their statements in Ior/KnowCollRulesFrame.lean.

The proofs go field by field, as in Ior/FrameProofsBasic.lean and Ior/FrameProofs.lean; the parts on
locality and on honest-verifier exact zero knowledge (`Honest.Exact`, Ior/Honest.lean) are those
files' (`IsLocal.keepE`, `IsLocal.pre`, `IsLocal.post`, `Honest.Exact.keepE`, `Honest.Exact.pre`,
`Honest.Exact.post`, `carry_output`, `keepX_output`; `Honest.mapW_output`, `exact_conseq`, and these
parts of `goodB_keepX`, `exact_keepX` and `goodT_pure` are proved here).

Limits: see Limits in the head of Ior/KnowCollRulesFrame.lean.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollRulesFrame
import Ior.FrameProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} {Wi Wi' Wo Wo' : Type}

theorem Honest.mapW_run (H : R.Honest Wi Wo) (fi : Wi' → Wi) (fo : Wi' → Wo → Wo') (w : Wi')
    (x : Xi) (c : H.Coin) (ρ : Rho R.shape) :
    ((H.mapW fi fo).strat w x c).run ρ =
      (((H.strat (fi w) x c).run ρ).1,
        (((H.strat (fi w) x c).run ρ).2.1, fo w ((H.strat (fi w) x c).run ρ).2.2)) :=
  Strat.run_map _ _ _

/-- With the witness re-typed the run shows the same. -/
theorem Honest.mapW_output (H : R.Honest Wi Wo) (fi : Wi' → Wi) (fo : Wi' → Wo → Wo') (w : Wi')
    (x : Xi) (ρ : Rho R.shape) (T : Finset (OPos R.shape)) :
    (H.mapW fi fo).output w x ρ T = H.output (fi w) x ρ T := by
  by_cases h : ρ ∈ H.withheld (fi w) x
  · rw [H.output_of_mem T h]
    exact (H.mapW fi fo).output_of_mem T h
  · rw [H.output_of_not_mem T h]
    refine ((H.mapW fi fo).output_of_not_mem T h).trans ?_
    refine congrArg (fun f => PMF.map f (unif H.Coin)) (funext fun c => ?_)
    rw [mapW_run]

end IOR

open IOR

theorem exact_mapW :
    Spec.exact_mapW := fun _ _ _ _ _ _ _ _ _ H fi fo _ _ _ _ hR hS x y w hw ρ hρ T hT =>
  (H.mapW_output fi fo w x ρ T).trans (hS x y (fi w) (hR x y w hw) ρ hρ T hT)

theorem goodB_mapW : Spec.goodB_mapW := by
  intro K K' Xi Xo Ei Eo R Wi Wi' Wo Wo' H A B A' B' ext ext' P cov' fi fo bo g hA hB
    hoA hoB hk hc hp hb1 hb2
  exact
    { point := g.point
      isLocal := g.isLocal
      acc := by
        intro x y w c ρ hR hρ
        rw [Honest.mapW_run]
        exact ⟨(g.acc x y (fi w) c ρ (hA x y w hR) hρ).1,
          hB x y w c ρ hR hρ (g.acc x y (fi w) c ρ (hA x y w hR) hρ).2⟩
      onOut := fun a τ b ha hb => hoB a τ b ha hb (g.onOut a τ b (hoA a ha) hb)
      keeps := by
        intro w x c ρ
        rw [Honest.mapW_run]
        exact hk w x c ρ
      prBad := g.prBad
      cover := hc
      prCov := hp
      know := fun a ha =>
        Doomed.mono _ _
          (fun τ hτ b w hb hw => hb2 a τ b w ha hb hw (hτ b (bo w) hb (hb1 a τ b w ha hb hw)))
          (g.know a (hoA a ha)) }

theorem exact_conseq : Spec.exact_conseq :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hR hb hS x y w hw ρ hρ T hT =>
    hS x y w (hR x y w hw) ρ hρ T (hb ρ T hT)

theorem goodB_and : Spec.goodB_and := by
  intro K Xi Xo Ei Eo R Wi Wo H A B ext P S SR T S' SR' T' g hS hSR hT
  exact
    { point := g.point
      isLocal := g.isLocal
      acc := fun x y w c ρ hR hρ =>
        ⟨(g.acc x y w c ρ hR.1 hρ).1,
          (g.acc x y w c ρ hR.1 hρ).2,
          hS x y w c ρ hR.1 hR.2 hρ (g.acc x y w c ρ hR.1 hρ).2⟩
      onOut := fun a τ b ha hb => ⟨g.onOut a τ b ha.1 hb, hT a τ b ha.1 ha.2 hb⟩
      keeps := g.keeps
      prBad := g.prBad
      cover := g.cover
      prCov := g.prCov
      know := fun a ha =>
        Doomed.mono _ _
          (fun τ hτ b w hb hw =>
            ⟨hτ b w hb hw.1, hSR a τ b w ha.1 ha.2 hb hw.1 (hτ b w hb hw.1) hw.2⟩)
          (g.know a ha.1) }

theorem goodB_carry : Spec.goodB_carry := by
  intro K Xi Xo Ei Eo R Wi Wo Wz H A B ext P upd g
  exact
    { point := g.point
      isLocal := g.isLocal
      acc := by
        intro x y w c ρ hR hρ
        rw [Honest.carry_run]
        exact g.acc x y w.1 c ρ hR hρ
      onOut := g.onOut
      keeps := by
        intro w x c ρ
        rw [Honest.carry_run]
        show (B.core _, w.2) = (A.core w.1, w.2)
        rw [g.keeps]
      prBad := g.prBad
      cover := fun w x => g.cover w.1 x
      prCov := fun k => g.prCov k.1
      know := fun a ha => Doomed.mono _ _ (fun τ hτ b w hb hw => hτ b w.1 hb hw) (g.know a ha) }

theorem exact_carry : Spec.exact_carry := fun _ _ _ _ _ _ _ Wz H _ _ _ hS x y w hw ρ hρ T hT =>
  (H.carry_output Wz w x ρ T).trans (hS x y w.1 hw ρ hρ T hT)

theorem goodB_frame : Spec.goodB_frame := by
  intro K Xi Xo Ei Eo R Wi Wo Wz H A B ext P upd S SR T S' SR' T' g hS hSR hT
  refine goodB_and (K × Wz) Xi Xo Ei Eo R (Wi × Wz) (Wo × Wz) (H.carry Wz) (A.lift Wz) (B.lift Wz)
    (fun a τ w => (ext a τ w.1, upd a τ w.1 w.2)) (P.carry Wz) (fun x y w => S x y w.1 w.2)
    (fun a w => SR a w.1 w.2) T (fun x y w => S' x y w.1 w.2) (fun b w => SR' b w.1 w.2) T'
    (goodB_carry K Xi Xo Ei Eo R Wi Wo Wz H A B ext P upd g) ?_ ?_ hT
  · intro x y w c ρ hR hs hρ hB
    rw [Honest.carry_run] at hB ⊢
    exact hS x y w.1 w.2 c ρ hR hs hρ hB
  · intro a τ b w ha ht hb hB hA hs
    exact hSR a τ b w.1 w.2 ha ht hb hB hA hs

theorem goodB_recore : Spec.goodB_recore := by
  intro K K' Xi Xo Ei Eo R Wi Wo H A B ext P κi κo cov g hk hc hp
  exact
    { point := g.point
      isLocal := g.isLocal
      acc := g.acc
      onOut := g.onOut
      keeps := hk
      prBad := g.prBad
      cover := hc
      prCov := hp
      know := g.know }

theorem goodB_keepX : Spec.goodB_keepX := by
  intro K Xi Xo Z Ei Eo R Wi Wo H A B ext P g
  exact
    { point := g.point
      isLocal :=
        { out := by
            intro a y y' τ τ' hρ hπ hE hO
            show (R.out a.1 y τ).map _ = (R.out a.1 y' τ').map _
            rw [g.isLocal.out a.1 y y' τ τ' hρ hπ hE hO]
          imp := g.isLocal.imp }
      acc := by
        intro a y w c ρ hR hρ
        have h := g.acc a.1 y w c ρ hR hρ
        rw [Honest.keepX_run]
        refine ⟨?_, h.2⟩
        show (R.out a.1 y _).map _ = _
        rw [h.1]
        rfl
      onOut := fun a τ b ha hb =>
        g.onOut (a.1.1, a.2) τ (b.1.1, b.2) ha (keepX_red_out R Z a τ b hb).2
      keeps := by
        intro w a c ρ
        rw [Honest.keepX_run]
        exact g.keeps w a.1 c ρ
      prBad := g.prBad
      cover := fun w a => g.cover w a.1
      prCov := g.prCov
      know := fun a ha =>
        Doomed.mono _ _ (fun τ hτ b w hb hw => hτ (b.1.1, b.2) w (keepX_red_out R Z a τ b hb).2 hw)
          (g.know (a.1.1, a.2) ha) }

theorem exact_keepX : Spec.exact_keepX := by
  intro Xi Xo Z Ei Eo R Wi Wo H Ri bud h
  obtain ⟨Sm, hSm⟩ := h
  refine ⟨fun a ρ U ans => (Sm a.1 ρ U ans).map (Option.map (viewKeepX R Z)),
    fun a y w hw ρ hρ U hU => ?_⟩
  rw [Honest.keepX_output, hSm a.1 y w hw ρ hρ U hU]
  rfl

theorem goodB_keepE : Spec.goodB_keepE := by
  intro K Xi Xo Ei Eo F R Wi Wo H A B ext P hG
  refine ⟨hG.point, hG.isLocal.keepE F, ?_, ?_, hG.keeps, hG.prBad, hG.cover, hG.prCov, ?_⟩
  · intro x y w c ρ hR hρ
    exact hG.acc x y.1 w c ρ hR hρ
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    exact hG.onOut (a.1, a.2.1) τ (b.1, b.2.1) ha (red_out_eq_some.2 ⟨h1, congrArg Prod.fst h2⟩)
  · intro a ha
    refine Doomed.mono _ _ ?_ (hG.know (a.1, a.2.1) ha)
    intro τ hτ b w hb hw
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    exact hτ (b.1, b.2.1) w (red_out_eq_some.2 ⟨h1, congrArg Prod.fst h2⟩) hw

theorem exact_keepE : Spec.exact_keepE := fun _ _ _ _ F _ _ _ _ _ _ h => h.keepE F

theorem goodB_keep_frame : Spec.goodB_keep_frame := by
  intro K Xi Xo Z Ei Eo F R Wi Wo Wz H A B ext P S SR T hG
  have h1 := goodB_keepE K (Xi × Z) (Xo × Z) Ei Eo F (R.keepX Z) Wi Wo (H.keepX Z) (A.keepX Z)
    (B.keepX Z) (fun a τ w => ext (a.1.1, a.2) τ w) (P.keepX Z)
    (goodB_keepX K Xi Xo Z Ei Eo R Wi Wo H A B ext P hG)
  refine goodB_frame K (Xi × Z) (Xo × Z) (Ei.prod F) (Eo.prod F) (R.keep Z F) Wi Wo Wz
    (H.keep Z F) (A.keep Z F) (B.keep Z F) (fun a τ w => ext (a.1.1, a.2.1) τ w) (P.keep Z F)
    (fun _ _ _ z => z) (fun a y _ z => S a.2 y.2 z) (fun a _ z => SR a.1.2 a.2.2 z)
    (fun a => T a.1.2 a.2.2) (fun a y _ z => S a.2 y.2 z) (fun a _ z => SR a.1.2 a.2.2 z)
    (fun a => T a.1.2 a.2.2) h1 ?_ ?_ ?_
  · intro a y w z c ρ _ hS _ _
    have e := (keep_copies Xi Xo Ei Eo R).2.2.1 Z Wi Wo H w a c ρ
    show S (((H.keepX Z).strat w a c).run ρ).2.1.2 y.2 z
    rw [e]
    exact hS
  · intro a τ b _ z _ _ hb _ _ hSR
    obtain ⟨e2, hb'⟩ := (keep_copies (Xi × Z) (Xo × Z) Ei Eo (R.keepX Z)).2.1 F a τ b hb
    obtain ⟨e1, _⟩ := (keep_copies Xi Xo Ei Eo R).1 Z _ τ _ hb'
    show SR a.1.2 a.2.2 z
    rw [← e2, ← (show b.1.2 = a.1.2 from e1)]
    exact hSR
  · intro a τ b _ hT hb
    obtain ⟨e2, hb'⟩ := (keep_copies (Xi × Z) (Xo × Z) Ei Eo (R.keepX Z)).2.1 F a τ b hb
    obtain ⟨e1, _⟩ := (keep_copies Xi Xo Ei Eo R).1 Z _ τ _ hb'
    show T b.1.2 b.2.2
    rw [e2, (show b.1.2 = a.1.2 from e1)]
    exact hT

theorem goodB_beside : Spec.goodB_beside := by
  intro K Xi Xo Z Ei Eo F R Wi Wo Wz H A B ext P S g
  have h := goodB_keep_frame Unit Xi Xo Z Ei Eo F R Wi Wo Wz H A B ext P S.rel
    (fun z f wz => S.relR (z, f) wz) (fun z f => S.on (z, f)) g
  exact
    { point := h.point
      isLocal := h.isLocal
      acc := h.acc
      onOut := h.onOut
      keeps := by
        intro w x c ρ
        have e := h.keeps w x c ρ
        exact congrArg S.core (congrArg Prod.snd e)
      prBad := h.prBad
      cover := fun w x => h.cover w x
      prCov := fun _ => g.prCov ()
      know := h.know }

theorem exact_beside : Spec.exact_beside := by
  intro Xi Xo Z Ei Eo F R Wi Wo Wz H Ri bud h
  obtain ⟨S, hS⟩ := exact_keepE (Xi × Z) (Xo × Z) Ei Eo F (R.keepX Z) Wi Wo (H.keepX Z)
    (fun a y w => Ri a.1 y w) bud (exact_keepX Xi Xo Z Ei Eo R Wi Wo H Ri bud h)
  exact ⟨S, exact_carry (Xi × Z) (Xo × Z) (Ei.prod F) (Eo.prod F) (R.keep Z F) Wi Wo Wz (H.keep Z F)
      (fun a y w => Ri a.1 y.1 w) bud S hS⟩

theorem goodT_beside : Spec.goodT_beside := by
  intro K Xi Xo Z Ei Eo F R Wi Wo Wz H A B ext P S g
  obtain ⟨gb, ge⟩ := (goodT_iff Unit Xi Xo Ei Eo R Wi Wo H A B ext P).1 g
  refine (goodT_iff K (Xi × Z) (Xo × Z) (Ei.prod F) (Eo.prod F) (R.keep Z F) (Wi × Wz) (Wo × Wz)
      ((H.keep Z F).carry Wz) (A.beside S) (B.beside S) _ (P.beside K Z F)).2
    ⟨goodB_beside K Xi Xo Z Ei Eo F R Wi Wo Wz H A B ext P S gb, ?_⟩
  obtain ⟨Sm, hSm⟩ := exact_beside Xi Xo Z Ei Eo F R Wi Wo Wz H A.rel P.bud ge
  exact ⟨Sm, fun x y w hw ρ hρ T hT => hSm x y w hw.1 ρ hρ T hT⟩

theorem goodB_pre : Spec.goodB_pre := by
  intro K Xi Xi' Xo Ei Ei' Eo R Wi Wi' Wo H A' A B ext ext' P f g m back hS hG he
  refine ⟨hG.point, hG.isLocal.pre f g hS.isLocal, ?_, ?_, ?_, hG.prBad, ?_, hG.prCov, ?_⟩
  · intro x y w c ρ hR hρ
    obtain ⟨hf, hA⟩ := hS.acc x y w hR
    obtain ⟨ho, hb⟩ := hG.acc _ _ _ c ρ hA hρ
    refine ⟨?_, hb⟩
    show (f x).bind (fun x₁ => R.out x₁ (g.map y) _) = _
    rw [hf]
    exact ho
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨x₁, hx₁, ho⟩ := Option.bind_eq_some_iff.1 h1
    exact hG.onOut (x₁, g.map a.2) τ b (hS.onOut a.1 a.2 x₁ ha hx₁) (red_out_eq_some.2 ⟨ho, h2⟩)
  · intro w x c ρ
    exact (hG.keeps _ _ c ρ).trans (hS.keeps x w)
  · intro w x
    have := hG.cover (m (x, w)).2 (m (x, w)).1
    rw [hS.keeps x w] at this
    exact this
  · intro a ha
    cases hf : f a.1 with
    | none =>
        refine Doomed.of_forall _ _ fun τ b w hb _ => ?_
        obtain ⟨h1, _⟩ := red_out_eq_some.1 hb
        obtain ⟨x₁, hx₁, _⟩ := Option.bind_eq_some_iff.1 h1
        rw [hf] at hx₁
        cases hx₁
    | some x₁ =>
        have hon := hS.onOut a.1 a.2 x₁ ha hf
        refine Doomed.mono _ _ ?_ (hG.know (x₁, g.map a.2) hon)
        intro τ hτ b w hb hw
        obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
        obtain ⟨x₁', hx₁', ho⟩ := Option.bind_eq_some_iff.1 h1
        rw [hf] at hx₁'
        cases hx₁'
        rw [he a x₁ τ w hf]
        exact hS.know a.1 a.2 x₁ _ ha hf (hτ b w (red_out_eq_some.2 ⟨ho, h2⟩) hw)

theorem exact_pre : Spec.exact_pre := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ f g m hg hm h =>
  h.pre f g hg m hm

theorem goodB_post : Spec.goodB_post := by
  intro K Xi Xo Xo' Ei Eo Eo' R Wi Wo Wo' H A B B' ext ext' P f g m back hG hS he
  refine ⟨hG.point, hG.isLocal.post f g hS.isLocal, ?_, ?_, ?_, hG.prBad, hG.cover, hG.prCov, ?_⟩
  · intro x y w c ρ hR hρ
    obtain ⟨ho, hb⟩ := hG.acc x y w c ρ hR hρ
    obtain ⟨hf, hb'⟩ := hS.acc _ _ _ hb
    show (R.out x y ((Strat.map m (H.strat w x c)).run ρ).1).bind f =
        some ((Strat.map m (H.strat w x c)).run ρ).2.1 ∧
      B'.rel ((Strat.map m (H.strat w x c)).run ρ).2.1
        (g.map (R.imp y ((Strat.map m (H.strat w x c)).run ρ).1))
        ((Strat.map m (H.strat w x c)).run ρ).2.2
    rw [Strat.run_map]
    exact ⟨by rw [ho]; exact hf, hb'⟩
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨xo, hxo, hf⟩ := Option.bind_eq_some_iff.1 h1
    have hon := hG.onOut a τ (xo, R.imp a.2 τ) ha (red_out_eq_some.2 ⟨hxo, rfl⟩)
    have := hS.onOut xo (R.imp a.2 τ) b.1 hon hf
    rw [show b = (b.1, g.map (R.imp a.2 τ)) from Prod.ext rfl h2]
    exact this
  · intro w x c ρ
    show B'.core ((Strat.map m (H.strat w x c)).run ρ).2.2 = _
    rw [Strat.run_map]
    exact (hS.keeps _ _).trans (hG.keeps w x c ρ)
  · intro a ha
    refine Doomed.mono _ _ ?_ (hG.know a ha)
    intro τ hτ b w hb hw
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨xo, hxo, hf⟩ := Option.bind_eq_some_iff.1 h1
    have hb0 : R.red.out a τ = some (xo, R.imp a.2 τ) := red_out_eq_some.2 ⟨hxo, rfl⟩
    have hon := hG.onOut a τ _ ha hb0
    rw [show b = (b.1, g.map (R.imp a.2 τ)) from Prod.ext rfl h2] at hw
    rw [he a τ _ w hb0]
    exact hτ _ _ hb0 (hS.know xo (R.imp a.2 τ) b.1 w hon hf hw)

theorem exact_post : Spec.exact_post := fun _ _ _ _ _ _ _ _ _ _ _ _ _ f g m h => h.post f g m

theorem goodT_pure : Spec.goodT_pure := by
  intro K X X' E E' W W' A B f g m back hS
  refine ⟨⟨()⟩, ⟨fun x y y' τ τ' _ _ _ _ => rfl, fun y y' τ τ' q _ _ hE _ => hS.isLocal y y' q hE⟩,
    ?_, ?_, fun w x _ _ => hS.keeps x w, ?_, fun _ _ => le_refl _, ?_, ?_, ?_⟩
  · intro x y w c ρ hR _
    exact hS.acc x y w hR
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    rw [show b = (b.1, g.map a.2) from Prod.ext rfl h2]
    exact hS.onOut a.1 a.2 b.1 ha h1
  · exact prRho_empty _ fun _ h => h
  · intro k
    exact prRho_empty _ fun _ h => h
  · intro a ha b w hb hw
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    rw [show b = (b.1, g.map a.2) from Prod.ext rfl h2] at hw
    exact hS.know a.1 a.2 b.1 w ha h1 hw
  · refine ⟨fun _ _ T _ => PMF.pure (some ((IOR.pure f g).view T ())), fun x y w _ ρ _ T _ => ?_⟩
    rw [(Honest.pure f g m).output_of_not_mem T (fun h => h.elim id id)]
    exact PMF.map_const (unif Unit) (some ((IOR.pure f g).view T ()))

end Iop
