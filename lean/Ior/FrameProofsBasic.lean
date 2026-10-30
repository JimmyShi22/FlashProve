-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/FrameProofsBasic.lean: proofs of ten of the statements of Ior/Frame.lean (interactive oracle
reductions, IORs, that act on a part of a larger statement, and the frame rule), each proved as it
is stated there.
`Good` (Ior/Chain.lean): see the head of Ior/Frame.lean. In `good_and`, `good_carry`, `good_frame`,
`good_recore` and `good_keepX` `Good` is a premise and the conclusion. `Doomed` (Iop/Rbr.lean): "the
prover has lost" towards a goal: see the head of Ior/Know.lean.

Main names (statements and hypotheses: Ior/Frame.lean):
  `extMap_isLocal`: the standard maps on implicit instances.
  `know_frame`: the frame rule for reductions.
  `know_of_soundW`: from soundness to knowledge soundness with a further part of the witness.
  `good_and`: the frame rule, no type changes.
  `good_carry`: a further part of the witness.
  `good_frame`: the two together.
  `good_recore`: another core and another cover.
  `keep_copies`: the facts with which transports over `keepX` and `keepE` are proved.
  `good_keepX`: a further explicit part that is only copied.
  `impBy_frame`: `ImpBy` (Ior/Chain.lean) for the constructions.
  Helpers (stated here): what a run of the honest prover of "carry" and of "keepX" is, and what it
    shows (`IOR.Honest.carry_run`, `keepX_run`, `carry_output`, `keepX_output`).

Notation:
  In `good_and`: `S : Xi → Ei.Str → Wi → Prop`, `SR : Xi × Ei.Str → Wi → Prop`,
    `T : Xi × Ei.Str → Prop`: in `Rels.and` (Ior/Frame.lean): "S beside the honest relation, SR
    beside the relaxation, T beside the condition on statements".
  The fields of `Good R H A B ext P` (Ior/Chain.lean), in Lean's text:
    `point : Nonempty R.shape.IsPoint`
    `isLocal : R.IsLocal`
    `acc : H.Acc A.rel B.rel`
    `onOut : ∀ a τ b, A.on a → R.red.out a τ = some b → B.on b`
    `keeps : ∀ w x c ρ, B.core ((H.strat w x c).run ρ).2.2 = A.core w`
    `prBad : prRho H.Bad ≤ P.pBad`
    `cover : ∀ w x, H.Hid w x ⊆ P.cov (A.core w)`
    `prCov : ∀ k, prRho (P.cov k) ≤ P.pHid`
    `know : R.red.Know A.on A.relR B.relR (fun a τ w => ext a.2 τ.read w) P.err`
    `exact : H.Exact A.rel P.bud`

Limits: the rules are conditional: they give no IOR that is `Good` (Ior/Chain.lean). The other
statements of Ior/Frame.lean (copied oracles, steps without rounds) are proved in
Ior/FrameProofs.lean. See also Limits in the head of Ior/Frame.lean.
Terms: lean/GLOSSARY.md.
-/
import Ior.Frame
import Ior.ExactSeq

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} {Wi Wo : Type}

namespace Honest

theorem carry_run (H : R.Honest Wi Wo) (Wz : Type) (w : Wi × Wz) (x : Xi)
    (c : H.Coin) (ρ : Rho R.shape) :
    ((H.carry Wz).strat w x c).run ρ =
      (((H.strat w.1 x c).run ρ).1,
        (((H.strat w.1 x c).run ρ).2.1, (((H.strat w.1 x c).run ρ).2.2, w.2))) :=
  Strat.run_map _ _ _

theorem keepX_run (H : R.Honest Wi Wo) (Z : Type) (w : Wi) (a : Xi × Z)
    (c : H.Coin) (ρ : Rho R.shape) :
    ((H.keepX Z).strat w a c).run ρ =
      (((H.strat w a.1 c).run ρ).1,
        ((((H.strat w a.1 c).run ρ).2.1, a.2), ((H.strat w a.1 c).run ρ).2.2)) :=
  Strat.run_map _ _ _

/-- With a further part of the witness the run shows the same. -/
theorem carry_output (H : R.Honest Wi Wo) (Wz : Type) (w : Wi × Wz) (x : Xi)
    (ρ : Rho R.shape) (T : Finset (OPos R.shape)) :
    (H.carry Wz).output w x ρ T = H.output w.1 x ρ T := by
  by_cases h : ρ ∈ H.withheld w.1 x
  · rw [H.output_of_mem T h]
    exact (H.carry Wz).output_of_mem T h
  · rw [H.output_of_not_mem T h]
    refine ((H.carry Wz).output_of_not_mem T h).trans ?_
    refine congrArg (fun f => PMF.map f (unif H.Coin)) (funext fun c => ?_)
    rw [carry_run]

end Honest

/-- What a run of R shows, read as what a run of R.keepX Z shows: the same fields. -/
def viewKeepX (R : IOR Xi Ei Xo Eo) (Z : Type) (v : View R) : View (R.keepX Z) := ⟨v.plains, v.orc⟩

theorem view_keepX (R : IOR Xi Ei Xo Eo) (Z : Type) (T : Finset (OPos R.shape)) (τ : Tr R.shape) :
    (R.keepX Z).view T τ = viewKeepX R Z (R.view T τ) := rfl

/-- With a further explicit part the run shows the same. -/
theorem Honest.keepX_output (H : R.Honest Wi Wo) (Z : Type) (w : Wi) (a : Xi × Z)
    (ρ : Rho R.shape) (T : Finset (OPos R.shape)) :
    (H.keepX Z).output w a ρ T = (H.output w a.1 ρ T).map (Option.map (viewKeepX R Z)) := by
  by_cases h : ρ ∈ H.withheld w a.1
  · rw [H.output_of_mem T h, PMF.pure_map]
    exact (H.keepX Z).output_of_mem T h
  · rw [H.output_of_not_mem T h, PMF.map_comp]
    refine ((H.keepX Z).output_of_not_mem T h).trans ?_
    refine congrArg (fun f => PMF.map f (unif H.Coin)) (funext fun c => ?_)
    rw [keepX_run]
    rfl

theorem keepX_red_out (R : IOR Xi Ei Xo Eo) (Z : Type) (a : (Xi × Z) × Ei.Str) (τ : Tr R.shape)
    (b : (Xo × Z) × Eo.Str) (hb : (R.keepX Z).red.out a τ = some b) :
    b.1.2 = a.1.2 ∧ R.red.out (a.1.1, a.2) τ = some (b.1.1, b.2) := by
  obtain ⟨xz, hxz, rfl⟩ := Option.map_eq_some_iff.1 hb
  obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hxz
  refine ⟨rfl, ?_⟩
  show (R.out a.1.1 a.2 τ).map _ = _
  rw [hxo]
  rfl

theorem keepE_red_out (R : IOR Xi Ei Xo Eo) (F : ExtSpec) (a : Xi × (Ei.prod F).Str)
    (τ : Tr R.shape) (b : Xo × (Eo.prod F).Str) (hb : (R.keepE F).red.out a τ = some b) :
    b.2.2 = a.2.2 ∧ R.red.out (a.1, a.2.1) τ = some (b.1, b.2.1) := by
  obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hb
  have hxo' : R.out a.1 a.2.1 τ = some xo := hxo
  refine ⟨rfl, ?_⟩
  show (R.out a.1 a.2.1 τ).map _ = _
  rw [hxo']
  rfl

end IOR

open IOR

theorem extMap_isLocal : Spec.extMap_isLocal := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro E y y' q h
    exact h q (Finset.mem_singleton_self q)
  · intro E₁ E₂
    exact ⟨fun y y' q h => Sum.inl.inj (h (Sum.inl q) (Finset.mem_singleton_self _)),
      fun y y' q h => Sum.inr.inj (h (Sum.inr q) (Finset.mem_singleton_self _))⟩
  · intro E y y' q _
    rfl
  · intro E E' E'' g' g h' h y y' q hq
    classical
    refine h' _ _ q fun p hp => h _ _ p fun r hr => hq r ?_
    exact Finset.mem_biUnion.2 ⟨p, hp, hr⟩
  · intro E E₁ E₂ g₁ g₂ h₁ h₂ y y' q hq
    cases q with
    | inl q => exact congrArg Sum.inl (h₁ y y' q hq)
    | inr q => exact congrArg Sum.inr (h₂ y y' q hq)

theorem know_frame : Spec.know_frame := by
  intro A B WA WB Wz K on RA RB ext ε Φ Φ' upd hK hΦ a ha
  refine Doomed.mono _ _ ?_ (hK a ha)
  intro τ hτ b w hb hw
  exact ⟨hτ b w.1 hb hw.1, hΦ a τ b w.1 w.2 ha hb hw.1 (hτ b w.1 hb hw.1) hw.2⟩

theorem know_of_soundW : Spec.know_of_soundW := by
  intro A B WA WB WP K on RA RB LA LB d ε hK hA hB a ha
  refine Doomed.mono _ _ ?_ (hK a ha)
  intro τ hτ b w hb hw
  exact hA a w.2 ha (hτ b w.2 hb (hB b w hw))

theorem good_and : Spec.good_and := by
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
            ⟨hτ b w hb hw.1, hSR a τ b w ha.1 ha.2 hb hw.1 (hτ b w hb hw.1) hw.2⟩) (g.know a ha.1)
      exact := g.exact.elim fun Sm hSm => ⟨Sm, fun x y w hw ρ hρ U hU => hSm x y w hw.1 ρ hρ U hU⟩ }

theorem good_carry : Spec.good_carry := by
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
      know := fun a ha => Doomed.mono _ _ (fun τ hτ b w hb hw => hτ b w.1 hb hw) (g.know a ha)
      exact := g.exact.elim fun Sm hSm =>
        ⟨Sm, fun x y w hw ρ hρ U hU =>
            (H.carry_output Wz w x ρ U).trans (hSm x y w.1 hw ρ hρ U hU)⟩ }

theorem good_frame : Spec.good_frame := by
  intro K Xi Xo Ei Eo R Wi Wo Wz H A B ext P upd S SR T S' SR' T' g hS hSR hT
  refine good_and (K × Wz) Xi Xo Ei Eo R (Wi × Wz) (Wo × Wz) (H.carry Wz) (A.lift Wz) (B.lift Wz)
    (fun y o w => (ext y o w.1, upd y o w.1 w.2)) (P.carry Wz) (fun x y w => S x y w.1 w.2)
    (fun a w => SR a w.1 w.2) T (fun x y w => S' x y w.1 w.2) (fun b w => SR' b w.1 w.2) T'
    (good_carry K Xi Xo Ei Eo R Wi Wo Wz H A B ext P upd g) ?_ ?_ hT
  · intro x y w c ρ hR hs hρ hB
    rw [Honest.carry_run] at hB ⊢
    exact hS x y w.1 w.2 c ρ hR hs hρ hB
  · intro a τ b w ha ht hb hB hA hs
    exact hSR a τ b w.1 w.2 ha ht hb hB hA hs

theorem good_recore : Spec.good_recore := by
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
      know := g.know
      exact := g.exact }

theorem keep_copies : Spec.keep_copies := by
  intro Xi Xo Ei Eo R
  exact ⟨fun Z a τ b hb => keepX_red_out R Z a τ b hb,
    fun F a τ b hb => keepE_red_out R F a τ b hb,
    fun Z Wi Wo H w a c ρ => H.keepX_run Z w a c ρ,
    fun Wi Wo Wz H w x c ρ => H.carry_run Wz w x c ρ⟩

theorem good_keepX : Spec.good_keepX := by
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
          (g.know (a.1.1, a.2) ha)
      exact := g.exact.elim fun Sm hSm => ⟨fun a ρ U ans => (Sm a.1 ρ U ans).map (Option.map (viewKeepX R Z)), fun a y w hw ρ hρ U hU => by
        rw [Honest.keepX_output, hSm a.1 y w hw ρ hρ U hU]
        rfl⟩ }

theorem impBy_frame : Spec.impBy_frame := by
  intro Xi Xo Ei Eo R io h
  exact ⟨fun Z y τ => h y τ,
    fun F y τ => congrArg (fun u => (u, y.2)) (h y.1 τ),
    fun Xi' Ei' f g y τ => h (g.map y) τ,
    fun Xo' Eo' f g y τ => congrArg g.map (h y τ)⟩

end Iop
