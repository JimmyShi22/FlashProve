-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSigLiftProofs.lean: the proofs of the statements of Cb/Ld/LdSigLift.lean (from a reduction
on claims about messages to a reduction on statements about oracle messages).

The order. Tools: what `R.keep` outputs; the run of a re-typed honest side (`mapW`) and what it
shows; the run of the honest side over a signature. Then knowledge soundness, the bundle, zero
knowledge, the two together, and the case of a block that is knowledge sound outright.
Nothing is defined here that a statement reads.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigLift
import Cb.Ld.LdSigProofs
import Ior.FrameProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

section Tools
variable {Xi Xo Z : Type} {Ei Eo F : ExtSpec}

theorem keep_red_out (R : IOR Xi Ei Xo Eo) (Z : Type) (F : ExtSpec) (a : (Xi × Z) × (Ei.prod F).Str)
    (τ : Tr R.shape) (b : (Xo × Z) × (Eo.prod F).Str) (hb : (R.keep Z F).red.out a τ = some b) :
    b.1.2 = a.1.2 ∧ b.2.2 = a.2.2 ∧ R.red.out (a.1.1, a.2.1) τ = some (b.1.1, b.2.1) := by
  have h1 := keepE_red_out (R.keepX Z) F a τ b hb
  have h2 := keepX_red_out R Z (a.1, a.2.1) τ (b.1, b.2.1) h1.2
  exact ⟨h2.1, h1.1, h2.2⟩

theorem isLocal_keepX {R : IOR Xi Ei Xo Eo} (h : R.IsLocal) (Z : Type) : (R.keepX Z).IsLocal where
  out := by
    intro a y y' τ τ' hρ hπ hE hO
    show (R.out a.1 y τ).map _ = (R.out a.1 y' τ').map _
    rw [h.out a.1 y y' τ τ' hρ hπ hE hO]
  imp := h.imp

theorem exact_keepX' {R : IOR Xi Ei Xo Eo} {Wi Wo : Type} {H : R.Honest Wi Wo}
    {Ri : Xi → Ei.Str → Wi → Prop} {bud : Rho R.shape → Finset (OPos R.shape) → Prop}
    (h : H.Exact Ri bud) (Z : Type) :
    (H.keepX Z).Exact (fun a y w => Ri a.1 y w) bud :=
  h.elim fun Sm hSm => ⟨fun a ρ U ans => (Sm a.1 ρ U ans).map (Option.map (viewKeepX R Z)), fun a y w hw ρ hρ U hU => by
    rw [Honest.keepX_output, hSm a.1 y w hw ρ hρ U hU]
    rfl⟩

theorem mapW_run {R : IOR Xi Ei Xo Eo} {Wi Wi' Wo Wo' : Type} (H : R.Honest Wi Wo) (fi : Wi' → Wi)
    (fo : Wi' → Wo → Wo') (w : Wi') (x : Xi) (c : H.Coin) (ρ : Rho R.shape) :
    ((H.mapW fi fo).strat w x c).run ρ =
      (((H.strat (fi w) x c).run ρ).1,
        (((H.strat (fi w) x c).run ρ).2.1, fo w ((H.strat (fi w) x c).run ρ).2.2)) :=
  Strat.run_map _ _ _

theorem mapW_output {R : IOR Xi Ei Xo Eo} {Wi Wi' Wo Wo' : Type}
    (H : R.Honest Wi Wo) (fi : Wi' → Wi) (fo : Wi' → Wo → Wo') (w : Wi') (x : Xi)
    (ρ : Rho R.shape) (T : Finset (OPos R.shape)) :
    (H.mapW fi fo).output w x ρ T = H.output (fi w) x ρ T := by
  by_cases h : ρ ∈ H.withheld (fi w) x
  · rw [H.output_of_mem T h]
    exact (H.mapW fi fo).output_of_mem T h
  · rw [H.output_of_not_mem T h]
    refine ((H.mapW fi fo).output_of_not_mem T h).trans ?_
    refine congrArg (fun f => PMF.map f (unif H.Coin)) (funext fun c => ?_)
    rw [mapW_run]

end Tools

section
variable {E : Type} (S : Sig E) {St St' Wp Wp' : Type} {E₀ E₀' : ExtSpec} {R : IOR St E₀ St' E₀'}

theorem Sig.liftH_run (H : R.Honest (S.Msg × Wp) (S.Msg × Wp')) (w : S.Wit × Wp) (x : St × S.Smp)
    (c : H.Coin) (ρ : Rho R.shape) :
    ((S.liftH H).strat w x c).run ρ =
      (((H.strat (S.msgs w.1, w.2) x.1 c).run ρ).1,
        ((((H.strat (S.msgs w.1, w.2) x.1 c).run ρ).2.1, x.2),
          (w.1, ((H.strat (S.msgs w.1, w.2) x.1 c).run ρ).2.2.2))) := by
  refine (mapW_run (H.keep S.Smp S.ext) _ _ w x c ρ).trans ?_
  have h : (((H.keep S.Smp S.ext).strat (S.msgs w.1, w.2) x c).run ρ) = _ :=
    Honest.keepX_run H S.Smp (S.msgs w.1, w.2) x c ρ
  rw [h]
  rfl

end

section
variable (E : Type) [Field E]

theorem sigLift_know : Spec.sigLift_know E := by
  intro S Kc St St' Wp Wp' E₀ E₀' R A B ext ε h a ha
  by_cases hdec : ∃ m : S.Msg, ∀ i, S.decs a.1.2 a.2.2 i = some (m i)
  · obtain ⟨m, hm⟩ := hdec
    refine Doomed.mono _ _ ?_ (h m (a.1.1, a.2.1) ha.2)
    intro τ hτ b w hb hw
    obtain ⟨h1, h2, h3⟩ := keep_red_out R S.Smp S.ext a τ b hb
    have hw1 : ∀ i, S.decs a.1.2 a.2.2 i = some (w.1 i).1 := by
      rw [← h1, ← h2]
      exact hw.1
    have hmw : S.msgs w.1 = m := funext fun i => Option.some.inj ((hw1 i).symm.trans (hm i))
    have hw2 : B.relR (b.1.1, b.2.1) (S.msgs w.1, w.2) := hw.2
    refine ⟨hw1, ?_⟩
    show A.relR (a.1.1, a.2.1) (S.msgs w.1, ext (S.msgs w.1) (a.1.1, a.2.1) τ w.2)
    rw [hmw] at hw2 ⊢
    exact hτ (b.1.1, b.2.1) w.2 h3 hw2
  · refine Doomed.of_forall _ _ fun τ b w hb hw => ?_
    obtain ⟨h1, h2, _⟩ := keep_red_out R S.Smp S.ext a τ b hb
    refine absurd ⟨S.msgs w.1, ?_⟩ hdec
    rw [← h1, ← h2]
    exact hw.1

theorem sigLift_goodB : Spec.sigLift_goodB E := by
  intro S Kc St St' Wp Wp' E₀ E₀' R H A B ext P g
  have hs : ∀ (w : S.Wit × Wp) (x : St × S.Smp) c ρ,
      (S.msgs w.1, ((H.strat (S.msgs w.1, w.2) x.1 c).run ρ).2.2.2) =
        ((H.strat (S.msgs w.1, w.2) x.1 c).run ρ).2.2 :=
    fun w x c ρ => Prod.ext (g.same (S.msgs w.1, w.2) x.1 c ρ).symm rfl
  exact
    { point := g.point
      isLocal := IsLocal.keepE S.ext (isLocal_keepX g.isLocal S.Smp)
      acc := by
        intro x y w c ρ hR hρ
        have h := g.acc x.1 y.1 (S.msgs w.1, w.2) c ρ hR.2.2 hρ
        rw [S.liftH_run]
        refine ⟨?_, hR.1, hR.2.1, ?_⟩
        · show (R.out x.1 y.1 _).map _ = _
          rw [h.1]
          rfl
        · show B.rel _ _ (S.msgs w.1, ((H.strat (S.msgs w.1, w.2) x.1 c).run ρ).2.2.2)
          rw [hs]
          exact h.2
      onOut := by
        intro a τ b ha hb
        obtain ⟨h1, h2, h3⟩ := keep_red_out R S.Smp S.ext a τ b hb
        refine ⟨?_, g.onOut _ τ _ ha.2 h3⟩
        rw [h1, h2]
        exact ha.1
      keeps := by
        intro w x c ρ
        rw [S.liftH_run]
        show B.core (S.msgs w.1, ((H.strat (S.msgs w.1, w.2) x.1 c).run ρ).2.2.2) = _
        rw [hs]
        exact g.keeps (S.msgs w.1, w.2) x.1 c ρ
      prBad := g.prBad
      cover := fun w x => g.cover (S.msgs w.1, w.2) x.1
      prCov := g.prCov
      know := sigLift_know E S Kc St St' Wp Wp' E₀ E₀' R A B ext P.err g.know }

theorem sigLift_exact : Spec.sigLift_exact E := by
  intro S Kc St St' Wp Wp' E₀ E₀' R H A bud h
  obtain ⟨Sm, hSm⟩ := Honest.Exact.keepE S.ext (exact_keepX' h S.Smp)
  refine ⟨Sm, fun x y w hw ρ hρ T hT => ?_⟩
  refine (mapW_output (H.keep S.Smp S.ext) _ _ w x ρ T).trans ?_
  exact hSm x y (S.msgs w.1, w.2) hw.2.2 ρ hρ T hT

theorem sigLift_goodT : Spec.sigLift_goodT E := by
  intro S Kc St St' Wp Wp' E₀ E₀' R H A B ext P g hx
  have b := sigLift_goodB E S Kc St St' Wp Wp' E₀ E₀' R H A B ext P g
  exact ⟨b.point, b.isLocal, b.acc, b.onOut, b.keeps, b.prBad, b.cover, b.prCov, b.know,
    sigLift_exact E S Kc St St' Wp Wp' E₀ E₀' R H A P.bud hx⟩

end

theorem goodAt_of_goodB : Spec.goodAt_of_goodB := by
  intro K M Xi Xo Ei Eo Wi Wo R H A B ext P g hs
  exact ⟨g.point, g.isLocal, g.acc, g.onOut, g.keeps, g.prBad, g.cover, g.prCov, hs, fun m a ha =>
    Doomed.mono _ _ (fun τ hτ b wp hb hw => hτ b (m, wp) hb hw) (g.know a ha)⟩

end Cb
