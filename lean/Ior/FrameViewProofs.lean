-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/FrameViewProofs.lean: proof of `Spec.good_reimp` (Ior/FrameView.lean): the rounds of R with
another new implicit instance.

R is an interactive oracle reduction (`IOR`, Ior/Ior.lean). A statement has an explicit part, which
the verifier holds, and an implicit part, the implicit instance: oracles, which it reads by queries.
`R.reimp f imp' srcE' srcO'`: its verifier outputs f xo where R's outputs xo; imp' is its new
implicit instance (in place of `R.imp`); srcE', srcO' say from which symbols a symbol of it is
computed. The honest prover sends what R's sends and ends with (f xo, g w xo wo).
`H.ExactWith Ri bud S`: for every (x, y, w) in Ri, every ρ outside `H.Hid w x` and every T with
`bud ρ T`, the distribution `H.output w x ρ T` equals `S x ρ T a`, where a gives the symbols of y at
the positions `R.given ρ T` and `none` at the others. `Exact` says that some S does. In
`Honest.Exact.reimp` it is the premise, of H, and the conclusion, of `H.reimp f imp' srcE' srcO' g`.
`Spec.good_reimp`: if R leads from A to B, then `R.reimp` leads from A to B', with the errors of R
plus those of a second game on the same rounds, under the hypotheses (1) to (5) of the head of
Ior/FrameView.lean. In the proof hG is `Good R H A B ext P`; hloc, hfwd, hgame, hback are (1) to
(4), in that order; (5) is the last two, hon and hcore.
Knowledge soundness: the prover has lost both games at once, with the errors added (`Doomed.and`);
at a transcript that is bad for it in both, hypothesis (4) gives the extraction.
Honest-verifier zero knowledge (`Honest.Exact.reimp`): a view of the new IOR is a view of R under
another type, and the output of the new honest side is that of the old one, carried over; the
simulator is the old one. The rest is read off the hypotheses.

Notation (binders of `Spec.good_reimp`, Ior/FrameView.lean):
`ext : Ei.Str → Orcs R.shape → Wo → Wi`, `ext' : Ei.Str → Orcs R.shape → Wo' → Wi`: the extractors
in `Good` (Ior/Chain.lean). `ε' : Err R.shape`: a list of errors (`Err`, Iop/Rbr.lean); it stands in
hypothesis (3). `Q : Xi × Ei.Str → Tr R.shape → Prop`: a predicate on a statement and a full
transcript (`Tr`, Iop/Shape.lean); it stands in hypotheses (3) and (4).

Limits: see Limits in the head of Ior/FrameView.lean.
Terms: lean/GLOSSARY.md.
-/
import Ior.FrameView
import Ior.FrameProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K Xi Xo Xo' : Type} {Ei Eo Eo' : ExtSpec} {Wi Wo Wo' : Type}

section
variable {R : IOR Xi Ei Xo Eo} (f : Xo → Xo') (imp' : Ei.Str → Tr R.shape → Eo'.Str)
  (srcE' : Rho R.shape → Eo'.Pos → Finset Ei.Pos)
  (srcO' : Rho R.shape → Eo'.Pos → Finset (OPos R.shape))

/-- A view of R as a view of `R.reimp`. -/
def View.reimp (v : View R) : View (R.reimp f imp' srcE' srcO') := ⟨v.plains, v.orc⟩

theorem Honest.output_reimp (H : R.Honest Wi Wo) (g : Wi → Xo → Wo → Wo') (w : Wi) (x : Xi)
    (ρ : Rho R.shape) (T : Finset (OPos R.shape)) :
    (H.reimp f imp' srcE' srcO' g).output w x ρ T =
      (H.output w x ρ T).map (Option.map (View.reimp f imp' srcE' srcO')) := by
  by_cases h : ρ ∈ H.withheld w x
  · rw [H.output_of_mem T h, PMF.pure_map]
    exact (H.reimp f imp' srcE' srcO' g).output_of_mem T h
  · rw [H.output_of_not_mem T h, PMF.map_comp]
    refine ((H.reimp f imp' srcE' srcO' g).output_of_not_mem T h).trans ?_
    refine congrArg (fun k => PMF.map k (unif H.Coin)) (funext fun c => ?_)
    show some ((R.reimp f imp' srcE' srcO').view
          T ((Strat.map (fun o => (f o.1, g w o.1 o.2)) (H.strat w x c)).run ρ).1) =
      some (View.reimp f imp' srcE' srcO' (R.view T ((H.strat w x c).run ρ).1))
    rw [Strat.run_map]
    rfl

theorem Honest.Exact.reimp {H : R.Honest Wi Wo} {Ri : Xi → Ei.Str → Wi → Prop}
    {bud : Rho R.shape → Finset (OPos R.shape) → Prop} (h : H.Exact Ri bud)
    (g : Wi → Xo → Wo → Wo') :
    (H.reimp f imp' srcE' srcO' g).Exact Ri bud := by
  obtain ⟨S, hS⟩ := h
  refine ⟨fun x ρ T a => (S x ρ T a).map (Option.map (View.reimp f imp' srcE' srcO')),
    fun x y w hR ρ hρ T hT => ?_⟩
  rw [Honest.output_reimp]
  exact congrArg _ (hS x y w hR ρ hρ T hT)

end
end IOR

open IOR

theorem good_reimp : Spec.good_reimp := by
  intro K Xi Xo Xo' Ei Eo Eo' R Wi Wo Wo' H A B B' ext ext' P ε' Q f imp' srcE' srcO' g hG hloc
    hfwd hgame hback hon hcore
  refine ⟨hG.point,
    ⟨fun x y y' τ τ' hρ hπ hE hO =>
        congrArg (Option.map f) (hG.isLocal.out x y y' τ τ' hρ hπ hE hO),
      hloc⟩,
    ?_, ?_, ?_, hG.prBad, hG.cover, hG.prCov, ?_, hG.exact.reimp f imp' srcE' srcO' g⟩
  · intro x y w c ρ hR hρ
    obtain ⟨ho, hb⟩ := hG.acc x y w c ρ hR hρ
    have h2 := hfwd x y w c ρ hR hρ hb
    show (R.out x y ((Strat.map (fun o => (f o.1, g w o.1 o.2)) (H.strat w x c)).run ρ).1).map f =
        some ((Strat.map (fun o => (f o.1, g w o.1 o.2)) (H.strat w x c)).run ρ).2.1 ∧
      B'.rel ((Strat.map (fun o => (f o.1, g w o.1 o.2)) (H.strat w x c)).run ρ).2.1
        (imp' y ((Strat.map (fun o => (f o.1, g w o.1 o.2)) (H.strat w x c)).run ρ).1)
        ((Strat.map (fun o => (f o.1, g w o.1 o.2)) (H.strat w x c)).run ρ).2.2
    rw [Strat.run_map]
    exact ⟨by rw [ho]; rfl, h2⟩
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨xo, hxo, hf⟩ := Option.map_eq_some_iff.1 h1
    rw [show b = (f xo, imp' a.2 τ) from Prod.ext hf.symm h2]
    exact hon a τ xo ha hxo
  · intro w x c ρ
    show B'.core ((Strat.map (fun o => (f o.1, g w o.1 o.2)) (H.strat w x c)).run ρ).2.2 = _
    rw [Strat.run_map]
    exact hcore w x c ρ
  · intro a ha
    refine Doomed.mono _ _ ?_ (Doomed.and _ (hG.know a ha) (hgame a ha))
    intro τ hτ b w' hb hw'
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨xo, hxo, hf⟩ := Option.map_eq_some_iff.1 h1
    rw [show b = (f xo, imp' a.2 τ) from Prod.ext hf.symm h2] at hw'
    exact hback a τ xo w' ha hτ.2 hxo hw' fun w hw =>
      hτ.1 (xo, R.imp a.2 τ) w (red_out_eq_some.2 ⟨hxo, rfl⟩) hw

end Iop
