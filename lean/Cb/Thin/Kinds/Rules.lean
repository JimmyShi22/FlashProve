-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/Kinds/Rules.lean.
A KNOW-ONLY LEMMA FOR EACH KIND OF MOVE.
THE GENERIC PART: no protocol occurs here.
  D1 `IOR.GoodK₀ R A B ext ε`: the four fields point, isLocal, onOut, know of a reduction between
    two joints: no honest side among its arguments (`GoodB`, Ior/Masked.lean:88, less H, acc, keeps,
    prBad, cover, prCov). WITH ONE CONTROL: G1.
  D2 `IOR.StepK f g back A B`: `StepT` (Ior/KnowCollRulesFrame.lean:80) less m, acc, keeps: its
    other three fields to the letter.
  G1 goodK_iff; G3r know_post, G3o onOut_post (raw, in the form of Ior/KnowRules and the library's
    knowB_pre); G3 goodK₀_post;
  G4r know_pre, G4o onOut_pre, G4 goodK₀_pre; G5a goodK₀_cf (know_cf is CALLED), G5b goodK₀_cf_in;
    G6 goodK₀_pure (know_pure | onOut_pure are CALLED).
TWINS AT A LINK, NAMED: the four fields read no honest side, so the form without H is the root: G4 |
goodK_pre (Cb/Thin/K4/Door.lean [not in this library]); G5a | goodK_cf (Cb/Thin/K4/Lift.lean
[not in this library]): these have the same know and onOut (Cb/Thin/Kinds/Twins.lean
[not in this library]); both stand twice.
NO THIN DEFINITION OR PREMISE names a bundle, an honest side, a joint's exact relation or core. THE
CONTROLS AND GUARDS DO.
The proofs of G3r, G3o are the library's `goodB_post` (Ior/KnowCollRulesFrameProofs.lean:314-347),
those of G4r, G4o its `goodB_pre` (:272-309), two of nine components each: lines repeated.

-/
import Ior.KnowRulesProofs
import Cb.Thin.K3.GoodK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop
open Prob IOR

namespace IOR

/-- D1. The four, for a reduction between two joints. -/
structure GoodK₀ {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} (R : IOR Xi Ei Xo Eo)
    (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
    (ε : Err R.shape) : Prop where
  point   : Nonempty R.shape.IsPoint
  isLocal : R.IsLocal
  onOut   : ∀ a τ b, A.on a → R.red.out a τ = some b → B.on b
  know    : R.red.Know A.on A.relR B.relR ext ε

/-- D2. A step without rounds, its side of knowledge soundness. -/
structure StepK {K X X' : Type} {E E' : ExtSpec} {W W' : Type} (f : X → Option X')
    (g : ExtMap E E') (back : X × E.Str → W' → W) (A : Rels K X E W) (B : Rels K X' E' W') :
    Prop where
  isLocal : g.IsLocal
  onOut   : ∀ x y x', A.on (x, y) → f x = some x' → B.on (x', g.map y)
  know    : ∀ x y x' w',
    A.on (x, y) → f x = some x' → B.relR (x', g.map y) w' → A.relR (x, y) (back (x, y) w')

end IOR

/-- G1: THE ONE CONTROL: a link's GoodK is D1 at the link's parts. -/
theorem goodK_iff {K : Type} {A B : Joint K} (l : Link K A B) :
    l.GoodK ↔ IOR.GoodK₀ l.R A.rels B.rels l.ext l.P.err :=
  ⟨fun g => ⟨g.point, g.isLocal, g.onOut, g.know⟩, fun g => ⟨g.point, g.isLocal, g.onOut, g.know⟩⟩

/-- G3r: R, then a step without rounds: knowledge soundness. -/
theorem know_post {Xi Xo Xo' : Type} {Ei Eo Eo' : ExtSpec} {Wi Wo Wo' : Type}
    (R : IOR Xi Ei Xo Eo) (f : Xo → Option Xo') (g : ExtMap Eo Eo') (on : Xi × Ei.Str → Prop)
    (on₁ : Xo × Eo.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
    (RB' : Xo' × Eo'.Str → Wo' → Prop) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
    (ext' : Xi × Ei.Str → Tr R.shape → Wo' → Wi) (back : Xo × Eo.Str → Wo' → Wo) (ε : Err R.shape)
    (hK : R.red.Know on RA RB ext ε) (hO : ∀ a τ b, on a → R.red.out a τ = some b → on₁ b)
    (hB : ∀ x y x' w, on₁ (x, y) → f x = some x' → RB' (x', g.map y) w → RB (x, y) (back (x, y) w))
    (he : ∀ a τ b w, R.red.out a τ = some b → ext' a τ w = ext a τ (back b w)) :
    (R.post f g).red.Know on RA RB' ext' ε := by
  intro a ha
  refine Doomed.mono _ _ ?_ (hK a ha)
  intro τ hτ b w hb hw
  obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
  obtain ⟨xo, hxo, hf⟩ := Option.bind_eq_some_iff.1 h1
  have hb0 : R.red.out a τ = some (xo, R.imp a.2 τ) := red_out_eq_some.2 ⟨hxo, rfl⟩
  have hon := hO a τ _ ha hb0
  rw [show b = (b.1, g.map (R.imp a.2 τ)) from Prod.ext rfl h2] at hw
  rw [he a τ _ w hb0]
  exact hτ _ _ hb0 (hB xo (R.imp a.2 τ) b.1 w hon hf hw)

/-- G3o: R, then a step without rounds: the clause on outputs. -/
theorem onOut_post {Xi Xo Xo' : Type} {Ei Eo Eo' : ExtSpec} (R : IOR Xi Ei Xo Eo)
    (f : Xo → Option Xo') (g : ExtMap Eo Eo') (on : Xi × Ei.Str → Prop) (on₁ : Xo × Eo.Str → Prop)
    (on₂ : Xo' × Eo'.Str → Prop) (hO : ∀ a τ b, on a → R.red.out a τ = some b → on₁ b)
    (hS : ∀ x y x', on₁ (x, y) → f x = some x' → on₂ (x', g.map y)) :
    ∀ a τ b, on a → (R.post f g).red.out a τ = some b → on₂ b := by
  intro a τ b ha hb
  obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
  obtain ⟨xo, hxo, hf⟩ := Option.bind_eq_some_iff.1 h1
  have hon := hO a τ (xo, R.imp a.2 τ) ha (red_out_eq_some.2 ⟨hxo, rfl⟩)
  have := hS xo (R.imp a.2 τ) b.1 hon hf
  rw [show b = (b.1, g.map (R.imp a.2 τ)) from Prod.ext rfl h2]
  exact this

/-- G3: the four behind which a step without rounds comes: the four of `goodB_post`'s nine. -/
theorem goodK₀_post {K Xi Xo Xo' : Type} {Ei Eo Eo' : ExtSpec} {Wi Wo Wo' : Type}
    (R : IOR Xi Ei Xo Eo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (B' : Rels K Xo' Eo' Wo')
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ext' : Xi × Ei.Str → Tr R.shape → Wo' → Wi)
    (ε : Err R.shape) (f : Xo → Option Xo') (g : ExtMap Eo Eo') (back : Xo × Eo.Str → Wo' → Wo)
    (hG : IOR.GoodK₀ R A B ext ε) (hS : IOR.StepK f g back B B')
    (he : ∀ a τ b w, R.red.out a τ = some b → ext' a τ w = ext a τ (back b w)) :
    IOR.GoodK₀ (R.post f g) A B' ext' ε :=
  ⟨hG.point, hG.isLocal.post f g hS.isLocal,
    onOut_post R f g A.on B.on B'.on hG.onOut hS.onOut,
    know_post R f g A.on B.on A.relR B.relR B'.relR ext ext' back ε hG.know hG.onOut hS.know he⟩

/-- G4r: a step without rounds, then R: knowledge soundness. The premises are those of the library's
`knowB_pre` (Ior/KnowBRulesStep.lean:38),
for `Know`. -/
theorem know_pre {Xi Xi' Xo : Type} {Ei Ei' Eo : ExtSpec} {Wi Wi' Wo : Type} (R : IOR Xi Ei Xo Eo)
    (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) (on : Xi × Ei.Str → Prop)
    (on' : Xi' × Ei'.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RA' : Xi' × Ei'.Str → Wi' → Prop)
    (RB : Xo × Eo.Str → Wo → Prop) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
    (ext' : Xi' × Ei'.Str → Tr R.shape → Wo → Wi') (back : Xi' × Ei'.Str → Wi → Wi')
    (ε : Err R.shape) (hK : R.red.Know on RA RB ext ε)
    (hO : ∀ x y x₁, on' (x, y) → f x = some x₁ → on (x₁, g.map y))
    (hB : ∀ x y x₁ w, on' (x, y) → f x = some x₁ → RA (x₁, g.map y) w → RA' (x, y) (back (x, y) w))
    (he : ∀ a x₁ τ w, f a.1 = some x₁ → ext' a τ w = back a (ext (x₁, g.map a.2) τ w)) :
    (R.pre f g).red.Know on' RA' RB ext' ε := by
  intro a ha
  cases hf : f a.1 with
  | none =>
      refine Doomed.of_forall _ _ fun τ b w hb _ => ?_
      obtain ⟨h1, _⟩ := red_out_eq_some.1 hb
      obtain ⟨x₁, hx₁, _⟩ := Option.bind_eq_some_iff.1 h1
      rw [hf] at hx₁
      cases hx₁
  | some x₁ =>
      have hon := hO a.1 a.2 x₁ ha hf
      refine Doomed.mono _ _ ?_ (hK (x₁, g.map a.2) hon)
      intro τ hτ b w hb hw
      obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
      obtain ⟨x₁', hx₁', ho⟩ := Option.bind_eq_some_iff.1 h1
      rw [hf] at hx₁'
      cases hx₁'
      rw [he a x₁ τ w hf]
      exact hB a.1 a.2 x₁ _ ha hf (hτ b w (red_out_eq_some.2 ⟨ho, h2⟩) hw)

/-- G4o: a step without rounds, then R: the clause on outputs. -/
theorem onOut_pre {Xi Xi' Xo : Type} {Ei Ei' Eo : ExtSpec} (R : IOR Xi Ei Xo Eo)
    (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) (on : Xi × Ei.Str → Prop)
    (on' : Xi' × Ei'.Str → Prop) (on₂ : Xo × Eo.Str → Prop)
    (hG : ∀ a τ b, on a → R.red.out a τ = some b → on₂ b)
    (hO : ∀ x y x₁, on' (x, y) → f x = some x₁ → on (x₁, g.map y)) :
    ∀ a τ b, on' a → (R.pre f g).red.out a τ = some b → on₂ b := by
  intro a τ b ha hb
  obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
  obtain ⟨x₁, hx₁, ho⟩ := Option.bind_eq_some_iff.1 h1
  exact hG (x₁, g.map a.2) τ b (hO a.1 a.2 x₁ ha hx₁) (red_out_eq_some.2 ⟨ho, h2⟩)

/-- G4: the four behind a step without rounds: the four of `goodB_pre`'s nine. TWIN AT A LINK:
Cb/Thin/K4/Door.lean [not in this library] goodK_pre. -/
theorem goodK₀_pre {K Xi Xi' Xo : Type} {Ei Ei' Eo : ExtSpec} {Wi Wi' Wo : Type}
    (R : IOR Xi Ei Xo Eo) (A' : Rels K Xi' Ei' Wi') (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ext' : Xi' × Ei'.Str → Tr R.shape → Wo → Wi')
    (ε : Err R.shape) (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) (back : Xi' × Ei'.Str → Wi → Wi')
    (hS : IOR.StepK f g back A' A) (hG : IOR.GoodK₀ R A B ext ε)
    (he : ∀ a x₁ τ w, f a.1 = some x₁ → ext' a τ w = back a (ext (x₁, g.map a.2) τ w)) :
    IOR.GoodK₀ (R.pre f g) A' B ext' ε :=
  ⟨hG.point, hG.isLocal.pre f g hS.isLocal,
    onOut_pre R f g A.on A'.on B.on hG.onOut hS.onOut,
    know_pre R f g A.on A'.on A.relR A'.relR B.relR ext ext' back ε hG.know hS.onOut hS.know he⟩

/-- G5a: to joints whose condition may fail: the four of `goodB_cf`'s nine. TWIN AT A LINK:
Cb/Thin/K4/Lift.lean [not in this library] goodK_cf. -/
theorem goodK₀_cf {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} (R : IOR Xi Ei Xo Eo)
    (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
    (ε : Err R.shape) (g : IOR.GoodK₀ R A B ext ε) : IOR.GoodK₀ R A.cf B.cf ext ε :=
  ⟨g.point, g.isLocal, fun _ _ _ _ _ => trivial,
    know_cf K Xi Xo Ei Eo R Wi Wo A B ext ε g.know g.onOut⟩

/-- G5b: a block that is proved «on A's condition, into B.cf» enters a chain: the four of
`goodB_cf_in`'s first half. -/
theorem goodK₀_cf_in {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} (R : IOR Xi Ei Xo Eo)
    (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
    (ε : Err R.shape) (g : IOR.GoodK₀ R A B.cf ext ε) : IOR.GoodK₀ R A.cf B.cf ext ε :=
  ⟨g.point, g.isLocal, fun _ _ _ _ _ => trivial,
    (know_iff_orOff _ _ _ _ R.red A.on A.relR B.cf.relR ext ε).1 g.know⟩

/-- G6: a step without rounds, alone: the four of `goodT_pure`'s ten. -/
theorem goodK₀_pure {K X X' : Type} {E E' : ExtSpec} {W W' : Type} (A : Rels K X E W)
    (B : Rels K X' E' W') (f : X → Option X') (g : ExtMap E E') (back : X × E.Str → W' → W)
    (hS : IOR.StepK f g back A B) :
    IOR.GoodK₀ (IOR.pure f g) A B (fun a _ w => back a w) () :=
  ⟨⟨()⟩, ⟨fun _ _ _ _ _ _ _ _ _ => rfl, fun y y' _ _ q _ _ hE _ => hS.isLocal y y' q hE⟩,
    onOut_pure _ _ _ _ f g A.on B.on fun a x' ha hx => hS.onOut a.1 a.2 x' ha hx,
    know_pure _ _ _ _ f g _ _ A.on A.relR B.relR back () fun a x' w ha hx hw =>
      hS.know a.1 a.2 x' w ha hx hw⟩

/-! ## The controls: the library's forms give the thin ones, by projections alone -/

theorem goodK₀_of_goodB {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {H : R.Honest Wi Wo} {A : Rels K Xi Ei Wi} {B : Rels K Xo Eo Wo}
    {ext : Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : Nums K R} (g : IOR.GoodB R H A B ext P) :
    IOR.GoodK₀ R A B ext P.err :=
  ⟨g.point, g.isLocal, g.onOut, g.know⟩

theorem goodK₀_of_goodT {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {H : R.Honest Wi Wo} {A : Rels K Xi Ei Wi} {B : Rels K Xo Eo Wo}
    {ext : Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : Nums K R} (g : IOR.GoodT R H A B ext P) :
    IOR.GoodK₀ R A B ext P.err :=
  ⟨g.point, g.isLocal, g.onOut, g.know⟩

theorem stepK_of_stepT {K X X' : Type} {E E' : ExtSpec} {W W' : Type} {f : X → Option X'}
    {g : ExtMap E E'} {m : X × W → X' × W'} {back : X × E.Str → W' → W} {A : Rels K X E W}
    {B : Rels K X' E' W'} (h : IOR.StepT f g m back A B) : IOR.StepK f g back A B :=
  ⟨h.isLocal, h.onOut, h.know⟩

theorem stepK_of_step {K X X' : Type} {E E' : ExtSpec} {W W' : Type} {f : X → Option X'}
    {g : ExtMap E E'} {m : X × W → X' × W'} {back : E.Str → W' → W} {A : Rels K X E W}
    {B : Rels K X' E' W'} (h : IOR.Step f g m back A B) :
    IOR.StepK f g (fun a w => back a.2 w) A B :=
  ⟨h.isLocal, h.onOut, h.know⟩

/-! ## The rules' own guards: under the library's premises, ONE proposition (up to unfolding) -/

example (K Xi Xo Xo' : Type) (Ei Eo Eo' : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wo' : Type)
    (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (B' : Rels K Xo' Eo' Wo')
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ext' : Xi × Ei.Str → Tr R.shape → Wo' → Wi)
    (P : Nums K R) (f : Xo → Option Xo') (g : ExtMap Eo Eo') (m : Xo × Wo → Xo' × Wo')
    (back : Xo × Eo.Str → Wo' → Wo) (hG : IOR.GoodB R H A B ext P) (hS : IOR.StepT f g m back B B')
    (he : ∀ a τ b w, R.red.out a τ = some b → ext' a τ w = ext a τ (back b w)) :
    (goodB_post K Xi Xo Xo' Ei Eo Eo' R Wi Wo Wo' H A B B' ext ext' P f g m back hG hS he).know =
      (goodK₀_post R A B B' ext ext' P.err f g back (goodK₀_of_goodB hG) (stepK_of_stepT hS)
        he).know := rfl

example (K Xi Xo Xo' : Type) (Ei Eo Eo' : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wo' : Type)
    (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (B' : Rels K Xo' Eo' Wo')
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ext' : Xi × Ei.Str → Tr R.shape → Wo' → Wi)
    (P : Nums K R) (f : Xo → Option Xo') (g : ExtMap Eo Eo') (m : Xo × Wo → Xo' × Wo')
    (back : Xo × Eo.Str → Wo' → Wo) (hG : IOR.GoodB R H A B ext P) (hS : IOR.StepT f g m back B B')
    (he : ∀ a τ b w, R.red.out a τ = some b → ext' a τ w = ext a τ (back b w)) :
    (goodB_post K Xi Xo Xo' Ei Eo Eo' R Wi Wo Wo' H A B B' ext ext' P f g m back hG hS he).onOut =
      (goodK₀_post R A B B' ext ext' P.err f g back (goodK₀_of_goodB hG) (stepK_of_stepT hS)
        he).onOut := rfl

example (K X X' : Type) (E E' : ExtSpec) (W W' : Type) (A : Rels K X E W) (B : Rels K X' E' W')
    (f : X → Option X') (g : ExtMap E E') (m : X × W → X' × W') (back : X × E.Str → W' → W)
    (hS : IOR.StepT f g m back A B) :
    (goodT_pure K X X' E E' W W' A B f g m back hS).know =
      (goodK₀_pure A B f g back (stepK_of_stepT hS)).know := rfl

example (K X X' : Type) (E E' : ExtSpec) (W W' : Type) (A : Rels K X E W) (B : Rels K X' E' W')
    (f : X → Option X') (g : ExtMap E E') (m : X × W → X' × W') (back : X × E.Str → W' → W)
    (hS : IOR.StepT f g m back A B) :
    (goodT_pure K X X' E E' W W' A B f g m back hS).onOut =
      (goodK₀_pure A B f g back (stepK_of_stepT hS)).onOut := rfl

example (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
    (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R) (g : IOR.GoodB R H A B.cf ext P) :
    ((goodB_cf_in K Xi Xo Ei Eo R Wi Wo H A B ext P).1 g).know =
      (goodK₀_cf_in R A B ext P.err (goodK₀_of_goodB g)).know := rfl

example (K Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo : Type)
    (H : R.Honest Wi Wo) (A' : Rels K Xi' Ei' Wi') (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ext' : Xi' × Ei'.Str → Tr R.shape → Wo → Wi')
    (P : Nums K R) (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) (m : Xi' × Wi' → Xi × Wi)
    (back : Xi' × Ei'.Str → Wi → Wi') (hS : IOR.StepT f g m back A' A)
    (hG : IOR.GoodB R H A B ext P)
    (he : ∀ a x₁ τ w, f a.1 = some x₁ → ext' a τ w = back a (ext (x₁, g.map a.2) τ w)) :
    (goodB_pre K Xi Xi' Xo Ei Ei' Eo R Wi Wi' Wo H A' A B ext ext' P f g m back hS hG he).know =
      (goodK₀_pre R A' A B ext ext' P.err f g back (stepK_of_stepT hS) (goodK₀_of_goodB hG)
        he).know := rfl

example (K Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo : Type)
    (H : R.Honest Wi Wo) (A' : Rels K Xi' Ei' Wi') (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ext' : Xi' × Ei'.Str → Tr R.shape → Wo → Wi')
    (P : Nums K R) (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) (m : Xi' × Wi' → Xi × Wi)
    (back : Xi' × Ei'.Str → Wi → Wi') (hS : IOR.StepT f g m back A' A)
    (hG : IOR.GoodB R H A B ext P)
    (he : ∀ a x₁ τ w, f a.1 = some x₁ → ext' a τ w = back a (ext (x₁, g.map a.2) τ w)) :
    (goodB_pre K Xi Xi' Xo Ei Ei' Eo R Wi Wi' Wo H A' A B ext ext' P f g m back hS hG he).onOut =
      (goodK₀_pre R A' A B ext ext' P.err f g back (stepK_of_stepT hS) (goodK₀_of_goodB hG)
        he).onOut := rfl

example (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
    (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R) (g : IOR.GoodB R H A B ext P) :
    (goodB_cf K Xi Xo Ei Eo R Wi Wo H A B ext P g).know =
      (goodK₀_cf R A B ext P.err (goodK₀_of_goodB g)).know := rfl

example (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
    (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R) (g : IOR.GoodB R H A B ext P) :
    (goodB_cf K Xi Xo Ei Eo R Wi Wo H A B ext P g).onOut =
      (goodK₀_cf R A B ext P.err (goodK₀_of_goodB g)).onOut := rfl

end Iop

#print Iop.IOR.GoodK₀
#print Iop.IOR.StepK
#check @Iop.know_pre
#check @Iop.onOut_pre
#check @Iop.goodK₀_pre
#check @Iop.goodK₀_cf
#check @Iop.goodK_iff
#check @Iop.know_post
#check @Iop.onOut_post
#check @Iop.goodK₀_post
#check @Iop.goodK₀_cf_in
#check @Iop.goodK₀_pure
