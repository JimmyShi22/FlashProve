-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSigStep.lean: a rule for composing reductions: under `StepAt`, a step in which no message is
sent, before or after a reduction with the bundle `GoodAt`, gives a reduction with `GoodAt` again,
for an extractor composed of theirs.

Definitions, statements and proofs. No protocol occurs here.

Why: a chain of blocks on claims about messages is built between base joints (joints in which the
tuple of messages is a part of the witness, Cb/Ld/LdSig.lean), in the bundle `GoodAt` of
Cb/Ld/LdSigLift.lean (knowledge sound for each fixed tuple of messages), and lifted once. Between
two blocks the explicit part must sometimes be rewritten though no verifier message stands between
them: the row on a value that one sumcheck outputs is the input claim of the next, but its explicit
part has another form.
Ior/KnowCollRulesFrame.lean has the rules for steps without rounds before and after a block with the
bundle `GoodB` (`StepT`, `goodB_pre`, `goodB_post`). Here they are for `GoodAt`. No round is added:
`R.pre`, `R.post` of Ior/Frame.lean have the shape of R.

Main names:
  `StepAt f g m back A B`: f, g: what the verifier does to explicit part and oracles; m: what the
    honest prover does to (explicit part, witness), keeping the tuple; back u: the extractor on the
    further witness, at the tuple u.
  `Spec.goodAt_post`: a block, then a step; `Spec.goodAt_pre`: a step, then a block. From `GoodAt`
    of the block and `StepAt` of the step: `GoodAt` of the whole, for an extractor composed of
    theirs. Same shape, same numbers.
  `Spec.stepAt_map`: the usual case: a map φ on the explicit part; oracles and witness stay.
    Assumed: the relation goes forward, the condition goes forward, the cores agree, the relaxed
    relation goes back (on the statements with the condition).
  `Spec.goodAt_postMap`, `Spec.goodAt_preMap`: the two rules in that case; the extractor stays
    (before a block it is read at the new explicit part).

Limits: this file says nothing on zero knowledge or on the item "masked messages". For those:
Ior/KnowCollRulesFrame.lean: exact_pre, exact_post; Ior/MaskedFrame.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigLift
import Ior.KnowCollRulesFrameProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-- A step without rounds leads from A to B, for each fixed tuple. -/
structure StepAt {K M X X' : Type} {E E' : ExtSpec} {W W' : Type} (f : X → Option X')
    (g : ExtMap E E') (m : X × (M × W) → X' × (M × W')) (back : M → X × E.Str → W' → W)
    (A : Rels K X E (M × W)) (B : Rels K X' E' (M × W')) : Prop where
  isLocal : g.IsLocal
  acc     : ∀ x y w,
    A.rel x y w → f x = some (m (x, w)).1 ∧ B.rel (m (x, w)).1 (g.map y) (m (x, w)).2
  onOut   : ∀ x y x', A.on (x, y) → f x = some x' → B.on (x', g.map y)
  keeps   : ∀ x w, B.core (m (x, w)).2 = A.core w
  same    : ∀ x w, (m (x, w)).2.1 = w.1
  know    : ∀ u x y x' w',
    A.on (x, y) → f x = some x' → B.relR (x', g.map y) (u, w') → A.relR (x, y) (u, back u (x, y) w')

namespace Spec

def goodAt_post : Prop :=
  ∀ (K M Xi Xo Xo' : Type) (Ei Eo Eo' : ExtSpec) (Wi Wo Wo' : Type) (R : IOR Xi Ei Xo Eo)
      (H : R.Honest (M × Wi) (M × Wo)) (A : Rels K Xi Ei (M × Wi)) (B : Rels K Xo Eo (M × Wo))
      (B' : Rels K Xo' Eo' (M × Wo')) (ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (ext' : M → Xi × Ei.Str → Tr R.shape → Wo' → Wi) (P : Nums K R) (f : Xo → Option Xo')
      (g : ExtMap Eo Eo') (m : Xo × (M × Wo) → Xo' × (M × Wo')) (back : M → Xo × Eo.Str → Wo' → Wo),
    GoodAt R H A B ext P → StepAt f g m back B B' →
    (∀ u a τ b w, R.red.out a τ = some b → ext' u a τ w = ext u a τ (back u b w)) →
    GoodAt (R.post f g) (H.post f g m) A B' ext' (P.post f g)

def goodAt_pre : Prop :=
  ∀ (K M Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (Wi Wi' Wo : Type) (R : IOR Xi Ei Xo Eo)
      (H : R.Honest (M × Wi) (M × Wo)) (A' : Rels K Xi' Ei' (M × Wi')) (A : Rels K Xi Ei (M × Wi))
      (B : Rels K Xo Eo (M × Wo)) (ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (ext' : M → Xi' × Ei'.Str → Tr R.shape → Wo → Wi') (P : Nums K R) (f : Xi' → Option Xi)
      (g : ExtMap Ei' Ei) (m : Xi' × (M × Wi') → Xi × (M × Wi))
      (back : M → Xi' × Ei'.Str → Wi → Wi'),
    StepAt f g m back A' A → GoodAt R H A B ext P →
    (∀ u a x₁ τ w, f a.1 = some x₁ → ext' u a τ w = back u a (ext u (x₁, g.map a.2) τ w)) →
    GoodAt (R.pre f g) (H.pre f g m) A' B ext' (P.pre f g)

/-- A map on the explicit part; oracles and witness stay. -/
def stepAt_map : Prop :=
  ∀ (K M X X' : Type) (E : ExtSpec) (W : Type) (φ : X → X')
      (A : Rels K X E (M × W)) (B : Rels K X' E (M × W)),
    (∀ x y w, A.rel x y w → B.rel (φ x) y w) → (∀ x y, A.on (x, y) → B.on (φ x, y)) →
    (∀ w, B.core w = A.core w) → (∀ x y w, A.on (x, y) → B.relR (φ x, y) w → A.relR (x, y) w) →
    StepAt (fun x => some (φ x)) (ExtMap.id E) (fun o => (φ o.1, o.2)) (fun _ _ w => w) A B

def goodAt_postMap : Prop :=
  ∀ (K M Xi Xo Xo' : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo)
      (H : R.Honest (M × Wi) (M × Wo)) (A : Rels K Xi Ei (M × Wi)) (B : Rels K Xo Eo (M × Wo))
      (B' : Rels K Xo' Eo (M × Wo)) (ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (φ : Xo → Xo'),
    GoodAt R H A B ext P → (∀ x y w, B.rel x y w → B'.rel (φ x) y w) →
    (∀ x y, B.on (x, y) → B'.on (φ x, y)) → (∀ w, B'.core w = B.core w) →
    (∀ x y w, B.on (x, y) → B'.relR (φ x, y) w → B.relR (x, y) w) →
    GoodAt (R.post (fun x => some (φ x)) (ExtMap.id Eo))
      (H.post (fun x => some (φ x)) (ExtMap.id Eo) fun o => (φ o.1, o.2)) A B' ext
      (P.post (fun x => some (φ x)) (ExtMap.id Eo))

def goodAt_preMap : Prop :=
  ∀ (K M Xi Xi' Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo)
      (H : R.Honest (M × Wi) (M × Wo)) (A' : Rels K Xi' Ei (M × Wi))
      (A : Rels K Xi Ei (M × Wi)) (B : Rels K Xo Eo (M × Wo))
      (ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R) (φ : Xi' → Xi),
    (∀ x y w, A'.rel x y w → A.rel (φ x) y w) → (∀ x y, A'.on (x, y) → A.on (φ x, y)) →
    (∀ w, A.core w = A'.core w) →
    (∀ x y w, A'.on (x, y) → A.relR (φ x, y) w → A'.relR (x, y) w) → GoodAt R H A B ext P →
    GoodAt (R.pre (fun x => some (φ x)) (ExtMap.id Ei))
      (H.pre (fun x => some (φ x)) (ExtMap.id Ei) fun o => (φ o.1, o.2)) A' B
      (fun u a τ w => ext u (φ a.1, a.2) τ w) (P.pre (fun x => some (φ x)) (ExtMap.id Ei))

end Spec

theorem goodAt_post : Spec.goodAt_post := by
  intro K M Xi Xo Xo' Ei Eo Eo' Wi Wo Wo' R H A B B' ext ext' P f g m back hG hS he
  refine ⟨hG.point, hG.isLocal.post f g hS.isLocal, ?_, ?_, ?_, hG.prBad,
    hG.cover, hG.prCov, ?_, ?_⟩
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
  · intro w x c ρ
    show ((Strat.map m (H.strat w x c)).run ρ).2.2.1 = _
    rw [Strat.run_map]
    exact (hS.same _ _).trans (hG.same w x c ρ)
  · intro u a ha
    refine Doomed.mono _ _ ?_ (hG.know u a ha)
    intro τ hτ b w hb hw
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨xo, hxo, hf⟩ := Option.bind_eq_some_iff.1 h1
    have hb0 : R.red.out a τ = some (xo, R.imp a.2 τ) := red_out_eq_some.2 ⟨hxo, rfl⟩
    have hon := hG.onOut a τ _ ha hb0
    rw [show b = (b.1, g.map (R.imp a.2 τ)) from Prod.ext rfl h2] at hw
    rw [he u a τ _ w hb0]
    exact hτ _ _ hb0 (hS.know u xo (R.imp a.2 τ) b.1 w hon hf hw)

theorem goodAt_pre : Spec.goodAt_pre := by
  intro K M Xi Xi' Xo Ei Ei' Eo Wi Wi' Wo R H A' A B ext ext' P f g m back hS hG he
  refine ⟨hG.point, hG.isLocal.pre f g hS.isLocal, ?_, ?_, ?_, hG.prBad, ?_, hG.prCov, ?_, ?_⟩
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
  · intro w x c ρ
    exact (hG.same _ _ c ρ).trans (hS.same x w)
  · intro u a ha
    cases hf : f a.1 with
    | none =>
        refine Doomed.of_forall _ _ fun τ b w hb _ => ?_
        obtain ⟨h1, _⟩ := red_out_eq_some.1 hb
        obtain ⟨x₁, hx₁, _⟩ := Option.bind_eq_some_iff.1 h1
        rw [hf] at hx₁
        cases hx₁
    | some x₁ =>
        have hon := hS.onOut a.1 a.2 x₁ ha hf
        refine Doomed.mono _ _ ?_ (hG.know u (x₁, g.map a.2) hon)
        intro τ hτ b w hb hw
        obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
        obtain ⟨x₁', hx₁', ho⟩ := Option.bind_eq_some_iff.1 h1
        rw [hf] at hx₁'
        cases hx₁'
        rw [he u a x₁ τ w hf]
        exact hS.know u a.1 a.2 x₁ _ ha hf (hτ b w (red_out_eq_some.2 ⟨ho, h2⟩) hw)

theorem stepAt_map : Spec.stepAt_map := fun _ _ _ _ E _ _ _ _ h1 h2 h3 h4 =>
  ⟨(extMap_isLocal.1 E),
    fun x y w h => ⟨rfl, h1 x y w h⟩,
    fun x y _ h e => (Option.some.inj e) ▸ h2 x y h,
    fun _ w => h3 w, fun _ _ => rfl,
    fun u x y _ w' h e hw => h4 x y (u, w') h ((Option.some.inj e).symm ▸ hw)⟩

theorem goodAt_postMap :
    Spec.goodAt_postMap := fun K M Xi Xo Xo' Ei Eo Wi Wo R H A B B' ext P φ hG h1 h2 h3 h4 =>
  goodAt_post K M Xi Xo Xo' Ei Eo Eo Wi Wo Wo R H A B B' ext ext P _ _ _ _ hG
    (stepAt_map K M Xo Xo' Eo Wo φ B B' h1 h2 h3 h4) fun _ _ _ _ _ _ => rfl

theorem goodAt_preMap :
    Spec.goodAt_preMap := fun K M Xi Xi' Xo Ei Eo Wi Wo R H A' A B ext P φ h1 h2 h3 h4 hG =>
  goodAt_pre K M Xi Xi' Xo Ei Ei Eo Wi Wi Wo R H A' A B ext _ P _ _ _ _
      (stepAt_map K M Xi' Xi Ei Wi φ A' A h1 h2 h3 h4) hG fun _ _ _ _ _ e => by
    obtain rfl := Option.some.inj e
    rfl

end Cb
