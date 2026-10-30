-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Join.lean: rules that join blocks whose soundness is stated as `KnowAt` (Cb/G6/Cut.lean).

Statements with their proofs. No protocol occurs here. The library has six of these rules for the
bundle `GoodAt`, which names an honest prover (Cb/Ld/LdBattKit.lean: `goodAt_seq_ext`,
`goodAt_draw`; Cb/Ld/LdSigStep.lean: `goodAt_post`, `goodAt_pre`, `goodAt_postMap`,
`goodAt_preMap`). Here each of the six is given for the four clauses of `KnowAt` alone; their proofs
are the library's lines for these four clauses, which read only these four of their premises
(`knowAt_draw` calls the library's theorem; `knowAt_seq` is a case of `knowAt_seq_ext`).
`knowAt_sig` stands beside the library's lifting rule for `GoodAt` (`sigLift_goodB`,
Cb/Ld/LdSigLift.lean) and is, as that is, by `sigLift_know`. `knowAt_mono` and `knowAt_err` have no
rule for `GoodAt` beside them in the files named here. No premise speaks of an exact relation or of
an honest prover.

Main names:
  `knowAt_seq_ext`: two blocks in a row, with any extractor that is the two in turn. The errors are
    `Err.app`.
  `knowAt_seq`: the same where both extractors hand the further witness back.
  `knowAt_post`, `knowAt_pre`: a step without rounds behind or before a block. The step is given by
    three clauses (it is local; it carries the condition; the relaxed relation goes back) and the
    equation of the extractor.
  `knowAt_postMap`, `knowAt_preMap`: the same for a map on the explicit part.
  `knowAt_draw`: a round in which the verifier draws, from a bound on the number of bad draws, where
    the draw carries the condition on statements. It is the library's `goodAt_draw`, taken at joints
    whose exact relation is empty.
  `knowAt_mono`: fewer statements, a larger relation in front, a smaller relation behind, a weaker
    condition behind.
  `knowAt_err`: larger errors.
  `knowAt_sig`: over oracle messages with samples (a signature), by the library's `sigLift_know`.
  `errList_draw`: the list of errors of a draw. `errList_toList`: `errList` is the library's
    `Err.toList`.
  `ior_seq_some`, `red_draw`: what the verifier puts out for two blocks in a row, the first of which
    rejects nothing, and for a draw.

Limits: nothing on an honest prover, completeness or zero knowledge.

-/
import Cb.G6.Cut
import Cb.Ld.LdBattKit
import Cb.Ld.LdSigStep
import Cb.Ld.LdSigLiftProofs
import Ior.KnowCollRulesChainErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole
open Iop Prob Cb IOR

/-- Two blocks in a row, with any extractor that is the two in turn. -/
theorem knowAt_seq_ext {K M X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {W₁ W₂ W₃ : Type}
    {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {A : Rels K X₁ E₁ (M × W₁)}
    {B : Rels K X₂ E₂ (M × W₂)} {C : Rels K X₃ E₃ (M × W₃)}
    {e₁ : M → X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁} {e₂ : M → X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂}
    (ext : M → X₁ × E₁.Str → Tr (R₁.seq R₂).shape → W₃ → W₁) {ε₁ : Err R₁.shape}
    {ε₂ : Err R₂.shape} (g₁ : KnowAt R₁ A B e₁ ε₁) (g₂ : KnowAt R₂ B C e₂ ε₂)
    (he : ∀ m a (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) b w,
      R₁.red.out a τ₁ = some b → ext m a (Tr.app τ₁ τ₂) w = e₁ m a τ₁ (e₂ m b τ₂ w)) :
    KnowAt (R₁.seq R₂) A C ext (Err.app ε₁ ε₂) where
  point := g₁.point.elim fun p₁ => g₂.point.elim fun p₂ => ⟨Shape.IsPoint.append p₁ p₂⟩
  isLocal := g₁.isLocal.seq g₂.isLocal
  onOut := by
    intro a τ c ha hc
    obtain ⟨b, hb, hc'⟩ := Option.bind_eq_some_iff.1 ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hc)
    exact g₂.onOut b _ c (g₁.onOut a _ b ha hb) hc'
  know := by
    intro m a ha
    refine Doomed.mono _ _ ?_
      (Reduction.Know.seq_ext (g₁.know m) (g₂.know m) g₁.onOut (ext m) (he m) a ha)
    intro τ h b w hb hw
    exact h b w ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hb) hw

/-- Two blocks in a row, where both extractors hand the further witness back. -/
theorem knowAt_seq {K M X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {W : Type}
    {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {A : Rels K X₁ E₁ (M × W)}
    {B : Rels K X₂ E₂ (M × W)} {C : Rels K X₃ E₃ (M × W)} {ε₁ : Err R₁.shape} {ε₂ : Err R₂.shape}
    (g₁ : KnowAt R₁ A B (fun _ _ _ wp => wp) ε₁) (g₂ : KnowAt R₂ B C (fun _ _ _ wp => wp) ε₂) :
    KnowAt (R₁.seq R₂) A C (fun _ _ _ wp => wp) (Err.app ε₁ ε₂) :=
  knowAt_seq_ext _ g₁ g₂ fun _ _ _ _ _ _ _ => rfl

/-- A step without rounds behind a block. -/
theorem knowAt_post {K M Xi Xo Xo' : Type} {Ei Eo Eo' : ExtSpec} {Wi Wo Wo' : Type}
    {R : IOR Xi Ei Xo Eo} {A : Rels K Xi Ei (M × Wi)} {B : Rels K Xo Eo (M × Wo)}
    {B' : Rels K Xo' Eo' (M × Wo')} {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi}
    (ext' : M → Xi × Ei.Str → Tr R.shape → Wo' → Wi) {ε : Err R.shape} (f : Xo → Option Xo')
    (g : ExtMap Eo Eo') (back : M → Xo × Eo.Str → Wo' → Wo) (hG : KnowAt R A B ext ε)
    (hLoc : g.IsLocal)
    (hOn : ∀ x y x', B.on (x, y) → f x = some x' → B'.on (x', g.map y))
    (hKn : ∀ u x y x' w, B.on (x, y) → f x = some x' → B'.relR (x', g.map y) (u, w) →
      B.relR (x, y) (u, back u (x, y) w))
    (he : ∀ u a τ b w, R.red.out a τ = some b → ext' u a τ w = ext u a τ (back u b w)) :
    KnowAt (R.post f g) A B' ext' ε where
  point := hG.point
  isLocal := hG.isLocal.post f g hLoc
  onOut := by
    intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨xo, hxo, hf⟩ := Option.bind_eq_some_iff.1 h1
    have hon := hG.onOut a τ (xo, R.imp a.2 τ) ha (red_out_eq_some.2 ⟨hxo, rfl⟩)
    have := hOn xo (R.imp a.2 τ) b.1 hon hf
    rw [show b = (b.1, g.map (R.imp a.2 τ)) from Prod.ext rfl h2]
    exact this
  know := by
    intro u a ha
    refine Doomed.mono _ _ ?_ (hG.know u a ha)
    intro τ hτ b w hb hw
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨xo, hxo, hf⟩ := Option.bind_eq_some_iff.1 h1
    have hb0 : R.red.out a τ = some (xo, R.imp a.2 τ) := red_out_eq_some.2 ⟨hxo, rfl⟩
    have hon := hG.onOut a τ _ ha hb0
    rw [show b = (b.1, g.map (R.imp a.2 τ)) from Prod.ext rfl h2] at hw
    rw [he u a τ _ w hb0]
    exact hτ _ _ hb0 (hKn u xo (R.imp a.2 τ) b.1 w hon hf hw)

/-- A step without rounds before a block. -/
theorem knowAt_pre {K M Xi Xi' Xo : Type} {Ei Ei' Eo : ExtSpec} {Wi Wi' Wo : Type}
    {R : IOR Xi Ei Xo Eo} {A' : Rels K Xi' Ei' (M × Wi')} {A : Rels K Xi Ei (M × Wi)}
    {B : Rels K Xo Eo (M × Wo)} {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi}
    (ext' : M → Xi' × Ei'.Str → Tr R.shape → Wo → Wi') {ε : Err R.shape} (f : Xi' → Option Xi)
    (g : ExtMap Ei' Ei) (back : M → Xi' × Ei'.Str → Wi → Wi') (hLoc : g.IsLocal)
    (hOn : ∀ x y x', A'.on (x, y) → f x = some x' → A.on (x', g.map y))
    (hKn : ∀ u x y x' w, A'.on (x, y) → f x = some x' → A.relR (x', g.map y) (u, w) →
      A'.relR (x, y) (u, back u (x, y) w))
    (hG : KnowAt R A B ext ε)
    (he : ∀ u a x₁ τ w, f a.1 = some x₁ → ext' u a τ w = back u a (ext u (x₁, g.map a.2) τ w)) :
    KnowAt (R.pre f g) A' B ext' ε where
  point := hG.point
  isLocal := hG.isLocal.pre f g hLoc
  onOut := by
    intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    obtain ⟨x₁, hx₁, ho⟩ := Option.bind_eq_some_iff.1 h1
    exact hG.onOut (x₁, g.map a.2) τ b (hOn a.1 a.2 x₁ ha hx₁) (red_out_eq_some.2 ⟨ho, h2⟩)
  know := by
    intro u a ha
    cases hf : f a.1 with
    | none =>
        refine Doomed.of_forall _ _ fun τ b w hb _ => ?_
        obtain ⟨h1, _⟩ := red_out_eq_some.1 hb
        obtain ⟨x₁, hx₁, _⟩ := Option.bind_eq_some_iff.1 h1
        rw [hf] at hx₁
        cases hx₁
    | some x₁ =>
        have hon := hOn a.1 a.2 x₁ ha hf
        refine Doomed.mono _ _ ?_ (hG.know u (x₁, g.map a.2) hon)
        intro τ hτ b w hb hw
        obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
        obtain ⟨x₁', hx₁', ho⟩ := Option.bind_eq_some_iff.1 h1
        rw [hf] at hx₁'
        cases hx₁'
        rw [he u a x₁ τ w hf]
        exact hKn u a.1 a.2 x₁ _ ha hf (hτ b w (red_out_eq_some.2 ⟨ho, h2⟩) hw)

/-- A map on the explicit part behind a block. Oracles and witness stay. -/
theorem knowAt_postMap {K M Xi Xo Xo' : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}
    {R : IOR Xi Ei Xo Eo} {A : Rels K Xi Ei (M × Wi)} {B : Rels K Xo Eo (M × Wo)}
    {B' : Rels K Xo' Eo (M × Wo)} {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi}
    {ε : Err R.shape} (φ : Xo → Xo') (hG : KnowAt R A B ext ε)
    (h2 : ∀ x y, B.on (x, y) → B'.on (φ x, y))
    (h4 : ∀ x y w, B.on (x, y) → B'.relR (φ x, y) w → B.relR (x, y) w) :
    KnowAt (R.post (fun x => some (φ x)) (ExtMap.id Eo)) A B' ext ε :=
  knowAt_post ext _ _ (fun _ _ w => w) hG (extMap_isLocal.1 Eo)
    (fun x y _ h e => (Option.some.inj e) ▸ h2 x y h)
    (fun u x y _ w h e hw => h4 x y (u, w) h ((Option.some.inj e).symm ▸ hw))
    fun _ _ _ _ _ _ => rfl

/-- A map on the explicit part before a block. -/
theorem knowAt_preMap {K M Xi Xi' Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}
    {R : IOR Xi Ei Xo Eo} {A' : Rels K Xi' Ei (M × Wi)} {A : Rels K Xi Ei (M × Wi)}
    {B : Rels K Xo Eo (M × Wo)} {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    (φ : Xi' → Xi) (h2 : ∀ x y, A'.on (x, y) → A.on (φ x, y))
    (h4 : ∀ x y w, A'.on (x, y) → A.relR (φ x, y) w → A'.relR (x, y) w)
    (hG : KnowAt R A B ext ε) :
    KnowAt (R.pre (fun x => some (φ x)) (ExtMap.id Ei)) A' B
      (fun u a τ w => ext u (φ a.1, a.2) τ w) ε :=
  knowAt_pre _ _ _ (fun _ _ w => w) (extMap_isLocal.1 Ei)
    (fun x y _ h e => (Option.some.inj e) ▸ h2 x y h)
    (fun u x y _ w h e hw => h4 x y (u, w) h ((Option.some.inj e).symm ▸ hw)) hG
    fun _ _ _ _ _ e => by
      obtain rfl := Option.some.inj e
      rfl

/-- A draw, from a bound on the number of bad draws: the library's `goodAt_draw` at joints whose
exact relation is empty. `KnowAt` reads neither that relation nor the core. -/
theorem knowAt_draw {K M X X' : Type} {Ex : ExtSpec} {Wp D : Type} [Fintype D] [Nonempty D]
    (nx : X → D → X') (A : Rels K X Ex (M × Wp)) (A' : Rels K X' Ex (M × Wp)) (err : ℕ)
    (hon : ∀ x y β, A.on (x, y) → A'.on (nx x β, y))
    (hcnt : ∀ x y (m : M), A.on (x, y) →
      cnt (fun β => ∃ wp, A'.relR (nx x β, y) (m, wp) ∧ ¬ A.relR (x, y) (m, wp)) ≤ err) :
    KnowAt (IOR.draw D nx Ex) A A' (fun _ _ _ wp => wp) (Nums.draw K D nx Ex err).err :=
  have h := ((goodAt_iff _ _ _ _ _ _).1
    (goodAt_draw K M X X' Ex Wp D nx ⟨fun _ _ _ => False, A.relR, A.on, A.core⟩
      ⟨fun _ _ _ => False, A'.relR, A'.on, A.core⟩ err (fun _ _ _ _ h => h) hon (fun _ => rfl)
      hcnt)).1
  ⟨h.point, h.isLocal, h.onOut, h.know⟩

/-- Fewer statements, a larger relation in front, a smaller relation behind (asked only at outputs
that meet the condition), a weaker condition behind. -/
theorem knowAt_mono {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {A A' : Rels K Xi Ei (M × Wi)} {B B' : Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape} (h : KnowAt R A B ext ε)
    (ho : ∀ a, A'.on a → A.on a) (hA : ∀ a w, A'.on a → A.relR a w → A'.relR a w)
    (hB : ∀ b w, B.on b → B'.relR b w → B.relR b w) (hb : ∀ b, B.on b → B'.on b) :
    KnowAt R A' B' ext ε where
  point := h.point
  isLocal := h.isLocal
  onOut := fun a τ b ha hb' => hb b (h.onOut a τ b (ho a ha) hb')
  know := fun m a ha =>
    Doomed.mono _ _
      (fun τ hτ b w hb' hw =>
        hA a _ ha (hτ b w hb' (hB b _ (h.onOut a τ b (ho a ha) hb') hw)))
      (h.know m a (ho a ha))

/-- Larger errors. -/
theorem knowAt_err {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {A : Rels K Xi Ei (M × Wi)} {B : Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε ε' : Err R.shape} (h : KnowAt R A B ext ε)
    (hε : Err.le ε ε') : KnowAt R A B ext ε' :=
  ⟨h.point, h.isLocal, h.onOut, fun m => (h.know m).mono_err hε⟩

/-- Over a signature, by the library's `sigLift_know`, which takes the clause `know` as it
stands. -/
theorem knowAt_sig {E : Type} [Field E] (S : Sig E) {Kc St St' Wp Wp' : Type} {E₀ E₀' : ExtSpec}
    {R : IOR St E₀ St' E₀'} {A : Rels Kc St E₀ (S.Msg × Wp)} {B : Rels Kc St' E₀' (S.Msg × Wp')}
    {ext : S.Msg → St × E₀.Str → Tr R.shape → Wp' → Wp} {ε : Err R.shape}
    (h : KnowAt R A B ext ε) :
    (R.keep S.Smp S.ext).red.Know (S.over A).on (S.over A).relR (S.over B).relR
      (fun a τ w => (w.1, ext (S.msgs w.1) (a.1.1, a.2.1) τ w.2)) ε :=
  sigLift_know E S Kc St St' Wp Wp' E₀ E₀' R A B ext ε h.know

/-- The list of errors of a draw. -/
theorem errList_draw {K X X' D : Type} [Fintype D] [Nonempty D] (nx : X → D → X') (Ex : ExtSpec)
    (err : ℕ) : errList (Nums.draw K D nx Ex err).err = [err] := rfl

/-- `errList` is the library's `Err.toList`. -/
theorem errList_toList : ∀ {s : Shape} (ε : Err s), errList ε = ε.toList
  | [], _ => rfl
  | _ :: _, (e, ε) => congrArg (e :: ·) (errList_toList ε)

/-! ### What the verifier puts out -/

/-- Two blocks in a row, the first of which rejects nothing. -/
theorem ior_seq_some {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} (R₁ : IOR X₁ E₁ X₂ E₂)
    (R₂ : IOR X₂ E₂ X₃ E₃) (v₁ : X₁ × E₁.Str → Tr R₁.shape → X₂ × E₂.Str)
    (h : ∀ a τ, R₁.red.out a τ = some (v₁ a τ)) (a : X₁ × E₁.Str)
    (τ : Tr (R₁.seq R₂).shape) :
    (R₁.seq R₂).red.out a τ = R₂.red.out (v₁ a (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ) := by
  rw [IOR.red_seq_out R₁ R₂ a τ]
  show (R₁.red.out a (Tr.fst τ)).bind (fun b => R₂.red.out b (Tr.snd (s := R₁.shape) τ)) = _
  rw [h]
  rfl

/-- A draw rejects nothing and copies the oracles. -/
theorem red_draw {X X' D : Type} [Fintype D] [Nonempty D] (nx : X → D → X') (Ex : ExtSpec)
    (a : X × Ex.Str) (τ : Tr (IOR.draw D nx Ex).shape) :
    ∃ β, (IOR.draw D nx Ex).red.out a τ = some (nx a.1 β, a.2) := ⟨_, rfl⟩

end TWhole
