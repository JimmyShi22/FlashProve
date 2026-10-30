-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/FrameProofs.lean: proofs of the statements of Ior/Frame.lean on further oracles that are only
copied, on steps without rounds before R, after R and alone, and of the frame rule for copied
components.

The other statements of Ior/Frame.lean are proved in Ior/FrameProofsBasic.lean.
R is an interactive oracle reduction (`IOR`, Ior/Ior.lean).
`Good` (Ior/Chain.lean): see the head of Ior/Frame.lean.

Main names (statements and hypotheses: Ior/Frame.lean; each concludes `Good`, Ior/Chain.lean, and
all but `good_pure` also have it as a premise):
  `good_post`: a step without rounds after R.
  `good_pre`: a step without rounds before R.
  `good_keepE`: further oracles that are only copied.
  `good_pure`: a step without rounds, alone.
  `good_keep_frame`: the frame rule for copied components.

Each construction but `IOR.pure` has the shape, the verifier's positions in the prover's oracles and
the blinding of R itself, so a view of the new IOR is a view of R under another type (`View.keepE`,
`View.pre`, `View.post`), and the output of the new honest side is the output of the old one,
carried over.
A simulator of a reduction (`Honest.Sim`) is a function from the explicit statement, the verifier's
randomness ρ, a set T of further positions, and a partial reading of the implicit instance, to a
distribution on `Option (View R)`. `H.ExactWith Ri bud S`: for every (x, y, w) in Ri, every ρ
outside `H.Hid w x` and every T with `bud ρ T`, the distribution `H.output w x ρ T` equals
`S x ρ T a`, where a gives the symbols of y at the positions `R.given ρ T` and `none` at the others.
`Exact` says that some S does. `Exact` is a premise and the conclusion of `Honest.Exact.keepE`,
`Honest.Exact.pre`, `Honest.Exact.post`. `Good.exact`: `Honest.Exact`, Ior/Honest.lean.
The simulators:
 (1) After R, the simulator is the old one.
 (2) With copied oracles, it is the old one, given the answers on the first component.
 (3) Before R, it takes from the answers given some oracles that agree with them (a choice), applies
     the map g and gives the old simulator what it is to be given; because g is local these are the
     true symbols.
 (4) Without rounds, the view is empty.
Two parts of the bundle (`Good.isLocal`, `Good.exact`) are also there one by one: `IsLocal.keepE`,
`IsLocal.pre`, `IsLocal.post`, `Honest.Exact.keepE`, `Honest.Exact.pre`, `Honest.Exact.post`.

Limits: see Limits in the head of Ior/Frame.lean.
Terms: lean/GLOSSARY.md.
-/
import Ior.Frame
import Ior.ExactSeq
import Ior.FrameProofsBasic

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K X X' Xi Xi' Xo Xo' Z : Type}
  {E E' Ei Ei' Eo Eo' F : ExtSpec} {W W' Wi Wi' Wo Wo' Wz : Type}

/-- When the reduction of an IOR outputs a statement. -/
theorem red_out_eq_some {R : IOR Xi Ei Xo Eo} {a : Xi × Ei.Str} {τ : Tr R.shape} {b : Xo × Eo.Str} :
    R.red.out a τ = some b ↔ R.out a.1 a.2 τ = some b.1 ∧ b.2 = R.imp a.2 τ := by
  show (R.out a.1 a.2 τ).map (fun xo => (xo, R.imp a.2 τ)) = some b ↔ _
  cases h : R.out a.1 a.2 τ with
  | none => simp
  | some xo =>
      obtain ⟨b1, b2⟩ := b
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

/-! ## 1. A step after R -/

section Post
variable {R : IOR Xi Ei Xo Eo} (f : Xo → Option Xo') (g : ExtMap Eo Eo')

open Classical in
theorem IsLocal.post (h : R.IsLocal) (hg : g.IsLocal) : (R.post f g).IsLocal where
  out := fun x y y' τ τ' hρ hπ hE hO =>
    congrArg (fun o => Option.bind o f) (h.out x y y' τ τ' hρ hπ hE hO)
  imp := fun y y' τ τ' q hρ hπ hE hO => hg _ _ q fun p hp =>
    h.imp y y' τ τ' p hρ hπ (fun e he => hE e (Finset.mem_biUnion.2 ⟨p, hp, he⟩))
      (fun e he => hO e (Finset.mem_biUnion.2 ⟨p, hp, he⟩))

/-- A view of R as a view of `R.post f g`. -/
def View.post (v : View R) : View (R.post f g) := ⟨v.plains, v.orc⟩

theorem Honest.output_post (H : R.Honest Wi Wo) (m : Xo × Wo → Xo' × Wo') (w : Wi) (x : Xi)
    (ρ : Rho R.shape) (T : Finset (OPos R.shape)) :
    (H.post f g m).output w x ρ T = (H.output w x ρ T).map (Option.map (View.post f g)) := by
  by_cases h : ρ ∈ H.withheld w x
  · rw [H.output_of_mem T h, PMF.pure_map]
    exact (H.post f g m).output_of_mem T h
  · rw [H.output_of_not_mem T h, PMF.map_comp]
    refine ((H.post f g m).output_of_not_mem T h).trans ?_
    refine congrArg (fun k => PMF.map k (unif H.Coin)) (funext fun c => ?_)
    show some ((R.post f g).view T ((Strat.map m (H.strat w x c)).run ρ).1) =
      some (View.post f g (R.view T ((H.strat w x c).run ρ).1))
    rw [Strat.run_map]
    rfl

theorem Honest.Exact.post {H : R.Honest Wi Wo} {Ri : Xi → Ei.Str → Wi → Prop}
    {bud : Rho R.shape → Finset (OPos R.shape) → Prop} (h : H.Exact Ri bud)
    (m : Xo × Wo → Xo' × Wo') :
    (H.post f g m).Exact Ri bud := by
  obtain ⟨S, hS⟩ := h
  refine ⟨fun x ρ T a => (S x ρ T a).map (Option.map (View.post f g)), fun x y w hR ρ hρ T hT => ?_⟩
  rw [Honest.output_post]
  exact congrArg _ (hS x y w hR ρ hρ T hT)

end Post

/-! ## 2. A step before R -/

section Pre
variable {R : IOR Xi Ei Xo Eo} (f : Xi' → Option Xi) (g : ExtMap Ei' Ei)

open Classical in
theorem IsLocal.pre (h : R.IsLocal) (hg : g.IsLocal) : (R.pre f g).IsLocal where
  out := fun x y y' τ τ' hρ hπ hE hO => by
    show (f x).bind (fun x₁ => R.out x₁ (g.map y) τ) = (f x).bind fun x₁ => R.out x₁ (g.map y') τ'
    refine congrArg _ (funext fun x₁ => ?_)
    exact h.out x₁ _ _ τ τ' hρ hπ
      (fun p hp => hg y y' p fun e he => hE e (Finset.mem_biUnion.2 ⟨p, hp, he⟩)) hO
  imp := fun y y' τ τ' q hρ hπ hE hO =>
    h.imp _ _ τ τ' q hρ hπ
      (fun p hp => hg y y' p fun e he => hE e (Finset.mem_biUnion.2 ⟨p, hp, he⟩)) hO

def View.pre (v : View R) : View (R.pre f g) := ⟨v.plains, v.orc⟩

theorem Honest.output_pre (H : R.Honest Wi Wo) (m : Xi' × Wi' → Xi × Wi) (w : Wi') (x : Xi')
    (ρ : Rho R.shape) (T : Finset (OPos R.shape)) :
    (H.pre f g m).output w x ρ T =
      (H.output (m (x, w)).2 (m (x, w)).1 ρ T).map (Option.map (View.pre f g)) := by
  by_cases h : ρ ∈ H.withheld (m (x, w)).2 (m (x, w)).1
  · rw [H.output_of_mem T h, PMF.pure_map]
    exact (H.pre f g m).output_of_mem T h
  · rw [H.output_of_not_mem T h, PMF.map_comp]
    exact (H.pre f g m).output_of_not_mem T h

open Classical in
/-- Every position from which a symbol for the old simulator is computed is among the positions
given. -/
theorem src_subset_given_pre {ρ : Rho R.shape} {T : Finset (OPos R.shape)} {q : Ei.Pos}
    (hq : q ∈ R.given ρ T) {p : Ei'.Pos} (hp : p ∈ g.src q) : p ∈ (R.pre f g).given ρ T := by
  rcases mem_given.1 hq with hq | ⟨r, hr, hq⟩
  · exact mem_given.2 (Or.inl (Finset.mem_biUnion.2 ⟨q, hq, hp⟩))
  · exact mem_given.2 (Or.inr ⟨r, hr, Finset.mem_biUnion.2 ⟨q, hq, hp⟩⟩)

theorem Honest.Exact.pre {H : R.Honest Wi Wo} {Ri : Xi → Ei.Str → Wi → Prop}
    {Ri' : Xi' → Ei'.Str → Wi' → Prop} {bud : Rho R.shape → Finset (OPos R.shape) → Prop}
    (h : H.Exact Ri bud) (hg : g.IsLocal) (m : Xi' × Wi' → Xi × Wi)
    (hm : ∀ x y w, Ri' x y w → f x = some (m (x, w)).1 ∧ Ri (m (x, w)).1 (g.map y) (m (x, w)).2) :
    (H.pre f g m).Exact Ri' bud := by
  obtain ⟨S, hS⟩ := h
  refine ⟨fun x ρ T a =>
      (f x).elim (PMF.pure none) fun x₁ =>
        (pick (Ei'.Fits a)).elim (PMF.pure none) fun y' =>
          (S x₁ ρ T (Ei.ans (R.given ρ T) (g.map y'))).map (Option.map (View.pre f g)),
    fun x y w hR ρ hρ T hT => ?_⟩
  obtain ⟨hf, hRi⟩ := hm x y w hR
  obtain ⟨y', hy', hF⟩ :=
    pick_spec (P := Ei'.Fits (Ei'.ans ((R.pre f g).given ρ T) y)) ⟨y, Ei'.fits_ans _ y⟩
  have e : Ei.ans (R.given ρ T) (g.map y') = Ei.ans (R.given ρ T) (g.map y) :=
    Ei.ans_congr fun q hq => hg y' y q fun p hp => hF.rd_eq (src_subset_given_pre f g hq hp)
  rw [Honest.output_pre]
  show _ = (f x).elim (PMF.pure none) fun x₁ =>
        (pick (Ei'.Fits (Ei'.ans ((R.pre f g).given ρ T) y))).elim (PMF.pure none) fun y' =>
    (S x₁ ρ T (Ei.ans (R.given ρ T) (g.map y'))).map (Option.map (View.pre f g))
  rw [hf, hy', Option.elim_some, Option.elim_some, e]
  exact congrArg _ (hS _ _ _ hRi ρ hρ T hT)

end Pre

/-! ## 3. Further oracles that are only copied -/

section KeepE
variable {R : IOR Xi Ei Xo Eo} (F : ExtSpec)

theorem IsLocal.keepE (h : R.IsLocal) : (R.keepE F).IsLocal where
  out := fun x y y' τ τ' hρ hπ hE hO =>
    h.out x y.1 y'.1 τ τ' hρ hπ
      (fun p hp => Sum.inl.inj (hE (Sum.inl p) (Finset.mem_map.2 ⟨p, hp, rfl⟩))) hO
  imp := fun y y' τ τ' q hρ hπ hE hO => by
    cases q with
    | inl q =>
        exact congrArg Sum.inl
          (h.imp y.1 y'.1 τ τ' q hρ hπ
            (fun p hp => Sum.inl.inj (hE (Sum.inl p) (Finset.mem_map.2 ⟨p, hp, rfl⟩))) hO)
    | inr p => exact congrArg Sum.inr (Sum.inr.inj (hE (Sum.inr p) (Finset.mem_singleton.2 rfl)))

def View.keepE (v : View R) : View (R.keepE F) := ⟨v.plains, v.orc⟩

theorem Honest.output_keepE (H : R.Honest Wi Wo) (w : Wi) (x : Xi)
    (ρ : Rho R.shape) (T : Finset (OPos R.shape)) :
    (H.keepE F).output w x ρ T = (H.output w x ρ T).map (Option.map (View.keepE F)) := by
  by_cases h : ρ ∈ H.withheld w x
  · rw [H.output_of_mem T h, PMF.pure_map]
    exact (H.keepE F).output_of_mem T h
  · rw [H.output_of_not_mem T h, PMF.map_comp]
    exact (H.keepE F).output_of_not_mem T h

theorem inl_mem_given_keepE {ρ : Rho R.shape} {T : Finset (OPos R.shape)} {p : Ei.Pos} :
    Sum.inl p ∈ (R.keepE F).given ρ T ↔ p ∈ R.given ρ T := by
  have hm : ∀ U : Finset Ei.Pos,
      (Sum.inl p : Ei.Pos ⊕ F.Pos) ∈ U.map Function.Embedding.inl ↔ p ∈ U := fun U =>
    ⟨fun h => by
      obtain ⟨p', hp', e⟩ := Finset.mem_map.1 h
      exact Sum.inl.inj e ▸ hp', fun h => Finset.mem_map.2 ⟨p, h, rfl⟩⟩
  rw [mem_given, mem_given]
  exact or_congr (hm _) (exists_congr fun r => and_congr_right fun _ => hm _)

theorem Honest.Exact.keepE {H : R.Honest Wi Wo} {Ri : Xi → Ei.Str → Wi → Prop}
    {bud : Rho R.shape → Finset (OPos R.shape) → Prop} (h : H.Exact Ri bud) :
    (H.keepE F).Exact (fun x y w => Ri x y.1 w) bud := by
  obtain ⟨S, hS⟩ := h
  refine ⟨fun x ρ T a =>
      (S x ρ T fun p => (a (Sum.inl p)).bind Sum.getLeft?).map (Option.map (View.keepE F)),
    fun x y w hR ρ hρ T hT => ?_⟩
  have e : (fun p => ((Ei.prod F).ans ((R.keepE F).given ρ T) y (Sum.inl p)).bind Sum.getLeft?) =
      Ei.ans (R.given ρ T) y.1 := by
    funext p
    by_cases hp : p ∈ R.given ρ T
    · rw [(Ei.prod F).ans_of_mem y ((inl_mem_given_keepE F).2 hp), Ei.ans_of_mem y.1 hp]
      rfl
    · rw [(Ei.prod F).ans_of_not_mem y (fun h => hp ((inl_mem_given_keepE F).1 h)),
        Ei.ans_of_not_mem y.1 hp]
      rfl
  rw [Honest.output_keepE]
  show _ = (S x ρ T fun p =>
        ((Ei.prod F).ans ((R.keepE F).given ρ T) y (Sum.inl p)).bind Sum.getLeft?).map
      (Option.map (View.keepE F))
  rw [e]
  exact congrArg _ (hS x y.1 w hR ρ hρ T hT)

end KeepE

end IOR

open IOR

theorem good_post : Spec.good_post := by
  intro K Xi Xo Xo' Ei Eo Eo' R Wi Wo Wo' H A B B' ext P f g m back io hG hS hio
  refine ⟨hG.point, hG.isLocal.post f g hS.isLocal, ?_, ?_, ?_, hG.prBad, hG.cover, hG.prCov,
    ?_, hG.exact.post f g m⟩
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
    have h3 := hτ _ _ hb0 (hS.know xo (R.imp a.2 τ) b.1 w hon hf hw)
    have e : R.imp a.2 τ = io a.2 (Tr.read (s := R.shape) τ) := hio a.2 τ
    rw [e] at h3
    exact h3

theorem good_pre : Spec.good_pre := by
  intro K Xi Xi' Xo Ei Ei' Eo R Wi Wi' Wo H A' A B ext P f g m back hS hG
  refine ⟨hG.point, hG.isLocal.pre f g hS.isLocal, ?_, ?_, ?_, hG.prBad, ?_, hG.prCov,
    ?_, hG.exact.pre f g hS.isLocal m hS.acc⟩
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
        exact hS.know a.1 a.2 x₁ _ ha hf (hτ b w (red_out_eq_some.2 ⟨ho, h2⟩) hw)

theorem good_keepE : Spec.good_keepE := by
  intro K Xi Xo Ei Eo F R Wi Wo H A B ext P hG
  refine ⟨hG.point, hG.isLocal.keepE F, ?_, ?_, hG.keeps, hG.prBad, hG.cover,
    hG.prCov, ?_, hG.exact.keepE F⟩
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

theorem good_pure : Spec.good_pure := by
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

theorem good_keep_frame : Spec.good_keep_frame := by
  intro K Xi Xo Z Ei Eo F R Wi Wo Wz H A B ext P S SR T hG
  have h1 := good_keepE K (Xi × Z) (Xo × Z) Ei Eo F (R.keepX Z) Wi Wo (H.keepX Z) (A.keepX Z)
    (B.keepX Z) ext (P.keepX Z) (good_keepX K Xi Xo Z Ei Eo R Wi Wo H A B ext P hG)
  refine good_frame K (Xi × Z) (Xo × Z) (Ei.prod F) (Eo.prod F) (R.keep Z F) Wi Wo Wz
    (H.keep Z F) (A.keep Z F) (B.keep Z F) (fun y o w => ext y.1 o w) (P.keep Z F)
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

end Iop
