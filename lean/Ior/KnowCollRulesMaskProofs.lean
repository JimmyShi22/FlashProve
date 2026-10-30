-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollRulesMaskProofs.lean: proofs of the statements of Ior/KnowCollRulesMask.lean
(honest-verifier zero knowledge of a chain whose masks are sent in advance), each proved as it
stands there.
Block, prefix, `Fresh`: see the head of Ior/KnowCollRulesMask.lean.

Main names (statements and hypotheses: Ior/KnowCollRulesMask.lean):
  `exact_seq_masked`: see its statement there.
  `goodT_seq_masked`: for the bundles (`GoodT`, `GoodM`): see its statement there.
  `fresh_snd`, `fresh_seq`, `fresh_conseq`, `blind_carry`: see their statements there.

Why the proof of `exact_seq_masked` has its form: outside the withheld set, what the whole shows is
a function G (`mG`) of (the first prover's coins c, what the block reads k): the block's plain
parts in closed form, glued to the first transcript.
G depends on c only through the first view (at the further positions of the rule for chains) and
the explicit part handed on.
The real run is the law over c of G c (kc of the witness handed on).
The simulator is, by exactness of the prefix, the item "masked messages" and the further hypotheses
of `mG_sim`, the law over (c, M) of G c (put M (kc ..)).
In Lean: `mG_real`, `mG_sim`.
`Fresh` says that the arguments of G have the same law in both.
No honest block is ever run after a simulated prefix: the block's law is taken given the real
prefix, and the prefix's law is replaced last.
`fresh_seq`, `fresh_snd`: the same device (Prob/LawKit.lean: `map_eq_of_factor`: quantities that
are determined in the same way by quantities of the same law have the same law).

Limits: see Limits in the head of Ior/KnowCollRulesMask.lean.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollRulesMask
import Ior.ExactSeq
import Ior.FrameProofsBasic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace MaskKit
variable {α α' β γ δ : Type}

/-- an independent further coin beside two quantities of the same law -/
theorem map_pair_indep [Fintype α] [Nonempty α] [Fintype α'] [Nonempty α'] [Fintype β] [Nonempty β]
    (u : α → δ) (u' : α' → δ) (he : (unif α).map u = (unif α').map u') :
    (unif (α × β)).map (fun a => (u a.1, a.2)) = (unif (α' × β)).map (fun a => (u' a.1, a.2)) := by
  have h1 : (unif (α × β)).map (fun a => (u a.1, a.2)) =
      ((unif α).map u).bind fun d => (unif β).map fun b => (d, b) :=
    map_unif_bind_factor _ u (fun d => (unif β).map fun b => (d, b)) fun _ => rfl
  have h2 : (unif (α' × β)).map (fun a => (u' a.1, a.2)) =
      ((unif α').map u').bind fun d => (unif β).map fun b => (d, b) :=
    map_unif_bind_factor _ u' (fun d => (unif β).map fun b => (d, b)) fun _ => rfl
  rw [h1, h2, he]

/-- the coins renamed -/
theorem map_unif_of_equiv [Fintype α] [Nonempty α] [Fintype α'] [Nonempty α']
    (e : α ≃ α') (f : α' → γ) :
    (unif α).map (fun a => f (e a)) = (unif α').map f := by
  have h : (unif α).map (fun a => f (e a)) = ((unif α).map e).map f :=
    (PMF.map_comp e (unif α) f).symm
  rw [h, map_unif_equiv]

end MaskKit

namespace IOR
variable {X₁ X₂ X₃ : Type}
  {E₁ E₂ E₃ : ExtSpec} {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {W₁ W₂ W₃ : Type}

/-- Under the hypotheses below, the view of the composition is determined by the two views. -/
theorem view_app_of_views (ρ : Rho (R₁.shape ++ R₂.shape))
    (T : Finset (OPos (R₁.shape ++ R₂.shape))) {τ₁ τ₁' : Tr R₁.shape} {τ₂ τ₂' : Tr R₂.shape}
    (a1 : τ₁.rho = Rho.fst ρ) (a1' : τ₁'.rho = Rho.fst ρ) (a2 : τ₂.rho = Rho.snd (s := R₁.shape) ρ)
    (a2' : τ₂'.rho = Rho.snd (s := R₁.shape) ρ)
    (h1 : R₁.view (firstT R₁ R₂ ρ T) τ₁ = R₁.view (firstT R₁ R₂ ρ T) τ₁')
    (h2 : R₂.view (partR R₁.shape T) τ₂ = R₂.view (partR R₁.shape T) τ₂') :
    (R₁.seq R₂).view T (Tr.app τ₁ τ₂) = (R₁.seq R₂).view T (Tr.app τ₁' τ₂') := by
  have f1 : (R₁.view (firstT R₁ R₂ ρ T) τ₁).Fits τ₁'.rho τ₁' := by
    rw [h1]
    exact view_fits _ τ₁'
  have f2 : (R₂.view (partR R₁.shape T) τ₂).Fits τ₂'.rho τ₂' := by
    rw [h2]
    exact view_fits _ τ₂'
  exact view_app_congr ρ T a1 a1' a2 a2' f1.2.1.symm f2.2.1.symm
    (fun p hp => (f1.read_eq (a1 ▸ hp)).symm) (fun p hp => (f2.read_eq (a2 ▸ hp)).symm)

/-- Under the hypotheses below, what is glued to a first transcript depends on it only through its
view. -/
theorem glue_left_congr (ρ : Rho (R₁.shape ++ R₂.shape)) (T : Finset (OPos (R₁.shape ++ R₂.shape)))
    {τ₁ τ₁' : Tr R₁.shape} (a1 : τ₁.rho = Rho.fst ρ) (a1' : τ₁'.rho = Rho.fst ρ)
    (h1 : R₁.view (firstT R₁ R₂ ρ T) τ₁ = R₁.view (firstT R₁ R₂ ρ T) τ₁') :
    glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T τ₁ = glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T τ₁' := by
  funext o₂
  cases o₂ with
  | none => rfl
  | some V₂ => exact pick_map_congr fun τ₂ hτ₂ => view_app_of_views ρ T a1 a1' hτ₂.1 hτ₂.1 h1 rfl

/-- What the whole shows, as a function of the first prover's coins and of what the masked block
reads. -/
def mG (H₁ : R₁.Honest W₁ W₂) (D : MaskData R₂ W₂) (h : IsEmpty (OPos R₂.shape))
    (w : W₁) (x : X₁) (ρ : Rho (R₁.shape ++ R₂.shape)) (T : Finset (OPos (R₁.shape ++ R₂.shape)))
    (c : H₁.Coin) (k : D.Kc) : Option (View (R₁.seq R₂)) :=
  glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T ((H₁.strat w x c).run (Rho.fst ρ)).1
    (some (bareView h
        (D.msg k (D.pub ((H₁.strat w x c).run (Rho.fst ρ)).2.1) (Rho.snd (s := R₁.shape) ρ))))

theorem mG_real (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (D : MaskData R₂ W₂) (m : H₂.MM D)
    (w : W₁) (x : X₁) (ρ : Rho (R₁.shape ++ R₂.shape))
    (T : Finset (OPos (R₁.shape ++ R₂.shape))) (c : H₁.Coin × H₂.Coin) :
    some ((R₁.seq R₂).view T (((H₁.seq H₂).strat w x c).run ρ).1) =
      mG H₁ D m.noOrc w x ρ T c.1 (D.kc ((H₁.strat w x c.1).run (Rho.fst ρ)).2.2) := by
  have e : bareView m.noOrc
        (D.msg (D.kc ((H₁.strat w x c.1).run (Rho.fst ρ)).2.2)
          (D.pub ((H₁.strat w x c.1).run (Rho.fst ρ)).2.1) (Rho.snd (s := R₁.shape) ρ)) =
      R₂.view (partR R₁.shape T)
        ((H₂.strat ((H₁.strat w x c.1).run (Rho.fst ρ)).2.2
            ((H₁.strat w x c.1).run (Rho.fst ρ)).2.1 c.2).run
          (Rho.snd (s := R₁.shape) ρ)).1 := by
    rw [IOR.view_eq_bare R₂ m.noOrc, m.run]
  unfold mG
  rw [e, Honest.run_seq]
  exact (glue_view ρ T (Strat.rho_run _ _) (Strat.rho_run _ _)).symm

theorem mG_sim {H₁ : R₁.Honest W₁ W₂} {H₂ : R₂.Honest W₂ W₃} {Ra : X₁ → E₁.Str → W₁ → Prop}
    {Rb : X₂ → E₂.Str → W₂ → Prop} (D : MaskData R₂ W₂) (m : H₂.MM D) (hL : R₁.IsLocal)
    (hA : H₁.Acc Ra Rb) (hCl : ∀ x y w, Rb x y w → D.Cl (D.pub x) (D.kc w)) (x : X₁) (y : E₁.Str)
    (w : W₁) (hR : Ra x y w) (ρ : Rho (R₁.shape ++ R₂.shape)) (hw₁ : Rho.fst ρ ∉ H₁.withheld w x)
    (T : Finset (OPos (R₁.shape ++ R₂.shape))) (c : H₁.Coin) :
    simCont (D.simOwn m.noOrc) x ρ T (E₁.ans ((R₁.seq R₂).given ρ T) y)
        (R₁.view (firstT R₁ R₂ ρ T) ((H₁.strat w x c).run (Rho.fst ρ)).1) =
      (unif D.Mk).map fun M =>
        mG H₁ D m.noOrc w x ρ T c (D.put M (D.kc ((H₁.strat w x c).run (Rho.fst ρ)).2.2)) := by
  obtain ⟨ho, hRb⟩ := hA x y w c _ hR hw₁
  rw [simCont_view hL _ x y ρ T _ (Strat.rho_run _ _) _ ho]
  show ((D.sim (D.pub ((H₁.strat w x c).run (Rho.fst ρ)).2.1) (Rho.snd (s := R₁.shape) ρ)).map
      fun pl => some (bareView m.noOrc pl)).map _ = _
  rw [← m.law _ _ _ (hCl _ _ _ hRb), PMF.map_comp, PMF.map_comp]
  rfl

/-- A prefix that is honest-verifier zero knowledge and fresh, then a masked block, with the
simulator named. (not all hypotheses are named here: see the statement below) -/
theorem exactWith_seq_masked {H₁ : R₁.Honest W₁ W₂} {H₂ : R₂.Honest W₂ W₃}
    {Ra : X₁ → E₁.Str → W₁ → Prop} {Rb : X₂ → E₂.Str → W₂ → Prop}
    {b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop} {S₁ : Honest.Sim R₁} (D : MaskData R₂ W₂)
    (m : H₂.MM D) (hL : R₁.IsLocal) (hA : H₁.Acc Ra Rb) (h₁ : H₁.ExactWith Ra b₁ S₁)
    (hF : H₁.Fresh Ra b₁ D.kc D.Mk D.put) (hCl : ∀ x y w, Rb x y w → D.Cl (D.pub x) (D.kc w)) :
    (H₁.seq H₂).ExactWith Ra (budSeq R₁ R₂ b₁ fun _ _ => True) (simSeq S₁ (D.simOwn m.noOrc)) := by
  intro x y w hR ρ hρ T hT
  obtain ⟨-, hb₁⟩ := hT (partL T) (partR R₁.shape T) (fun _ => mem_partL) (fun _ => mem_partR)
  have hρ₁ : Rho.fst (s := R₁.shape) (t := R₂.shape) ρ ∉ H₁.Hid w x := fun h => hρ (Or.inl h)
  have e₁ := h₁ x y w hR (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ) hρ₁ (firstT R₁ R₂ ρ T) hb₁
  unfold simSeq
  rw [E₁.cut_ans (given_first_subset ρ T) y, ← e₁]
  by_cases hw₁ : Rho.fst (s := R₁.shape) (t := R₂.shape) ρ ∈ H₁.withheld w x
  · have hw : ρ ∈ (H₁.seq H₂).withheld w x :=
      hw₁.elim (fun h => Or.inl (Or.inl h)) fun h => absurd h hρ₁
    rw [H₁.output_of_mem _ hw₁, PMF.pure_bind, (H₁.seq H₂).output_of_mem T hw]
    rfl
  · have hw : ρ ∉ (H₁.seq H₂).withheld w x := (Honest.not_mem_withheld_seq H₁ H₂ w x ρ).2 ⟨hw₁, fun c h => by
      rw [m.free] at h
      exact h⟩
    rw [H₁.output_of_not_mem _ hw₁, PMF.bind_map, (H₁.seq H₂).output_of_not_mem T hw]
    have L : (unif (H₁.Coin × H₂.Coin)).map
          (fun c => some ((R₁.seq R₂).view T (((H₁.seq H₂).strat w x c).run ρ).1)) =
        (unif H₁.Coin).map fun c =>
          mG H₁ D m.noOrc w x ρ T c (D.kc ((H₁.strat w x c).run (Rho.fst ρ)).2.2) := by
      have e : (fun c : H₁.Coin × H₂.Coin =>
            some ((R₁.seq R₂).view T (((H₁.seq H₂).strat w x c).run ρ).1)) =
          (fun c => mG H₁ D m.noOrc w x ρ T c (D.kc ((H₁.strat w x c).run (Rho.fst ρ)).2.2)) ∘
            Prod.fst :=
        funext fun c => mG_real H₁ H₂ D m w x ρ T c
      refine (congrArg (fun f => PMF.map f (unif (H₁.Coin × H₂.Coin))) e).trans ?_
      rw [← PMF.map_comp, map_fst_unif]
    have Rr : (unif (H₁.Coin × D.Mk)).map (fun a =>
          mG H₁ D m.noOrc w x ρ T a.1 (D.put a.2 (D.kc ((H₁.strat w x a.1).run (Rho.fst ρ)).2.2))) =
        (unif H₁.Coin).bind
          ((fun o₁ : Option (View R₁) =>
              o₁.elim (PMF.pure none)
                (simCont (D.simOwn m.noOrc) x ρ T (E₁.ans ((R₁.seq R₂).given ρ T) y))) ∘
            fun c =>
              some (R₁.view (firstT R₁ R₂ ρ T)
                    ((H₁.strat w x c).run (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ)).1)) := by
      rw [map_unif_prod]
      exact congrArg _ (funext fun c => (mG_sim D m hL hA hCl x y w hR ρ hw₁ T c).symm)
    refine L.trans (Eq.trans ?_ Rr)
    refine (map_eq_of_factor _ _ ?_ (hF x y w hR _ hw₁ _ hb₁)).symm
    intro a c' hg
    have g1 : R₁.view (firstT R₁ R₂ ρ T) ((H₁.strat w x a.1).run (Rho.fst ρ)).1 =
        R₁.view (firstT R₁ R₂ ρ T) ((H₁.strat w x c').run (Rho.fst ρ)).1 :=
      congrArg (fun z => z.1) hg
    have g2 : ((H₁.strat w x a.1).run (Rho.fst ρ)).2.1 = ((H₁.strat w x c').run (Rho.fst ρ)).2.1 :=
      congrArg (fun z => z.2.1) hg
    have g3 : D.put a.2 (D.kc ((H₁.strat w x a.1).run (Rho.fst ρ)).2.2) =
        D.kc ((H₁.strat w x c').run (Rho.fst ρ)).2.2 :=
      congrArg (fun z => z.2.2) hg
    unfold mG
    rw [glue_left_congr ρ T (Strat.rho_run _ _) (Strat.rho_run _ _) g1, g2, g3]

end IOR

open IOR MaskKit

theorem exact_seq_masked : Spec.exact_seq_masked :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D m hL hA h₁ hF hCl =>
    exactWith_seq_masked D m hL hA h₁ hF hCl

theorem goodT_seq_masked : Spec.goodT_seq_masked := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂ D g₁ hF g₂
  obtain ⟨S₁, hS₁⟩ := g₁.exact
  refine (goodT_iff K X₁ X₃ E₁ E₃ (R₁.seq R₂) W₁ W₃ (H₁.seq H₂) A C
      (IOR.extSeq R₁ R₂ e₁ e₂ d) (P₁.seq P₂)).2
    ⟨goodB_seq K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂
        ((goodT_iff K X₁ X₂ E₁ E₂ R₁ W₁ W₂ H₁ A B e₁ P₁).1 g₁).1 g₂.base,
      simSeq S₁ (D.simOwn g₂.mm.noOrc),
      ?_⟩
  intro x y w hR ρ hρ T hT
  exact exactWith_seq_masked D g₂.mm g₁.isLocal g₁.acc hS₁ hF g₂.claim x y w hR ρ hρ T
    fun T₁ T₂ h1 h2 => ⟨trivial, (hT T₁ T₂ h1 h2).2⟩

theorem fresh_seq : Spec.fresh_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ Ra b₁ b₂ K₂ K₃ kc₂ kc₃ Mk _ _ put₂ put₃
    hF hB x y w hR ρ hρ T hT
  obtain ⟨-, hb₁⟩ := hT (partL T) (partR R₁.shape T) (fun _ => mem_partL) (fun _ => mem_partR)
  obtain ⟨hw₁, -⟩ := (Honest.not_mem_withheld_seq H₁ H₂ w x ρ).1 hρ
  have e := hF x y w hR _ hw₁ (firstT R₁ R₂ ρ T) hb₁
  have hg : (unif ((H₁.Coin × H₂.Coin) × Mk)).map (fun a =>
        (((H₁.seen kc₂ w x (Rho.fst ρ) (firstT R₁ R₂ ρ T) a.1.1).1,
            (H₁.seen kc₂ w x (Rho.fst ρ) (firstT R₁ R₂ ρ T) a.1.1).2.1,
            put₂ a.2 (H₁.seen kc₂ w x (Rho.fst ρ) (firstT R₁ R₂ ρ T) a.1.1).2.2),
          a.1.2)) =
      (unif (H₁.Coin × H₂.Coin)).map
        (fun c => (H₁.seen kc₂ w x (Rho.fst ρ) (firstT R₁ R₂ ρ T) c.1, c.2)) := by
    rw [← map_pair_indep (β := H₂.Coin) _ _ e]
    exact map_unif_of_equiv
      (⟨fun a => ((a.1.1, a.2), a.1.2), fun b => ((b.1.1, b.2), b.1.2),
        fun _ => rfl, fun _ => rfl⟩ : (H₁.Coin × H₂.Coin) × Mk ≃ (H₁.Coin × Mk) × H₂.Coin)
      (fun a : (H₁.Coin × Mk) × H₂.Coin =>
        (((H₁.seen kc₂ w x (Rho.fst ρ) (firstT R₁ R₂ ρ T) a.1.1).1,
            (H₁.seen kc₂ w x (Rho.fst ρ) (firstT R₁ R₂ ρ T) a.1.1).2.1,
            put₂ a.1.2 (H₁.seen kc₂ w x (Rho.fst ρ) (firstT R₁ R₂ ρ T) a.1.1).2.2),
          a.2))
  refine map_eq_of_factor (unif ((H₁.Coin × H₂.Coin) × Mk)) (unif (H₁.Coin × H₂.Coin)) ?_ hg
  rintro ⟨⟨c₁, c₂⟩, M⟩ ⟨c₁', c₂'⟩ h
  have g1 : R₁.view (firstT R₁ R₂ ρ T) ((H₁.strat w x c₁).run (Rho.fst ρ)).1 =
      R₁.view (firstT R₁ R₂ ρ T) ((H₁.strat w x c₁').run (Rho.fst ρ)).1 :=
    congrArg (fun z => z.1.1) h
  have g2 : ((H₁.strat w x c₁).run (Rho.fst ρ)).2.1 = ((H₁.strat w x c₁').run (Rho.fst ρ)).2.1 :=
    congrArg (fun z => z.1.2.1) h
  have g3 : put₂ M (kc₂ ((H₁.strat w x c₁).run (Rho.fst ρ)).2.2) =
      kc₂ ((H₁.strat w x c₁').run (Rho.fst ρ)).2.2 :=
    congrArg (fun z => z.1.2.2) h
  have g4 : c₂ = c₂' := congrArg (fun z => z.2) h
  subst g4
  obtain ⟨b1, b2, b3⟩ := hB ((H₁.strat w x c₁).run (Rho.fst ρ)).2.2
    ((H₁.strat w x c₁').run (Rho.fst ρ)).2.2 M ((H₁.strat w x c₁').run (Rho.fst ρ)).2.1 c₂
    (Rho.snd (s := R₁.shape) ρ) g3.symm
  show ((R₁.seq R₂).view T (((H₁.seq H₂).strat w x (c₁, c₂)).run ρ).1,
      (((H₁.seq H₂).strat w x (c₁, c₂)).run ρ).2.1,
      put₃ M (kc₃ (((H₁.seq H₂).strat w x (c₁, c₂)).run ρ).2.2)) =
    ((R₁.seq R₂).view T (((H₁.seq H₂).strat w x (c₁', c₂)).run ρ).1,
      (((H₁.seq H₂).strat w x (c₁', c₂)).run ρ).2.1,
      kc₃ (((H₁.seq H₂).strat w x (c₁', c₂)).run ρ).2.2)
  rw [Honest.run_seq H₁ H₂ w x (c₁, c₂) ρ, Honest.run_seq H₁ H₂ w x (c₁', c₂) ρ]
  dsimp only
  rw [g2, ← b2, ← b3]
  refine congrArg (fun v => (v, _)) ?_
  exact view_app_of_views ρ T (Strat.rho_run _ _) (Strat.rho_run _ _) (Strat.rho_run _ _)
    (Strat.rho_run _ _) g1 (congrArg _ b1.symm)

theorem fresh_snd : Spec.fresh_snd := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ Ra Rb b₁ b₂ Kc kc Mk _ _ put hA hF x y w hR ρ hρ T hT
  obtain ⟨hb₂, -⟩ := hT (partL T) (partR R₁.shape T) (fun _ => mem_partL) (fun _ => mem_partR)
  obtain ⟨hw₁, hw₂⟩ := (Honest.not_mem_withheld_seq H₁ H₂ w x ρ).1 hρ
  have re := map_unif_of_equiv (Equiv.prodAssoc H₁.Coin H₂.Coin Mk).symm
    (fun a : (H₁.Coin × H₂.Coin) × Mk =>
      (((H₁.seq H₂).seen kc w x ρ T a.1).1,
        ((H₁.seq H₂).seen kc w x ρ T a.1).2.1,
        put a.2 ((H₁.seq H₂).seen kc w x ρ T a.1).2.2))
  refine re.symm.trans ?_
  refine (map_unif_prod _).trans (Eq.trans ?_ (map_unif_prod (α := H₁.Coin) (β := H₂.Coin) _).symm)
  refine congrArg _ (funext fun c₁ => ?_)
  obtain ⟨-, hRb⟩ := hA x y w c₁ _ hR hw₁
  refine map_eq_of_factor (unif (H₂.Coin × Mk)) (unif H₂.Coin) ?_ (hF _ _ _ hRb _ (hw₂ c₁) _ hb₂)
  rintro ⟨c₂, M⟩ c₂' h
  have g1 : R₂.view (partR R₁.shape T)
        ((H₂.strat ((H₁.strat w x c₁).run (Rho.fst ρ)).2.2
            ((H₁.strat w x c₁).run (Rho.fst ρ)).2.1 c₂).run
          (Rho.snd (s := R₁.shape) ρ)).1 =
      R₂.view (partR R₁.shape T)
        ((H₂.strat ((H₁.strat w x c₁).run (Rho.fst ρ)).2.2
            ((H₁.strat w x c₁).run (Rho.fst ρ)).2.1 c₂').run
          (Rho.snd (s := R₁.shape) ρ)).1 :=
    congrArg (fun z => z.1) h
  have g2 : ((H₂.strat ((H₁.strat w x c₁).run (Rho.fst ρ)).2.2
          ((H₁.strat w x c₁).run (Rho.fst ρ)).2.1 c₂).run
        (Rho.snd (s := R₁.shape) ρ)).2.1 =
      ((H₂.strat ((H₁.strat w x c₁).run (Rho.fst ρ)).2.2
          ((H₁.strat w x c₁).run (Rho.fst ρ)).2.1 c₂').run
        (Rho.snd (s := R₁.shape) ρ)).2.1 :=
    congrArg (fun z => z.2.1) h
  have g3 : put M
        (kc ((H₂.strat ((H₁.strat w x c₁).run (Rho.fst ρ)).2.2
              ((H₁.strat w x c₁).run (Rho.fst ρ)).2.1 c₂).run
            (Rho.snd (s := R₁.shape) ρ)).2.2) =
      kc ((H₂.strat ((H₁.strat w x c₁).run (Rho.fst ρ)).2.2
            ((H₁.strat w x c₁).run (Rho.fst ρ)).2.1 c₂').run
          (Rho.snd (s := R₁.shape) ρ)).2.2 :=
    congrArg (fun z => z.2.2) h
  show ((R₁.seq R₂).view T (((H₁.seq H₂).strat w x (c₁, c₂)).run ρ).1,
      (((H₁.seq H₂).strat w x (c₁, c₂)).run ρ).2.1,
      put M (kc (((H₁.seq H₂).strat w x (c₁, c₂)).run ρ).2.2)) =
    ((R₁.seq R₂).view T (((H₁.seq H₂).strat w x (c₁, c₂')).run ρ).1,
      (((H₁.seq H₂).strat w x (c₁, c₂')).run ρ).2.1,
      kc (((H₁.seq H₂).strat w x (c₁, c₂')).run ρ).2.2)
  rw [Honest.run_seq H₁ H₂ w x (c₁, c₂) ρ, Honest.run_seq H₁ H₂ w x (c₁, c₂') ρ]
  dsimp only
  rw [g2, g3]
  refine congrArg (fun v => (v, _)) ?_
  exact view_app_of_views ρ T (Strat.rho_run _ _) (Strat.rho_run _ _) (Strat.rho_run _ _)
    (Strat.rho_run _ _) rfl g1

theorem fresh_conseq : Spec.fresh_conseq := by
  intro Xi Xo Ei Eo R Wi Wo H Ri Ri' bud bud' Kc Kc' kc g Mk _ _ put put' hR hb
    hg hF x y w hw ρ hρ T hT
  have e := congrArg (PMF.map fun z : View R × Xo × Kc => (z.1, z.2.1, g z.2.2))
    (hF x y w (hR x y w hw) ρ hρ T (hb ρ T hT))
  rw [PMF.map_comp, PMF.map_comp] at e
  refine Eq.trans (congrArg (fun f => PMF.map f (unif (H.Coin × Mk))) (funext fun a => ?_)) e
  show (_, _, put' a.2 (g _)) = (_, _, g (put a.2 _))
  rw [hg]
  rfl

theorem blind_carry : Spec.blind_carry := by
  intro Xi Xo Ei Eo R Wi Wo Wz H Kz kz Mk put w w' M x c ρ h
  have h0 : (w'.1, kz w'.2) = (w.1, put M (kz w.2)) := h
  have h1 : w'.1 = w.1 := (Prod.mk.inj h0).1
  have h2 : kz w'.2 = put M (kz w.2) := (Prod.mk.inj h0).2
  rw [Honest.carry_run, Honest.carry_run, h1]
  exact ⟨rfl, rfl, Prod.ext rfl h2⟩

end Iop
