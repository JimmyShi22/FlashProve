-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/SubProofs.lean: proofs of the statements of Ior/Sub.lean, on a transformation of interactive
oracle reductions (IORs) in which the verifier draws from a subset.

Nothing is assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs.
The old shape is s; the new shape is `s.pull σ` (Iop/Pull.lean); pushed forward: taken from the new
shape to the old by `Rho.push`, `Tr.push`, `Orcs.push`.
Part 1: what Iop/PullProofs.lean does not have (the oracles pushed forward; the result of a pulled
strategy; the fibres of an injection).

Main names (statements and hypotheses: Ior/Sub.lean):
  `doomed_sub`: "the prover has lost" in the new shape.
  `know_sub`: round-by-round knowledge soundness of `R.sub σ`.
  `exact_sub`, `good_sub`: see their statements.

Limits: see Limits in the head of Ior/Sub.lean.
Terms: lean/GLOSSARY.md.
-/
import Ior.Sub
import Ior.ExactSeq
import Ior.ChainProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Tools -/

theorem Tr.read_push_orcs :
    ∀ {s : Shape} (σ : Samplers s) (τ : Tr (s.pull σ)) (p : OPos s),
      (Tr.push σ τ).read p = Orcs.push σ τ.read p
  | _ :: _, (_, _), (_, _, _), .inl _ => rfl
  | _ :: _, (_, σ), (_, _, τ), .inr p => Tr.read_push_orcs σ τ p

theorem Strat.run_pull_snd :
    ∀ {s : Shape} {β : Type} (σ : Samplers s) (S : Strat s β) (ρ : Rho (s.pull σ)),
      ((Strat.pull σ S).run ρ).2 = (S.run (Rho.push σ ρ)).2
  | [], _, _, _, _ => rfl
  | _ :: _, _, (a, σ), (_, k), (c, ρ) => Strat.run_pull_snd σ (k (a.φ c)) ρ

/-- An injection has fibres of at most one element. -/
theorem cnt_fibre_le_one {U C : Type} [Fintype U] {φ : U → C} (h : Function.Injective φ) (c : C) :
    cnt (fun a => φ a = c) ≤ 1 := by
  by_cases hc : ∃ a₀, φ a₀ = c
  · obtain ⟨a₀, rfl⟩ := hc
    rw [← cnt_eq_const a₀]
    exact cnt_mono fun a ha => h ha
  · rw [cnt_false fun a ha => hc ⟨a, ha⟩]
    exact Nat.zero_le _

/-! ## 2. "The prover has lost" -/

theorem doomed_sub : Spec.doomed_sub := by
  intro s
  induction s with
  | nil => exact fun _ _ _ _ h => h
  | cons r s ih =>
      rintro ⟨a, σ⟩ ⟨e, ε⟩ bad hσ h m
      have h1 : cnt (fun c : a.Src =>
            ¬ Doomed (Shape.pull s σ) (Err.same σ ε) fun τ => bad (m, a.φ c, Tr.push σ τ)) ≤
          cnt (fun c : a.Src => ¬ Doomed s ε fun τ => bad (m, a.φ c, τ)) :=
        cnt_mono fun c hc hd => hc (ih σ ε (fun τ => bad (m, a.φ c, τ)) hσ.2 hd)
      have h2 :=
        cnt_comp_le a.φ (cnt_fibre_le_one hσ.1) fun c => ¬ Doomed s ε fun τ => bad (m, c, τ)
      rw [Nat.mul_one] at h2
      exact h1.trans (h2.trans (h m))

/-! ## 3. The reduction, its honest side, the bundle -/

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}
  (R : IOR Xi Ei Xo Eo) (σ : Samplers R.shape)

theorem mem_reads_sub {ρ : Rho (R.shape.pull σ)} {q : OPos (R.shape.pull σ)} :
    q ∈ (R.sub σ).reads ρ ↔ OPos.pushEquiv σ q ∈ R.reads (Rho.push σ ρ) := by
  show q ∈ (R.reads (Rho.push σ ρ)).map (OPos.pushEquiv σ).symm.toEmbedding ↔ _
  rw [Finset.mem_map_equiv, Equiv.symm_symm]

theorem mem_srcO_sub {ρ : Rho (R.shape.pull σ)} {e : Eo.Pos} {q : OPos (R.shape.pull σ)} :
    q ∈ (R.sub σ).srcO ρ e ↔ OPos.pushEquiv σ q ∈ R.srcO (Rho.push σ ρ) e := by
  show q ∈ (R.srcO (Rho.push σ ρ) e).map (OPos.pushEquiv σ).symm.toEmbedding ↔ _
  rw [Finset.mem_map_equiv, Equiv.symm_symm]

theorem mem_map_push {T : Finset (OPos (R.shape.pull σ))} {q : OPos (R.shape.pull σ)} :
    OPos.pushEquiv σ q ∈ T.map (OPos.pushEquiv σ).toEmbedding ↔ q ∈ T := by
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]

/-- What the simulator is given of the implicit instance is the same. -/
theorem given_sub (ρ : Rho (R.shape.pull σ)) (T : Finset (OPos (R.shape.pull σ))) :
    (R.sub σ).given ρ T = R.given (Rho.push σ ρ) (T.map (OPos.pushEquiv σ).toEmbedding) := by
  ext p
  rw [mem_given, mem_given]
  constructor
  · rintro (h | ⟨q, hq, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨OPos.pushEquiv σ q, hq.imp (mem_reads_sub R σ).1 (mem_map_push R σ).2, h⟩
  · rintro (h | ⟨r, hr, h⟩)
    · exact Or.inl h
    · obtain ⟨q, rfl⟩ := (OPos.pushEquiv σ).surjective r
      exact Or.inr ⟨q, hr.imp (mem_reads_sub R σ).2 (mem_map_push R σ).1, h⟩

theorem shown_sub (τ : Tr (R.shape.pull σ))
    (T : Finset (OPos (R.shape.pull σ))) (q : OPos (R.shape.pull σ)) :
    (R.sub σ).Shown τ.rho T q ↔
    R.Shown (Tr.push σ τ).rho (T.map (OPos.pushEquiv σ).toEmbedding) (OPos.pushEquiv σ q) := by
  unfold Shown
  rw [Tr.rho_push]
  exact or_congr (mem_reads_sub R σ) (or_congr (mem_map_push R σ).symm Iff.rfl)

/-- What a run shows in the new shape is what the run pushed forward shows, written for the new
shape. -/
theorem view_sub (T : Finset (OPos (R.shape.pull σ))) (τ : Tr (R.shape.pull σ)) :
    (R.sub σ).view T τ =
      View.sub σ (R.view (T.map (OPos.pushEquiv σ).toEmbedding) (Tr.push σ τ)) := by
  refine View.ext' ?_ (funext fun q => ?_)
  · show τ.plains = Plains.pull σ (Tr.push σ τ).plains
    rw [Tr.plains_push, Plains.pull_push]
  · show ((R.sub σ).view T τ).orc q =
      Option.map (OSym.pull σ q)
        ((R.view (T.map (OPos.pushEquiv σ).toEmbedding) (Tr.push σ τ)).orc (OPos.pushEquiv σ q))
    by_cases h : (R.sub σ).Shown τ.rho T q
    · have e1 : ((R.sub σ).view T τ).orc q = some (τ.read q) :=
        view_orc_of_shown (R := R.sub σ) T τ h
      have e2 : (R.view (T.map (OPos.pushEquiv σ).toEmbedding) (Tr.push σ τ)).orc
            (OPos.pushEquiv σ q) =
          some ((Tr.push σ τ).read (OPos.pushEquiv σ q)) :=
        view_orc_of_shown (R := R) _ _ ((shown_sub R σ τ T q).1 h)
      rw [e2]
      refine e1.trans ?_
      show some (τ.read q) = some (OSym.pull σ q ((Tr.push σ τ).read (OPos.pushEquiv σ q)))
      rw [Tr.read_push, OSym.pull_push]
    · have e1 : ((R.sub σ).view T τ).orc q = none := view_orc_of_not_shown (R := R.sub σ) T τ h
      have e2 : (R.view (T.map (OPos.pushEquiv σ).toEmbedding) (Tr.push σ τ)).orc
            (OPos.pushEquiv σ q) = none :=
        view_orc_of_not_shown (R := R) _ _ fun h' => h ((shown_sub R σ τ T q).2 h')
      rw [e2]
      exact e1

end IOR

open IOR

theorem know_sub : Spec.know_sub := by
  intro Xi Xo Ei Eo R σ Wi Wo on RA RB ext ε hσ h a ha
  refine Doomed.mono _ _ ?_ (doomed_sub R.shape σ ε _ hσ (h a ha))
  intro τ hτ b w hb hw
  have h1 : RA a (ext a.2 (Tr.push σ τ).read w) := hτ b w hb hw
  have e : (Tr.push σ τ).read = Orcs.push σ τ.read := funext fun p => Tr.read_push_orcs σ τ p
  show RA a (ext a.2 (Orcs.push σ τ.read) w)
  rw [← e]
  exact h1

theorem isLocal_sub : Spec.isLocal_sub := by
  intro Xi Xo Ei Eo R σ h
  refine ⟨fun x y y' τ τ' hρ hpl hy hτ => ?_, fun y y' τ τ' e hρ hpl hy hτ => ?_⟩
  · refine h.out x y y' (Tr.push σ τ) (Tr.push σ τ')
      ((Tr.rho_push σ τ).trans ((congrArg (Rho.push σ) hρ).trans (Tr.rho_push σ τ').symm))
      ((Tr.plains_push σ τ).trans ((congrArg (Plains.push σ) hpl).trans (Tr.plains_push σ τ').symm))
      ?_ ?_
    · intro p hp
      rw [Tr.rho_push] at hp
      exact hy p hp
    · intro p hp
      rw [Tr.rho_push] at hp
      obtain ⟨q, rfl⟩ := (OPos.pushEquiv σ).surjective p
      rw [Tr.read_push, Tr.read_push]
      exact congrArg (OSym.push σ q) (hτ q ((mem_reads_sub R σ).2 hp))
  · refine h.imp y y' (Tr.push σ τ) (Tr.push σ τ') e
      ((Tr.rho_push σ τ).trans ((congrArg (Rho.push σ) hρ).trans (Tr.rho_push σ τ').symm))
      ((Tr.plains_push σ τ).trans ((congrArg (Plains.push σ) hpl).trans (Tr.plains_push σ τ').symm))
      ?_ ?_
    · intro p hp
      rw [Tr.rho_push] at hp
      exact hy p hp
    · intro p hp
      rw [Tr.rho_push] at hp
      obtain ⟨q, rfl⟩ := (OPos.pushEquiv σ).surjective p
      rw [Tr.read_push, Tr.read_push]
      exact congrArg (OSym.push σ q) (hτ q ((mem_srcO_sub R σ).2 hp))

theorem point_sub : Spec.point_sub := fun _ σ ⟨h⟩ => ⟨Shape.IsPoint.pull σ h⟩

theorem acc_sub : Spec.acc_sub := by
  intro Xi Xo Ei Eo R σ Wi Wo H Ri Ro hA x y w c ρ hR hρ
  have h := hA x y w c (Rho.push σ ρ) hR hρ
  have e1 := Strat.run_pull σ (H.strat w x c) ρ
  have e2 := Strat.run_pull_snd σ (H.strat w x c) ρ
  show R.out x y (Tr.push σ ((Strat.pull σ (H.strat w x c)).run ρ).1) =
      some ((Strat.pull σ (H.strat w x c)).run ρ).2.1 ∧
    Ro ((Strat.pull σ (H.strat w x c)).run ρ).2.1
      (R.imp y (Tr.push σ ((Strat.pull σ (H.strat w x c)).run ρ).1))
      ((Strat.pull σ (H.strat w x c)).run ρ).2.2
  rw [e1, e2]
  exact h

theorem exact_sub : Spec.exact_sub := by
  intro Xi Xo Ei Eo R σ Wi Wo H Ri bud S hS x y w hR ρ hρ T hT
  have h := hS x y w hR (Rho.push σ ρ) hρ (T.map (OPos.pushEquiv σ).toEmbedding) hT
  show _ = (S x (Rho.push σ ρ) (T.map (OPos.pushEquiv σ).toEmbedding)
        (Ei.ans ((R.sub σ).given ρ T) y)).map
      (Option.map (View.sub σ))
  rw [given_sub, ← h]
  by_cases hw : Rho.push σ ρ ∈ H.withheld w x
  · rw [H.output_of_mem _ hw,
      (H.sub σ).output_of_mem T (show ρ ∈ (H.sub σ).withheld w x from hw), PMF.pure_map]
    rfl
  · rw [H.output_of_not_mem _ hw,
      (H.sub σ).output_of_not_mem T (show ρ ∉ (H.sub σ).withheld w x from hw), PMF.map_comp]
    refine congrArg (fun g => PMF.map g (unif H.Coin)) (funext fun c => ?_)
    show some ((R.sub σ).view T ((Strat.pull σ (H.strat w x c)).run ρ).1) =
      some (View.sub σ
          (R.view (T.map (OPos.pushEquiv σ).toEmbedding) ((H.strat w x c).run (Rho.push σ ρ)).1))
    rw [view_sub, Strat.run_pull]

theorem good_sub : Spec.good_sub := by
  intro K Xi Xo Ei Eo R σ Wi Wo H A B ext P pBad pHid hσ hB hC g
  obtain ⟨S, hS⟩ := g.exact
  exact {
    point := point_sub _ σ g.point
    isLocal := isLocal_sub _ _ _ _ R σ g.isLocal
    acc := acc_sub _ _ _ _ R σ _ _ H _ _ g.acc
    onOut := fun a τ b ha hb => g.onOut a (Tr.push σ τ) b ha hb
    keeps := fun w x c ρ => by
      show B.core ((Strat.pull σ (H.strat w x c)).run ρ).2.2 = A.core w
      rw [Strat.run_pull_snd]
      exact g.keeps w x c _
    prBad := hB
    cover := fun w x ρ hρ => g.cover w x hρ
    prCov := hC
    know := know_sub _ _ _ _ R σ _ _ A.on A.relR B.relR ext P.err hσ g.know
    exact := ⟨simSub σ S, exact_sub _ _ _ _ R σ _ _ H A.rel P.bud S hS⟩ }

/-! ## 4. Probabilities -/

theorem pr_sub_empty : Spec.pr_sub_empty := by
  intro s σ S h
  have e : {ρ : Rho (s.pull σ) | Rho.push σ ρ ∈ S} = ∅ := Set.eq_empty_of_forall_notMem h
  rw [e]
  unfold prRho
  exact pr_empty _

theorem Rho.push_bijective : ∀ {s : Shape} (σ : Samplers s), σ.Bij → Function.Bijective (Rho.push σ)
  | [], _, _ => ⟨fun _ _ _ => rfl, fun _ => ⟨(), rfl⟩⟩
  | _ :: _, (a, σ), h => by
      obtain ⟨i, su⟩ := Rho.push_bijective σ h.2
      refine ⟨?_, ?_⟩
      · rintro ⟨c, ρ⟩ ⟨c', ρ'⟩ e
        have e1 : a.φ c = a.φ c' := congrArg Prod.fst e
        have e2 : Rho.push σ ρ = Rho.push σ ρ' := congrArg Prod.snd e
        exact Prod.ext (h.1.1 e1) (i e2)
      · rintro ⟨c, ρ⟩
        obtain ⟨c', rfl⟩ := h.1.2 c
        obtain ⟨ρ', rfl⟩ := su ρ
        exact ⟨(c', ρ'), rfl⟩

theorem pr_sub_bij : Spec.pr_sub_bij := by
  intro s σ S h
  unfold prRho
  rw [← map_unif_equiv (Equiv.ofBijective (Rho.push σ) (Rho.push_bijective σ h)), pr_map]
  rfl

namespace Rho

/-- The verifier's randomness of two restricted shapes in a row: its two parts, and back. -/
def subFst :
    {s t : Shape} → (σ : Samplers s) → (τ : Samplers t) →
    Rho ((s ++ t).pull (σ.app τ)) → Rho (s.pull σ)
  | [], _, _, _, _ => ()
  | _ :: _, _, (_, σ), τ, (c, ρ) => (c, subFst σ τ ρ)

def subSnd :
    {s t : Shape} → (σ : Samplers s) → (τ : Samplers t) →
    Rho ((s ++ t).pull (σ.app τ)) → Rho (t.pull τ)
  | [], _, _, _, ρ => ρ
  | _ :: _, _, (_, σ), τ, (_, ρ) => subSnd σ τ ρ

def subApp :
    {s t : Shape} → (σ : Samplers s) → (τ : Samplers t) →
    Rho (s.pull σ) → Rho (t.pull τ) → Rho ((s ++ t).pull (σ.app τ))
  | [], _, _, _, _, ρ₂ => ρ₂
  | _ :: _, _, (_, σ), τ, (c, ρ₁), ρ₂ => (c, subApp σ τ ρ₁ ρ₂)

theorem subFst_app :
    ∀ {s t : Shape} (σ : Samplers s) (τ : Samplers t) (ρ₁ : Rho (s.pull σ)) (ρ₂ : Rho (t.pull τ)),
      subFst σ τ (subApp σ τ ρ₁ ρ₂) = ρ₁
  | [], _, _, _, (), _ => rfl
  | _ :: _, _, (_, σ), τ, (c, ρ₁), ρ₂ => by
      show (c, subFst σ τ (subApp σ τ ρ₁ ρ₂)) = (c, ρ₁)
      rw [subFst_app σ τ ρ₁ ρ₂]

theorem subSnd_app :
    ∀ {s t : Shape} (σ : Samplers s) (τ : Samplers t) (ρ₁ : Rho (s.pull σ)) (ρ₂ : Rho (t.pull τ)),
      subSnd σ τ (subApp σ τ ρ₁ ρ₂) = ρ₂
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (_, σ), τ, (_, ρ₁), ρ₂ => subSnd_app σ τ ρ₁ ρ₂

theorem subApp_fst_snd :
    ∀ {s t : Shape} (σ : Samplers s) (τ : Samplers t) (ρ : Rho ((s ++ t).pull (σ.app τ))),
      subApp σ τ (subFst σ τ ρ) (subSnd σ τ ρ) = ρ
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, σ), τ, (c, ρ) => by
      show (c, subApp σ τ (subFst σ τ ρ) (subSnd σ τ ρ)) = (c, ρ)
      rw [subApp_fst_snd σ τ ρ]

def subEquiv {s t : Shape} (σ : Samplers s) (τ : Samplers t) :
    Rho (s.pull σ) × Rho (t.pull τ) ≃ Rho ((s ++ t).pull (σ.app τ)) where
  toFun p := subApp σ τ p.1 p.2
  invFun ρ := (subFst σ τ ρ, subSnd σ τ ρ)
  left_inv p := Prod.ext (subFst_app σ τ p.1 p.2) (subSnd_app σ τ p.1 p.2)
  right_inv ρ := subApp_fst_snd σ τ ρ

theorem fst_push :
    ∀ {s t : Shape} (σ : Samplers s) (τ : Samplers t) (ρ : Rho ((s ++ t).pull (σ.app τ))),
      Rho.fst (Rho.push (σ.app τ) ρ) = Rho.push σ (subFst σ τ ρ)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (a, σ), τ, (c, ρ) => by
      show (a.φ c, Rho.fst (Rho.push (σ.app τ) ρ)) = (a.φ c, Rho.push σ (subFst σ τ ρ))
      rw [fst_push σ τ ρ]

theorem snd_push :
    ∀ {s t : Shape} (σ : Samplers s) (τ : Samplers t) (ρ : Rho ((s ++ t).pull (σ.app τ))),
      Rho.snd (s := s) (Rho.push (σ.app τ) ρ) = Rho.push τ (subSnd σ τ ρ)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, σ), τ, (_, ρ) => snd_push σ τ ρ

end Rho

theorem pr_sub_fst : Spec.pr_sub_fst := by
  intro s t σ τ S
  unfold prRho
  rw [← map_unif_equiv (Rho.subEquiv σ τ), pr_map,
    ← map_fst_unif (C := Rho (s.pull σ)) (D := Rho (t.pull τ)), pr_map]
  congr 1
  ext p
  show Rho.fst (Rho.push (σ.app τ) (Rho.subApp σ τ p.1 p.2)) ∈ S ↔ Rho.push σ p.1 ∈ S
  rw [Rho.fst_push, Rho.subFst_app]

theorem pr_sub_snd : Spec.pr_sub_snd := by
  intro s t σ τ S
  unfold prRho
  rw [← map_unif_equiv (Rho.subEquiv σ τ), pr_map,
    ← map_snd_unif (C := Rho (s.pull σ)) (D := Rho (t.pull τ)), pr_map]
  congr 1
  ext p
  show Rho.snd (s := s) (Rho.push (σ.app τ) (Rho.subApp σ τ p.1 p.2)) ∈ S ↔ Rho.push τ p.2 ∈ S
  rw [Rho.snd_push, Rho.subSnd_app]

theorem inj_app : Spec.inj_app := by
  intro s
  induction s with
  | nil => exact fun _ _ _ _ h => h
  | cons r s ih =>
      rintro t ⟨a, σ⟩ τ h h'
      exact ⟨h.1, ih t σ τ h.2 h'⟩

theorem inj_keep : Spec.inj_keep := by
  intro s
  induction s with
  | nil => exact trivial
  | cons r s ih => exact ⟨Function.injective_id, ih⟩

theorem bij_keep : Spec.bij_keep := by
  intro s
  induction s with
  | nil => exact trivial
  | cons r s ih => exact ⟨Function.bijective_id, ih⟩

end Iop
