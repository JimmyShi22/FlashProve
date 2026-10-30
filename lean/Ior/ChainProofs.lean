-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/ChainProofs.lean: proofs of the eleven statements of Ior/Chain.lean (rules for chains of
interactive oracle reductions, IORs), each proved as it is stated there.

Main names:
  Small facts: `Reduction.Know.seq_ext`: any extractor that agrees with "the second's, then the
    first's" wherever the first verifier outputs a statement (no default value is needed).
  The probabilities of the withheld sets of a composition: `hid_seq_le`, `bad_seq_le`,
    `withheld_seq_le`.

Limits: the rules are conditional: they give no IOR that is `Good`. This file says nothing on
numbers of queries or running times. Zero knowledge of a composition is taken from
Ior/ExactSeq.lean, locality and completeness from Ior/SeqProofs.lean. (honest-verifier:
`Spec.exact_seq`: `Honest.Exact`, Ior/Honest.lean) See also Limits in the head of Ior/Chain.lean.
Terms: lean/GLOSSARY.md.
-/
import Ior.Chain
import Ior.SeqProofs
import Ior.ExactSeq

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Small facts -/

namespace ChainKit

theorem fst_read {s t : Shape} (τ : Tr (s ++ t)) : Orcs.fst τ.read = (Tr.fst τ).read :=
  funext fun p => Tr.read_left τ p

theorem snd_read {s t : Shape} (τ : Tr (s ++ t)) :
    Orcs.snd (s := s) τ.read = (Tr.snd (s := s) τ).read :=
  funext fun p => Tr.read_right τ p

theorem fst_read_app {s t : Shape} (τ₁ : Tr s) (τ₂ : Tr t) :
    Orcs.fst (Tr.app τ₁ τ₂).read = τ₁.read := by
  rw [fst_read, Tr.fst_app]

theorem snd_read_app {s t : Shape} (τ₁ : Tr s) (τ₂ : Tr t) :
    Orcs.snd (s := s) (Tr.app τ₁ τ₂).read = τ₂.read := by
  rw [snd_read, Tr.snd_app]

/-- A set of values of ρ whose members have their first part in S or their second part in the set T
that belongs to the first part: its probability is at most q + p, under `hS`, `hT`. -/
theorem prRho_le_of_fibre {s t : Shape} (S : Set (Rho s)) (U : Set (Rho (s ++ t)))
    (T : Rho s → Set (Rho t)) (q p : ℝ≥0∞) (hS : prRho S ≤ q)
    (hU : ∀ ρ ∈ U, Rho.fst ρ ∉ S → Rho.snd (s := s) ρ ∈ T (Rho.fst ρ))
    (hT : ∀ ρ₁, ρ₁ ∉ S → prRho (T ρ₁) ≤ p) : prRho U ≤ q + p := by
  classical
  have hsub : U ⊆
      Rho.cylFst t S ∪ {ρ : Rho (s ++ t) | Rho.snd (s := s) ρ ∈ T (Rho.fst ρ)} := fun ρ hρ =>
    if h : Rho.fst ρ ∈ S then Or.inl h else Or.inr (hU ρ hρ h)
  exact le_trans (pr_mono _ hsub) (le_trans (prRho_fibre_le S T p hT) (add_le_add hS le_rfl))

end ChainKit

namespace Reduction
variable {A B C WA WB WC : Type}

/-- Sequential composition with any extractor that agrees with "the second's, then the first's"
wherever the first verifier outputs a statement. (not all hypotheses are named here: see the
statement below) -/
theorem Know.seq_ext {K₁ : Reduction A B} {K₂ : Reduction B C} {on₁ : A → Prop} {on₂ : B → Prop}
    {RA : A → WA → Prop} {RB : B → WB → Prop} {RC : C → WC → Prop} {e₁ : A → Tr K₁.shape → WB → WA}
    {e₂ : B → Tr K₂.shape → WC → WB} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape}
    (h₁ : K₁.Know on₁ RA RB e₁ ε₁) (h₂ : K₂.Know on₂ RB RC e₂ ε₂)
    (hon : ∀ a τ b, on₁ a → K₁.out a τ = some b → on₂ b) (ext : A → Tr (K₁.seq K₂).shape → WC → WA)
    (he : ∀ a τ₁ τ₂ b w, K₁.out a τ₁ = some b → ext a (Tr.app τ₁ τ₂) w = e₁ a τ₁ (e₂ b τ₂ w)) :
    (K₁.seq K₂).Know on₁ RA RC ext (Err.app ε₁ ε₂) := by
  intro a ha
  refine Doomed.append K₁.shape K₂.shape ε₁ ε₂ _ (Doomed.mono _ _ ?_ (h₁ a ha))
  intro τ₁ hτ₁
  cases hout : K₁.out a τ₁ with
  | none =>
      refine Doomed.of_forall _ _ fun τ₂ c w hc _ => ?_
      rw [seq_out_app, hout] at hc
      exact absurd hc (by simp)
  | some b =>
      refine Doomed.mono _ _ ?_ (h₂ b (hon a τ₁ b ha hout))
      intro τ₂ h c w hc hw
      rw [seq_out_app, hout] at hc
      rw [he a τ₁ τ₂ b w hout]
      exact hτ₁ b _ hout (h c w hc hw)

end Reduction

open IOR ChainKit

/-! ## 2. The withheld sets of a composition -/

theorem hid_seq_le : Spec.hid_seq_le := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ w x G z₁ z₂ h₁ hG hz
  refine prRho_le_of_fibre (s := R₁.shape) (t := R₂.shape) (H₁.Hid w x) _
    (fun ρ₁ => {ρ₂ : Rho R₂.shape | ρ₁ ∉ H₁.Bad ∧ ρ₂ ∈ G ρ₁}) z₁ z₂ h₁ ?_ ?_
  · rintro ρ (hρ | ⟨hB, c, hc⟩) hH
    · exact absurd hρ hH
    · exact ⟨hB, hG _ (fun h => h.elim hB hH) c hc⟩
  · intro ρ₁ hρ₁
    by_cases hB : ρ₁ ∈ H₁.Bad
    · have e : {ρ₂ : Rho R₂.shape | ρ₁ ∉ H₁.Bad ∧ ρ₂ ∈ G ρ₁} = ∅ :=
        Set.eq_empty_of_forall_notMem fun ρ₂ h => h.1 hB
      show prRho {ρ₂ : Rho R₂.shape | ρ₁ ∉ H₁.Bad ∧ ρ₂ ∈ G ρ₁} ≤ z₂
      rw [e]
      unfold prRho
      rw [pr_empty]
      exact zero_le _
    · exact le_trans (pr_mono _ fun ρ₂ h => h.2) (hz ρ₁ fun h => h.elim hB hρ₁)

theorem bad_seq_le : Spec.bad_seq_le := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ b₁ b₂ h₁ h₂
  exact le_trans (prRho_cyl_union_le H₁.Bad H₂.Bad) (add_le_add h₁ h₂)

theorem withheld_seq_le : Spec.withheld_seq_le := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ w x G p₁ b₂ z₂ h₁ hb hG hz
  refine prRho_le_of_fibre (s := R₁.shape) (t := R₂.shape) (H₁.withheld w x) _
    (fun ρ₁ => H₂.Bad ∪ G ρ₁) p₁ (b₂ + z₂) h₁ ?_ ?_
  · rintro ρ ((hρ | hρ) | (hρ | ⟨_, c, hc⟩)) hW
    · exact absurd (Or.inl hρ) hW
    · exact Or.inl hρ
    · exact absurd (Or.inr hρ) hW
    · exact Or.inr (hG _ hW c hc)
  · intro ρ₁ hρ₁
    exact le_trans (pr_union_le _ _ _) (add_le_add hb (hz ρ₁ hρ₁))

/-! ## 3. Extractors that read oracles only -/

theorem impBy_seq : Spec.impBy_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ io₁ io₂ h₁ h₂ y (τ : Tr (R₁.shape ++ R₂.shape))
  show R₂.imp (R₁.imp y (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ) =
    io₂ (io₁ y (Orcs.fst τ.read)) (Orcs.snd (s := R₁.shape) τ.read)
  rw [fst_read, snd_read, h₁ y (Tr.fst τ), h₂ _ (Tr.snd (s := R₁.shape) τ)]

theorem extSeqO_eq : Spec.extSeqO_eq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ e₁ e₂ io d hio a τ w hs
  obtain ⟨x₂, hx⟩ := Option.isSome_iff_exists.1 hs
  show _ =
    e₁ a.2 (Orcs.fst τ.read) (e₂ (io a.2 (Orcs.fst τ.read)) (Orcs.snd (s := R₁.shape) τ.read) w)
  rw [fst_read, snd_read, ← hio a.2 (Tr.fst τ)]
  simp only [Reduction.extSeq, hx, Option.map_some]

theorem know_seq_ext : Spec.know_seq_ext := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ on₁ on₂ RA RB RC e₁ e₂ ext ε₁ ε₂ h₁ h₂ hon he a ha
  have hk : (R₁.red.seq R₂.red).Know on₁ RA RC (fun a τ w => ext a.2 τ.read w) (Err.app ε₁ ε₂) := by
    refine Reduction.Know.seq_ext h₁ h₂ hon _ ?_
    intro a τ₁ τ₂ b w hb
    obtain ⟨xo, _, rfl⟩ := Option.map_eq_some_iff.1 hb
    exact he a.2 τ₁ τ₂ w
  refine Doomed.mono _ _ ?_ (hk a ha)
  intro τ h b w hb hw
  exact h b w ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hb) hw

/-! ## 4. The bundle -/

theorem good_seq_ext : Spec.good_seq_ext := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ ext P₁ P₂ g₁ g₂ he
  exact
    { point := g₁.point.elim fun p₁ => g₂.point.elim fun p₂ => ⟨Shape.IsPoint.append p₁ p₂⟩
      isLocal := g₁.isLocal.seq g₂.isLocal
      acc := g₁.acc.seq g₂.acc
      onOut := by
        intro a τ c ha hc
        obtain ⟨b, hb, hc'⟩ := Option.bind_eq_some_iff.1 ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hc)
        exact g₂.onOut b _ c (g₁.onOut a _ b ha hb) hc'
      keeps := by
        intro w x c ρ
        rw [Honest.run_seq]
        exact (g₂.keeps _ _ _ _).trans (g₁.keeps _ _ _ _)
      prBad := le_trans (prRho_cyl_union_le H₁.Bad H₂.Bad) (add_le_add g₁.prBad g₂.prBad)
      cover := by
        rintro w x ρ (hρ | ⟨_, c, hc⟩)
        · exact Or.inl (g₁.cover w x hρ)
        · have h := g₂.cover _ _ hc
          rw [g₁.keeps] at h
          exact Or.inr h
      prCov := fun k =>
        le_trans (prRho_cyl_union_le (P₁.cov k) (P₂.cov k)) (add_le_add (g₁.prCov k) (g₂.prCov k))
      know := know_seq_ext X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ A.on B.on A.relR B.relR C.relR e₁ e₂ ext
        P₁.err P₂.err g₁.know g₂.know g₁.onOut he
      exact := exact_seq X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A.rel B.rel P₁.bud P₂.bud g₁.isLocal
        g₁.acc g₁.exact g₂.exact }

theorem good_seq : Spec.good_seq := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ io P₁ P₂ g₁ g₂ hio
  refine good_seq_ext K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂
    (extSeqO e₁ e₂ io) P₁ P₂ g₁ g₂ ?_
  intro y τ₁ τ₂ w
  show e₁ y (Orcs.fst (Tr.app τ₁ τ₂).read)
      (e₂ (io y (Orcs.fst (Tr.app τ₁ τ₂).read)) (Orcs.snd (s := R₁.shape) (Tr.app τ₁ τ₂).read) w) =
    _
  rw [fst_read_app, snd_read_app, hio y τ₁]

theorem good_seq_dec : Spec.good_seq_dec := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C d e₂ P₁ P₂ g₁ g₂
  exact good_seq_ext K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C (fun y _ _ => d y) e₂
    (fun y _ _ => d y) P₁ P₂ g₁ g₂ (fun _ _ _ _ => rfl)

theorem good_conseq : Spec.good_conseq := by
  intro K Xi Xo Ei Eo R Wi Wo H A A' B B' ext P P' g hA hB hoA hoB hrA hrB hcA hcB hP
  exact
    { point := g.point
      isLocal := g.isLocal
      acc := fun x y w c ρ hR hρ =>
        ⟨(g.acc x y w c ρ (hA x y w hR) hρ).1, hB _ _ _ (g.acc x y w c ρ (hA x y w hR) hρ).2⟩
      onOut := fun a τ b ha hb => hoB b (g.onOut a τ b (hoA a ha) hb)
      keeps := fun w x c ρ => by rw [hcA, hcB]; exact g.keeps w x c ρ
      prBad := le_trans g.prBad hP.pBad
      cover := fun w x => by rw [hP.cov, hcA]; exact g.cover w x
      prCov := fun k => by rw [hP.cov]; exact le_trans (g.prCov k) hP.pHid
      know := (g.know.conseq hoA hrA hrB).mono_err hP.err
      exact := g.exact.elim fun S hS =>
        ⟨S, fun x y w hw ρ hρ T hT => hS x y w (hA x y w hw) ρ hρ T (hP.bud ρ T hT)⟩ }

theorem good_prHid : Spec.good_prHid := by
  intro K Xi Xo Ei Eo R Wi Wo H A B ext P g x y w _
  have h : prRho (H.Hid w x) ≤ P.pHid := le_trans (pr_mono _ (g.cover w x)) (g.prCov _)
  exact ⟨h, le_trans (pr_union_le _ _ _) (add_le_add g.prBad h)⟩

end Iop
