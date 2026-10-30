-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/ToProtoProofsSeq.lean: small generic facts, most of them on a composition (`IOR.seq`,
Ior/Ior.lean) of two IORs, that are needed when the composition is turned into an IOP
(Ior/ToProto.lean):

the exact form (`Honest.ExactWith`, Ior/Honest.lean) is kept under a smaller relation and a
smaller budget; under the hypotheses of `tied_seq`, "the verifier reads all that is tied to its
positions" is kept by composition; the composed budget (`budSeq`, Ior/Honest.lean) at no further
reads; the probabilities of the withheld sets of a composition; and, for a first IOR that reads
nothing of its implicit instance and hands it on unchanged beside oracles of its own (in this
sense: `h0`, `hI`, `hA` of `mem_extReads_seq_copy`), which positions the composed verifier reads
there, and at most how many.

An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement.

Limits: on soundness this file has one thing: the theorem `Reduction.Know.congr_ext`; beyond this
theorem no statement of the file speaks of it. This file says nothing on batches.

Terms: lean/GLOSSARY.md.
-/
import Ior.ToProtoProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace Reduction
variable {A B WA WB : Type}

/-- Knowledge soundness reads the extractor only where the verifier outputs a statement and the
witness is valid. -/
theorem Know.congr_ext {K : Reduction A B} {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop}
    {ext ext' : A → Tr K.shape → WB → WA} {ε : Err K.shape} (h : K.Know on RA RB ext ε)
    (he : ∀ a τ b w, on a → K.out a τ = some b → RB b w → ext' a τ w = ext a τ w) :
    K.Know on RA RB ext' ε :=
  fun a ha =>
    Doomed.mono _ _ (fun τ hτ b w hb hw => by rw [he a τ b w ha hb hw]; exact hτ b w hb hw) (h a ha)

end Reduction

namespace IOR
variable {X₁ X₂ X₃ Xi Xo : Type} {E₁ E₂ E₃ Ei Eo E₀ Ej : ExtSpec} {W₁ W₂ W₃ Wi Wo : Type}

/-- The exact form is kept under a smaller relation and a smaller budget, with the same simulator.
-/
theorem Honest.ExactWith.mono {R : IOR Xi Ei Xo Eo} {H : R.Honest Wi Wo}
    {Ri Ri' : Xi → Ei.Str → Wi → Prop} {bud bud' : Rho R.shape → Finset (OPos R.shape) → Prop}
    {S : Honest.Sim R} (h : H.ExactWith Ri bud S) (hR : ∀ x y w, Ri' x y w → Ri x y w)
    (hb : ∀ ρ T, bud' ρ T → bud ρ T) : H.ExactWith Ri' bud' S :=
  fun x y w hw ρ hρ T hT => h x y w (hR x y w hw) ρ hρ T (hb ρ T hT)

theorem Honest.Exact.mono {R : IOR Xi Ei Xo Eo} {H : R.Honest Wi Wo}
    {Ri Ri' : Xi → Ei.Str → Wi → Prop} {bud bud' : Rho R.shape → Finset (OPos R.shape) → Prop}
    (h : H.Exact Ri bud) (hR : ∀ x y w, Ri' x y w → Ri x y w) (hb : ∀ ρ T, bud' ρ T → bud ρ T) :
    H.Exact Ri' bud' :=
  h.elim fun S hS => ⟨S, hS.mono hR hb⟩

open Classical in
/-- If all that any oracle of the first gives away (data: see `given`, Ior/Honest.lean) is read by
the first verifier, and the second verifier reads all that is tied to its positions, then the
composed verifier reads all that is tied to its positions. -/
theorem tied_seq (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
    (h₁ : ∀ ρ p, R₁.tie ρ p ⊆ R₁.extReads ρ)
    (h₂ : ∀ ρ, (R₂.reads ρ).biUnion (R₂.tie ρ) ⊆ R₂.extReads ρ) (ρ : Rho (R₁.seq R₂).shape) :
    ((R₁.seq R₂).reads ρ).biUnion ((R₁.seq R₂).tie ρ) ⊆ (R₁.seq R₂).extReads ρ := by
  intro e he
  obtain ⟨p, hp, hep⟩ := Finset.mem_biUnion.1 he
  rcases Finset.mem_union.1 hp with hp | hp
  · obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hp
    have ht : (R₁.seq R₂).tie ρ (OPos.left q) = R₁.tie (Rho.fst ρ) q := by
      show (match OPos.split (s := R₁.shape) (OPos.left (t := R₂.shape) q) with
        | .inl p => R₁.tie (Rho.fst ρ) p
        | .inr p => (R₂.tie (Rho.snd (s := R₁.shape) ρ) p).biUnion (R₁.srcE (Rho.fst ρ))
            ∪ ((R₂.tie (Rho.snd (s := R₁.shape) ρ) p).biUnion (R₁.srcO (Rho.fst ρ))).biUnion (R₁.tie (Rho.fst ρ))) = _
      rw [OPos.split_left]
    rw [ht] at hep
    exact Finset.mem_union_left _ (h₁ _ _ hep)
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    have ht : (R₁.seq R₂).tie ρ (OPos.right (s := R₁.shape) q) =
        (R₂.tie (Rho.snd (s := R₁.shape) ρ) q).biUnion (R₁.srcE (Rho.fst ρ)) ∪
          ((R₂.tie (Rho.snd (s := R₁.shape) ρ) q).biUnion (R₁.srcO (Rho.fst ρ))).biUnion
            (R₁.tie (Rho.fst ρ)) := by
      show (match OPos.split (s := R₁.shape) (OPos.right (s := R₁.shape) q) with
        | .inl p => R₁.tie (Rho.fst ρ) p
        | .inr p => (R₂.tie (Rho.snd (s := R₁.shape) ρ) p).biUnion (R₁.srcE (Rho.fst ρ))
            ∪ ((R₂.tie (Rho.snd (s := R₁.shape) ρ) p).biUnion (R₁.srcO (Rho.fst ρ))).biUnion (R₁.tie (Rho.fst ρ))) = _
      rw [OPos.split_right]
    rw [ht] at hep
    rcases Finset.mem_union.1 hep with hep | hep
    · obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.1 hep
      exact Finset.mem_union_right
        _ (Finset.mem_biUnion.2 ⟨u, h₂ _ (Finset.mem_biUnion.2 ⟨q, hq, hu⟩), heu⟩)
    · obtain ⟨u, _, heu⟩ := Finset.mem_biUnion.1 hep
      exact Finset.mem_union_left _ (h₁ _ _ heu)

open Classical in
/-- The case in which no oracle of the first gives anything away (data: see `given`,
Ior/Honest.lean). -/
theorem tied_seq_of_noTie (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃) (h₁ : ∀ ρ p, R₁.tie ρ p = ∅)
    (h₂ : ∀ ρ, (R₂.reads ρ).biUnion (R₂.tie ρ) ⊆ R₂.extReads ρ) (ρ : Rho (R₁.seq R₂).shape) :
    ((R₁.seq R₂).reads ρ).biUnion ((R₁.seq R₂).tie ρ) ⊆ (R₁.seq R₂).extReads ρ :=
  tied_seq R₁ R₂ (fun ρ p => by rw [h₁]; exact Finset.empty_subset _) h₂ ρ

open Classical in
/-- `h₂`, `ht`, `h₁` give `budSeq R₁ R₂ b₁ b₂ ρ ∅`: the composed budget at no further reads: the
second bears its verifier's positions; the first bears what the second verifier reads of its
oracles. -/
theorem budSeq_empty (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
    (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
    (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop)
    (ρ : Rho (R₁.shape ++ R₂.shape)) (h₂ : b₂ (Rho.snd (s := R₁.shape) ρ) ∅)
    (ht : (R₂.reads (Rho.snd (s := R₁.shape) ρ)).biUnion (R₂.tie (Rho.snd (s := R₁.shape) ρ)) ⊆
      R₂.extReads (Rho.snd (s := R₁.shape) ρ))
    (h₁ : b₁ (Rho.fst ρ)
      ((R₂.extReads (Rho.snd (s := R₁.shape) ρ)).biUnion (R₁.srcO (Rho.fst ρ)))) :
    budSeq R₁ R₂ b₁ b₂ ρ ∅ := by
  intro T₁ T₂ hT₁ hT₂
  have e₁ : T₁ = ∅ :=
    Finset.eq_empty_of_forall_notMem fun p hp => absurd ((hT₁ p).1 hp) (Finset.notMem_empty _)
  have e₂ : T₂ = ∅ :=
    Finset.eq_empty_of_forall_notMem fun p hp => absurd ((hT₂ p).1 hp) (Finset.notMem_empty _)
  subst e₁ e₂
  rw [given_empty R₂ _ ht, Finset.empty_union]
  exact ⟨h₂, h₁⟩

/-! ### The withheld sets of a composition -/

section Withheld
variable {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃)

theorem Honest.prRho_bad_seq_le : prRho (H₁.seq H₂).Bad ≤ prRho H₁.Bad + prRho H₂.Bad :=
  prRho_cyl_union_le _ _

/-- If the second withholds nothing that depends on its witness, then of what depends on its
witness the composition withholds what the first does. -/
theorem Honest.hid_seq_of_noHid (h : ∀ w x, H₂.Hid w x = ∅) (w : W₁) (x : X₁) :
    (H₁.seq H₂).Hid w x = Rho.cylFst R₂.shape (H₁.Hid w x) := by
  ext ρ
  constructor
  · rintro (hρ | ⟨_, c, hc⟩)
    · exact hρ
    · rw [h] at hc
      exact absurd hc (Set.notMem_empty _)
  · exact Or.inl

theorem Honest.prRho_hid_seq_of_noHid (h : ∀ w x, H₂.Hid w x = ∅) (w : W₁) (x : X₁) :
    prRho ((H₁.seq H₂).Hid w x) = prRho (H₁.Hid w x) := by
  rw [Honest.hid_seq_of_noHid H₁ H₂ h]
  exact prRho_cylFst _ _

theorem Honest.prRho_withheld_seq_le (h : ∀ w x, H₂.Hid w x = ∅) (w : W₁) (x : X₁) :
    prRho ((H₁.seq H₂).withheld w x) ≤ prRho H₁.Bad + prRho (H₁.Hid w x) + prRho H₂.Bad := by
  refine le_trans (pr_union_le _ _ _) ?_
  refine le_trans
    (add_le_add (Honest.prRho_bad_seq_le H₁ H₂)
      (le_of_eq (Honest.prRho_hid_seq_of_noHid H₁ H₂ h w x))) ?_
  rw [add_right_comm]

end Withheld

/-- The withheld set of the IOP's honest side is that of the IOR's. -/
theorem Honest.withheld_toProto {X Wt : Type} {E : ExtSpec} {R : IOR X E Unit extNone}
    (H : R.Honest Wi Unit) (ext : Wt → E.Str) (inp : Wt → X → Wi) (w : Wt) (x : X) :
    (H.toProto ext inp).withheld w x = H.withheld (inp w x) x := rfl

/-! ### What the composed verifier reads of an implicit instance that is handed on unchanged -/

section Copy
variable (F : IOR X₁ E₀ X₂ (E₀.prod Ej)) (Q : IOR X₂ (E₀.prod Ej) X₃ E₃)

/-- Under `h0`, `hI`, `hA`: the composed verifier reads in the implicit instance exactly the
positions that the second verifier reads in the part handed on. -/
theorem mem_extReads_seq_copy (h0 : ∀ ρ, F.extReads ρ = ∅) (hI : ∀ ρ p, F.srcE ρ (Sum.inl p) = {p})
    (hA : ∀ ρ q, F.srcE ρ (Sum.inr q) = ∅) (ρ : Rho (F.shape ++ Q.shape)) (p : E₀.Pos) :
    p ∈ (F.seq Q).extReads ρ ↔ Sum.inl p ∈ Q.extReads (Rho.snd (s := F.shape) ρ) := by
  classical
  show p ∈ F.extReads (Rho.fst ρ) ∪
        (Q.extReads (Rho.snd (s := F.shape) ρ)).biUnion (F.srcE (Rho.fst ρ)) ↔
    _
  rw [h0, Finset.empty_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨u, hu, hpu⟩
    cases u with
    | inl u =>
        rw [hI, Finset.mem_singleton] at hpu
        rw [hpu]
        exact hu
    | inr u =>
        rw [hA] at hpu
        exact absurd hpu (Finset.notMem_empty _)
  · intro hp
    exact ⟨Sum.inl p, hp, by rw [hI]; exact Finset.mem_singleton_self p⟩

/-- ... and so no more of them. -/
theorem card_extReads_seq_copy (h0 : ∀ ρ, F.extReads ρ = ∅) (hI : ∀ ρ p, F.srcE ρ (Sum.inl p) = {p})
    (hA : ∀ ρ q, F.srcE ρ (Sum.inr q) = ∅) (ρ : Rho (F.shape ++ Q.shape))
    [DecidablePred fun p : E₀.Pos ⊕ Ej.Pos => p.isLeft = true] :
    ((F.seq Q).extReads ρ).card ≤
      ((Q.extReads (Rho.snd (s := F.shape) ρ)).filter fun p => p.isLeft = true).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun p => (Sum.inl p : E₀.Pos ⊕ Ej.Pos)) ?_ (fun _ _ _ _ h => Sum.inl.inj h)
  intro p hp
  exact Finset.mem_coe.2
    (Finset.mem_filter.2 ⟨(mem_extReads_seq_copy F Q h0 hI hA ρ p).1 (Finset.mem_coe.1 hp), rfl⟩)

end Copy

end IOR
end Iop
