-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/SeqProofs.lean: proofs of the first rules on interactive oracle reductions (IORs) that are run
one after the other.

Lemmas on a composition `R₁.seq R₂` (Ior/Ior.lean); proofs of four statements of Ior/Ior.lean and
Ior/Honest.lean, as they are stated there; two further statements, with proofs.
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement.

Main names:
  `seq_shape` to `mem_seq_tie_right`: what the parts of a composition are, as lemmas that hold by
    definition (`seq_shape`, `seq_out`, `seq_imp`), and which positions are in its sets of
    positions, said by membership, so that whoever uses them need not unfold the definition.
  `Honest.run_seq`, `Honest.not_mem_withheld_seq`: a run of the composed honest prover; when a value
    of the verifier's randomness is withheld.
  `isLocal_seq`: locality is kept by composition.
  `isLocal_toProto`: a local IOR to the trivial statement is a local IOP.
  `red_seq`: the reduction of a composition is the composition of the reductions (same verifier's
    output on every statement and transcript).
  `acc_seq`: pointwise completeness composes.
  `Spec.know_seq`: round-by-round knowledge soundness of a composition of IORs. If the first has it
    from RA to RB with extractor e₁ and errors ε₁ on the statements with on₁, the second from RB to
    RC with e₂, ε₂ on the statements with on₂, and on₂ holds of every statement that the first
    verifier outputs on a statement with on₁, then the composition has it from RA to RC on on₁; the
    errors are those of the first followed by those of the second; the extractor is named:
    `IOR.extSeq`.
  `Spec.sound_seq`: the same rule for round-by-round soundness (languages in place of relations; no
    on₁, on₂).

Limits: this file says nothing on zero knowledge (`Spec.exact_seq` is not proved here). It says
nothing on running times. The rules are conditional: they give no IOR that has any of these
properties. Where the first verifier rejects, the value d of the composed extractor has no meaning;
the notion asks nothing there.
Terms: lean/GLOSSARY.md.
-/
import Ior.Know
import Ior.Ior
import Ior.Honest

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR
variable {X₁ X₂ X₃ X : Type} {E₁ E₂ E₃ E : ExtSpec}

/-! ## 1. The parts of a composition -/

section Parts
variable (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)

theorem seq_shape : (R₁.seq R₂).shape = R₁.shape ++ R₂.shape := rfl

theorem seq_out (x : X₁) (y : E₁.Str) (τ : Tr (R₁.shape ++ R₂.shape)) :
    (R₁.seq R₂).out x y τ =
      (R₁.out x y (Tr.fst τ)).bind fun x₂ =>
        R₂.out x₂ (R₁.imp y (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ) := rfl

theorem seq_imp (y : E₁.Str) (τ : Tr (R₁.shape ++ R₂.shape)) :
    (R₁.seq R₂).imp y τ = R₂.imp (R₁.imp y (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ) := rfl

theorem seq_out_app (x : X₁) (y : E₁.Str) (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) :
    (R₁.seq R₂).out x y (Tr.app τ₁ τ₂) =
      (R₁.out x y τ₁).bind fun x₂ => R₂.out x₂ (R₁.imp y τ₁) τ₂ := by
  rw [seq_out, Tr.fst_app, Tr.snd_app]

theorem seq_imp_app (y : E₁.Str) (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) :
    (R₁.seq R₂).imp y (Tr.app τ₁ τ₂) = R₂.imp (R₁.imp y τ₁) τ₂ := by
  rw [seq_imp, Tr.fst_app, Tr.snd_app]

/-- The composed verifier reads in the implicit instance: what the first reads, and the sources of
what the second reads in the first's new implicit instance. -/
theorem mem_seq_extReads (ρ : Rho (R₁.shape ++ R₂.shape)) (p : E₁.Pos) :
    p ∈ (R₁.seq R₂).extReads ρ ↔
    p ∈ R₁.extReads (Rho.fst ρ) ∨
    ∃ q ∈ R₂.extReads (Rho.snd (s := R₁.shape) ρ), p ∈ R₁.srcE (Rho.fst ρ) q := by
  classical
  show p ∈ R₁.extReads (Rho.fst ρ) ∪
        (R₂.extReads (Rho.snd (s := R₁.shape) ρ)).biUnion (R₁.srcE (Rho.fst ρ)) ↔
    _
  rw [Finset.mem_union, Finset.mem_biUnion]

/-- At a position of the first part the composed verifier reads: what the first reads, and the
sources of what the second reads in the first's new implicit instance. -/
theorem left_mem_seq_reads (ρ : Rho (R₁.shape ++ R₂.shape)) (p : OPos R₁.shape) :
    OPos.left p ∈ (R₁.seq R₂).reads ρ ↔
    p ∈ R₁.reads (Rho.fst ρ) ∨
    ∃ q ∈ R₂.extReads (Rho.snd (s := R₁.shape) ρ), p ∈ R₁.srcO (Rho.fst ρ) q := by
  classical
  show OPos.left p ∈
      (R₁.reads (Rho.fst ρ) ∪
            (R₂.extReads (Rho.snd (s := R₁.shape) ρ)).biUnion (R₁.srcO (Rho.fst ρ))).image
          OPos.left ∪
        (R₂.reads (Rho.snd (s := R₁.shape) ρ)).image (OPos.right (s := R₁.shape)) ↔
    _
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨p', hp', he⟩ | ⟨p', _, he⟩)
    · rw [OPos.left_injective he, Finset.mem_union, Finset.mem_biUnion] at hp'
      exact hp'
    · exact absurd he.symm (OPos.left_ne_right p p')
  · intro h
    exact Or.inl ⟨p, by rw [Finset.mem_union, Finset.mem_biUnion]; exact h, rfl⟩

/-- At a position of the second part the composed verifier reads what the second reads. -/
theorem right_mem_seq_reads (ρ : Rho (R₁.shape ++ R₂.shape)) (p : OPos R₂.shape) :
    OPos.right (s := R₁.shape) p ∈ (R₁.seq R₂).reads ρ ↔
    p ∈ R₂.reads (Rho.snd (s := R₁.shape) ρ) := by
  classical
  show OPos.right (s := R₁.shape) p ∈
      (R₁.reads (Rho.fst ρ) ∪
            (R₂.extReads (Rho.snd (s := R₁.shape) ρ)).biUnion (R₁.srcO (Rho.fst ρ))).image
          OPos.left ∪
        (R₂.reads (Rho.snd (s := R₁.shape) ρ)).image (OPos.right (s := R₁.shape)) ↔
    _
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨p', _, he⟩ | ⟨p', hp', he⟩)
    · exact absurd he (OPos.left_ne_right p' p)
    · rw [OPos.right_injective he] at hp'
      exact hp'
  · intro h
    exact Or.inr ⟨p, h, rfl⟩

theorem mem_seq_srcE (ρ : Rho (R₁.shape ++ R₂.shape)) (q : E₃.Pos) (p : E₁.Pos) :
    p ∈ (R₁.seq R₂).srcE ρ q ↔
    ∃ q' ∈ R₂.srcE (Rho.snd (s := R₁.shape) ρ) q, p ∈ R₁.srcE (Rho.fst ρ) q' := by
  classical
  show p ∈ (R₂.srcE (Rho.snd (s := R₁.shape) ρ) q).biUnion (R₁.srcE (Rho.fst ρ)) ↔ _
  rw [Finset.mem_biUnion]

theorem left_mem_seq_srcO (ρ : Rho (R₁.shape ++ R₂.shape)) (q : E₃.Pos) (p : OPos R₁.shape) :
    OPos.left p ∈ (R₁.seq R₂).srcO ρ q ↔
    ∃ q' ∈ R₂.srcE (Rho.snd (s := R₁.shape) ρ) q, p ∈ R₁.srcO (Rho.fst ρ) q' := by
  classical
  show OPos.left p ∈
      ((R₂.srcE (Rho.snd (s := R₁.shape) ρ) q).biUnion (R₁.srcO (Rho.fst ρ))).image OPos.left ∪
        (R₂.srcO (Rho.snd (s := R₁.shape) ρ) q).image (OPos.right (s := R₁.shape)) ↔
    _
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨p', hp', he⟩ | ⟨p', _, he⟩)
    · rw [OPos.left_injective he, Finset.mem_biUnion] at hp'
      exact hp'
    · exact absurd he.symm (OPos.left_ne_right p p')
  · intro h
    exact Or.inl ⟨p, by rw [Finset.mem_biUnion]; exact h, rfl⟩

theorem right_mem_seq_srcO (ρ : Rho (R₁.shape ++ R₂.shape)) (q : E₃.Pos) (p : OPos R₂.shape) :
    OPos.right (s := R₁.shape) p ∈ (R₁.seq R₂).srcO ρ q ↔
    p ∈ R₂.srcO (Rho.snd (s := R₁.shape) ρ) q := by
  classical
  show OPos.right (s := R₁.shape) p ∈
      ((R₂.srcE (Rho.snd (s := R₁.shape) ρ) q).biUnion (R₁.srcO (Rho.fst ρ))).image OPos.left ∪
        (R₂.srcO (Rho.snd (s := R₁.shape) ρ) q).image (OPos.right (s := R₁.shape)) ↔
    _
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨p', _, he⟩ | ⟨p', hp', he⟩)
    · exact absurd he (OPos.left_ne_right p' p)
    · rw [OPos.right_injective he] at hp'
      exact hp'
  · intro h
    exact Or.inr ⟨p, h, rfl⟩

theorem seq_blinded_left (p : OPos R₁.shape) :
    (R₁.seq R₂).blinded (OPos.left p) = R₁.blinded p := by
  show (match OPos.split (s := R₁.shape) (OPos.left (t := R₂.shape) p) with
    | .inl p => R₁.blinded p
    | .inr p => R₂.blinded p) = _
  rw [OPos.split_left]

theorem seq_blinded_right (p : OPos R₂.shape) :
    (R₁.seq R₂).blinded (OPos.right (s := R₁.shape) p) = R₂.blinded p := by
  show (match OPos.split (s := R₁.shape) (OPos.right (s := R₁.shape) p) with
    | .inl p => R₁.blinded p
    | .inr p => R₂.blinded p) = _
  rw [OPos.split_right]

theorem seq_tie_left (ρ : Rho (R₁.shape ++ R₂.shape)) (p : OPos R₁.shape) :
    (R₁.seq R₂).tie ρ (OPos.left p) = R₁.tie (Rho.fst ρ) p := by
  classical
  show (match OPos.split (s := R₁.shape) (OPos.left (t := R₂.shape) p) with
    | .inl p => R₁.tie (Rho.fst ρ) p
    | .inr p => (R₂.tie (Rho.snd (s := R₁.shape) ρ) p).biUnion (R₁.srcE (Rho.fst ρ))
        ∪ ((R₂.tie (Rho.snd (s := R₁.shape) ρ) p).biUnion (R₁.srcO (Rho.fst ρ))).biUnion (R₁.tie (Rho.fst ρ))) = _
  rw [OPos.split_left]

/-- What a symbol of the second prover's oracle gives away of the first implicit instance: the
sources of what it gives away of the middle one, and what the first prover's symbols among those
sources give away. (data: see `given`, Ior/Honest.lean) -/
theorem mem_seq_tie_right (ρ : Rho (R₁.shape ++ R₂.shape)) (p : OPos R₂.shape) (u : E₁.Pos) :
    u ∈ (R₁.seq R₂).tie ρ (OPos.right (s := R₁.shape) p) ↔
    ∃ q ∈ R₂.tie (Rho.snd (s := R₁.shape) ρ) p,
      u ∈ R₁.srcE (Rho.fst ρ) q ∨ ∃ p₁ ∈ R₁.srcO (Rho.fst ρ) q, u ∈ R₁.tie (Rho.fst ρ) p₁ := by
  classical
  show u ∈ (match OPos.split (s := R₁.shape) (OPos.right (s := R₁.shape) p) with
    | .inl p => R₁.tie (Rho.fst ρ) p
    | .inr p => (R₂.tie (Rho.snd (s := R₁.shape) ρ) p).biUnion (R₁.srcE (Rho.fst ρ))
        ∪ ((R₂.tie (Rho.snd (s := R₁.shape) ρ) p).biUnion (R₁.srcO (Rho.fst ρ))).biUnion (R₁.tie (Rho.fst ρ))) ↔ _
  rw [OPos.split_right]
  simp only [Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (⟨q, hq, hu⟩ | ⟨p₁, ⟨q, hq, hp₁⟩, hu⟩)
    · exact ⟨q, hq, Or.inl hu⟩
    · exact ⟨q, hq, Or.inr ⟨p₁, hp₁, hu⟩⟩
  · rintro ⟨q, hq, hu | ⟨p₁, hp₁, hu⟩⟩
    · exact Or.inl ⟨q, hq, hu⟩
    · exact Or.inr ⟨p₁, ⟨q, hq, hp₁⟩, hu⟩

end Parts

/-! ## 2. Locality -/

/-- For a local R₁: if two implicit instances and two transcripts that begin with the rounds of R₁,
with the same verifier messages and plain parts, agree on the sources of a set U of positions of
R₁'s new implicit instance, the two new implicit instances agree on U. -/
theorem IsLocal.imp_fst {R₁ : IOR X₁ E₁ X₂ E₂} (h₁ : R₁.IsLocal) {t : Shape} (y y' : E₁.Str)
    (τ τ' : Tr (R₁.shape ++ t)) (U : E₂.Pos → Prop) (hρ : τ.rho = τ'.rho)
    (hπ : τ.plains = τ'.plains)
    (hE : ∀ q, U q → ∀ p ∈ R₁.srcE (Rho.fst τ.rho) q, E₁.rd y p = E₁.rd y' p)
    (hO : ∀ q,
      U q → ∀ p ∈ R₁.srcO (Rho.fst τ.rho) q, τ.read (OPos.left p) = τ'.read (OPos.left p)) :
    ∀ q, U q → E₂.rd (R₁.imp y (Tr.fst τ)) q = E₂.rd (R₁.imp y' (Tr.fst τ')) q := by
  intro q hq
  refine h₁.imp y y' _ _ q (by rw [Tr.rho_fst, Tr.rho_fst, hρ])
    (by rw [Tr.plains_fst, Tr.plains_fst, hπ]) ?_ ?_
  · intro p hp
    rw [Tr.rho_fst] at hp
    exact hE q hq p hp
  · intro p hp
    rw [Tr.rho_fst] at hp
    exact (Tr.read_left_eq_iff τ τ' p).1 (hO q hq p hp)

theorem IsLocal.seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃}
    (h₁ : R₁.IsLocal) (h₂ : R₂.IsLocal) : (R₁.seq R₂).IsLocal where
  out := by
    intro x y y' (τ : Tr (R₁.shape ++ R₂.shape)) (τ' : Tr (R₁.shape ++ R₂.shape))
      (hρ : Tr.rho (s := R₁.shape ++ R₂.shape) τ = Tr.rho τ')
      (hπ : Tr.plains (s := R₁.shape ++ R₂.shape) τ = Tr.plains τ') hE hO
    have e₁ : R₁.out x y (Tr.fst τ) = R₁.out x y' (Tr.fst τ') := by
      refine h₁.out x y y' _ _ (by rw [Tr.rho_fst, Tr.rho_fst, hρ])
        (by rw [Tr.plains_fst, Tr.plains_fst, hπ]) ?_ ?_
      · intro p hp
        rw [Tr.rho_fst] at hp
        exact hE p ((mem_seq_extReads R₁ R₂ _ p).2 (Or.inl hp))
      · intro p hp
        rw [Tr.rho_fst] at hp
        exact (Tr.read_left_eq_iff τ τ' p).1 (hO _ ((left_mem_seq_reads R₁ R₂ _ p).2 (Or.inl hp)))
    have e₂ : ∀ x₂, R₂.out x₂ (R₁.imp y (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ) =
        R₂.out x₂ (R₁.imp y' (Tr.fst τ')) (Tr.snd (s := R₁.shape) τ') := by
      intro x₂
      refine h₂.out x₂ _ _ _ _ (by rw [Tr.rho_snd, Tr.rho_snd, hρ])
        (by rw [Tr.plains_snd, Tr.plains_snd, hπ]) ?_ ?_
      · rw [Tr.rho_snd]
        exact h₁.imp_fst y y' τ τ' (· ∈ R₂.extReads (Rho.snd (s := R₁.shape) τ.rho)) hρ hπ
          (fun q hq p hp => hE p ((mem_seq_extReads R₁ R₂ _ p).2 (Or.inr ⟨q, hq, hp⟩)))
          (fun q hq p hp => hO _ ((left_mem_seq_reads R₁ R₂ _ p).2 (Or.inr ⟨q, hq, hp⟩)))
      · intro p hp
        rw [Tr.rho_snd] at hp
        exact (Tr.read_right_eq_iff τ τ' p).1 (hO _ ((right_mem_seq_reads R₁ R₂ _ p).2 hp))
    rw [seq_out, seq_out, e₁]
    exact congrArg _ (funext e₂)
  imp := by
    intro y y' (τ : Tr (R₁.shape ++ R₂.shape)) (τ' : Tr (R₁.shape ++ R₂.shape)) q
      (hρ : Tr.rho (s := R₁.shape ++ R₂.shape) τ = Tr.rho τ')
      (hπ : Tr.plains (s := R₁.shape ++ R₂.shape) τ = Tr.plains τ') hE hO
    rw [seq_imp, seq_imp]
    refine h₂.imp _ _ _ _ q (by rw [Tr.rho_snd, Tr.rho_snd, hρ])
      (by rw [Tr.plains_snd, Tr.plains_snd, hπ]) ?_ ?_
    · rw [Tr.rho_snd]
      exact h₁.imp_fst y y' τ τ' (· ∈ R₂.srcE (Rho.snd (s := R₁.shape) τ.rho) q) hρ hπ
        (fun q' hq' p hp => hE p ((mem_seq_srcE R₁ R₂ _ q p).2 ⟨q', hq', hp⟩))
        (fun q' hq' p hp => hO _ ((left_mem_seq_srcO R₁ R₂ _ q p).2 ⟨q', hq', hp⟩))
    · intro p hp
      rw [Tr.rho_snd] at hp
      exact (Tr.read_right_eq_iff τ τ' p).1 (hO _ ((right_mem_seq_srcO R₁ R₂ _ q p).2 hp))

theorem IsLocal.toProto {R : IOR X E Unit extNone} (h : R.IsLocal) : R.toInteractiveOracleProof.IsLocal :=
  fun x y y' τ τ' hρ hπ hE hO => congrArg Option.isSome (h.out x y y' τ τ' hρ hπ hE hO)

/-! ## 3. The reduction of a composition -/

theorem red_seq_out (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
    (a : X₁ × E₁.Str) (τ : Tr (R₁.shape ++ R₂.shape)) :
    (R₁.seq R₂).red.out a τ = (R₁.red.seq R₂.red).out a τ := by
  show ((R₁.out a.1 a.2 (Tr.fst τ)).bind fun x₂ =>
        R₂.out x₂ (R₁.imp a.2 (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ)).map
      (fun xo => (xo, R₂.imp (R₁.imp a.2 (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ))) =
    ((R₁.out a.1 a.2 (Tr.fst τ)).map fun xo => (xo, R₁.imp a.2 (Tr.fst τ))).bind fun b =>
      (R₂.out b.1 b.2 (Tr.snd (s := R₁.shape) τ)).map fun xo =>
        (xo, R₂.imp b.2 (Tr.snd (s := R₁.shape) τ))
  cases R₁.out a.1 a.2 (Tr.fst τ) <;> rfl

/-- The extractor of a composition of IORs: that of the second on the second part of the transcript,
then that of the first on the first part. Where the first verifier rejects: d. -/
def extSeq {W₁ W₂ W₃ : Type} (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
    (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂) (d : W₁) :
    X₁ × E₁.Str → Tr (R₁.seq R₂).red.shape → W₃ → W₁ :=
  Reduction.extSeq R₁.red R₂.red e₁ e₂ d

/-- The composed extractor where the first verifier outputs x₂. -/
theorem extSeq_app {W₁ W₂ W₃ : Type} (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
    (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂) (d : W₁)
    (a : X₁ × E₁.Str) (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) (x₂ : X₂) (w : W₃)
    (h : R₁.out a.1 a.2 τ₁ = some x₂) :
    extSeq R₁ R₂ e₁ e₂ d a (Tr.app τ₁ τ₂) w = e₁ a τ₁ (e₂ (x₂, R₁.imp a.2 τ₁) τ₂ w) := by
  simp only [extSeq, Reduction.extSeq, Tr.fst_app, Tr.snd_app, h, Option.map_some]

/-! ## 4. The honest side of a composition -/

namespace Honest
variable {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {W₁ W₂ W₃ : Type}

/-- A run of the composed honest prover: the run of the first on the first part of ρ, then the run
of the second, on what the first ends with, on the second part. -/
theorem run_seq (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (w : W₁) (x : X₁)
    (c : H₁.Coin × H₂.Coin) (ρ : Rho (R₁.shape ++ R₂.shape)) :
    ((H₁.seq H₂).strat w x c).run ρ =
      (Tr.app ((H₁.strat w x c.1).run (Rho.fst ρ)).1
          ((H₂.strat ((H₁.strat w x c.1).run (Rho.fst ρ)).2.2
              ((H₁.strat w x c.1).run (Rho.fst ρ)).2.1 c.2).run
            (Rho.snd (s := R₁.shape) ρ)).1,
        ((H₂.strat ((H₁.strat w x c.1).run (Rho.fst ρ)).2.2
            ((H₁.strat w x c.1).run (Rho.fst ρ)).2.1 c.2).run
          (Rho.snd (s := R₁.shape) ρ)).2) :=
  Strat.run_bind (H₁.strat w x c.1) (fun o => H₂.strat o.2 o.1 c.2) ρ

/-- What "not withheld by the composition" says: the first part is not withheld by the first, and
the second part is not withheld by the second on what the first hands on, whatever the coins of the
first. -/
theorem not_mem_withheld_seq (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (w : W₁)
    (x : X₁) (ρ : Rho (R₁.shape ++ R₂.shape)) :
    ρ ∉ (H₁.seq H₂).withheld w x ↔
    Rho.fst ρ ∉ H₁.withheld w x ∧
    ∀ c, Rho.snd (s := R₁.shape) ρ ∉
      H₂.withheld ((H₁.strat w x c).run (Rho.fst ρ)).2.2
        ((H₁.strat w x c).run (Rho.fst ρ)).2.1 := by
  show ¬ ((Rho.fst ρ ∈ H₁.Bad ∨ Rho.snd (s := R₁.shape) ρ ∈ H₂.Bad) ∨
      (Rho.fst ρ ∈ H₁.Hid w x ∨
        (Rho.fst ρ ∉ H₁.Bad ∧
          ∃ c, Rho.snd (s := R₁.shape) ρ ∈
            H₂.Hid ((H₁.strat w x c).run (Rho.fst ρ)).2.2
              ((H₁.strat w x c).run (Rho.fst ρ)).2.1))) ↔
    ¬ (Rho.fst ρ ∈ H₁.Bad ∨ Rho.fst ρ ∈ H₁.Hid w x) ∧
      ∀ c,
        ¬ (Rho.snd (s := R₁.shape) ρ ∈ H₂.Bad ∨
        Rho.snd (s := R₁.shape) ρ ∈
          H₂.Hid ((H₁.strat w x c).run (Rho.fst ρ)).2.2 ((H₁.strat w x c).run (Rho.fst ρ)).2.1)
  constructor
  · intro h
    exact ⟨fun h' => h (h'.elim (fun a => Or.inl (Or.inl a)) fun a => Or.inr (Or.inl a)),
      fun c h' =>
        h (h'.elim (fun a => Or.inl (Or.inr a)) fun a =>
            Or.inr (Or.inr ⟨fun b => h (Or.inl (Or.inl b)), c, a⟩))⟩
  · rintro ⟨h, h'⟩ ((a | a) | (a | ⟨_, c, a⟩))
    · exact h (Or.inl a)
    · exact h' (Classical.arbitrary _) (Or.inl a)
    · exact h (Or.inr a)
    · exact h' c (Or.inr a)

theorem Acc.seq {H₁ : R₁.Honest W₁ W₂} {H₂ : R₂.Honest W₂ W₃}
    {Ra : X₁ → E₁.Str → W₁ → Prop} {Rb : X₂ → E₂.Str → W₂ → Prop}
    {Rc : X₃ → E₃.Str → W₃ → Prop} (h₁ : H₁.Acc Ra Rb) (h₂ : H₂.Acc Rb Rc) :
    (H₁.seq H₂).Acc Ra Rc := by
  intro x y w c ρ hR hρ
  obtain ⟨hρ₁, hρ₂⟩ := (not_mem_withheld_seq H₁ H₂ w x ρ).1 hρ
  obtain ⟨ho₁, hb⟩ := h₁ x y w c.1 (Rho.fst ρ) hR hρ₁
  obtain ⟨ho₂, hc⟩ := h₂ _ _ _ c.2 (Rho.snd (s := R₁.shape) ρ) hb (hρ₂ c.1)
  rw [run_seq]
  refine ⟨?_, ?_⟩
  · show (R₁.seq R₂).out x y (Tr.app _ _) = _
    rw [seq_out_app, ho₁]
    exact ho₂
  · show Rc _ ((R₁.seq R₂).imp y (Tr.app _ _)) _
    rw [seq_imp_app]
    exact hc

end Honest
end IOR

/-! ## 5. The statements -/

namespace Spec
open IOR

/-- Round-by-round knowledge soundness of a composition of IORs: errors concatenated, extractors
composed. -/
def know_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (on₁ : X₁ × E₁.Str → Prop) (on₂ : X₂ × E₂.Str → Prop)
      (RA : X₁ × E₁.Str → W₁ → Prop) (RB : X₂ × E₂.Str → W₂ → Prop) (RC : X₃ × E₃.Str → W₃ → Prop)
      (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
      (ε₁ : Err R₁.shape) (ε₂ : Err R₂.shape) (d : W₁),
    R₁.red.Know on₁ RA RB e₁ ε₁ → R₂.red.Know on₂ RB RC e₂ ε₂ →
    (∀ a τ b, on₁ a → R₁.red.out a τ = some b → on₂ b) →
    (R₁.seq R₂).red.Know on₁ RA RC (IOR.extSeq R₁ R₂ e₁ e₂ d) (Err.app ε₁ ε₂)

/-- Round-by-round soundness of a composition of IORs: errors concatenated. -/
def sound_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (LA : X₁ × E₁.Str → Prop) (LB : X₂ × E₂.Str → Prop) (LC : X₃ × E₃.Str → Prop)
      (ε₁ : Err R₁.shape) (ε₂ : Err R₂.shape),
    R₁.red.Sound LA LB ε₁ → R₂.red.Sound LB LC ε₂ → (R₁.seq R₂).red.Sound LA LC (Err.app ε₁ ε₂)

end Spec

theorem isLocal_seq : Spec.isLocal_seq := fun _ _ _ _ _ _ _ _ h₁ h₂ => h₁.seq h₂

theorem isLocal_toProto : Spec.isLocal_toProto := fun _ _ _ h => h.toProto

theorem red_seq : Spec.red_seq := fun _ _ _ _ _ _ R₁ R₂ a τ => IOR.red_seq_out R₁ R₂ a τ

theorem acc_seq : Spec.acc_seq := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ => h₁.seq h₂

theorem know_seq : Spec.know_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ on₁ on₂ RA RB RC e₁ e₂ ε₁ ε₂ d h₁ h₂ hon a ha
  refine Doomed.mono _ _ ?_ (Reduction.Know.seq h₁ h₂ hon d a ha)
  intro τ h b w hb hw
  exact h b w ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hb) hw

theorem sound_seq : Spec.sound_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ LA LB LC ε₁ ε₂ h₁ h₂ a ha
  refine Doomed.mono _ _ ?_ (Reduction.Sound.seq h₁ h₂ a ha)
  intro τ h b hb
  exact h b ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hb)

end Iop
