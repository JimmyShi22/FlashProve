-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/FitOfOpens.lean: how many positions a verifier opens, compositionally.

Definitions, statements (in `Iop.Spec`) and proofs. Generic: no protocol occurs.
This is book-keeping for the compiler: a compiled proof opens, in hash trees, the oracle positions
that the verifier reads, and a bound on their number is announced in advance. "The implicit
instance" is the implicit part of a statement of an interactive oracle reduction (`IOR`,
Ior/Ior.lean).
The compiler asks for a number "the verifier opens at most so many positions, in the prover's
oracles and in the external oracles together" (`Iop.BatchProtocol.Opens`). The verifier of "R₁; then R₂"
(`IOR.seq`) opens its own positions of R₁, its own positions of R₂ in the oracles of R₂, and, for
each position that R₂ reads in the middle implicit instance, the positions of R₁'s oracles and of
the first implicit instance from which that symbol is computed (`srcO`, `srcE`).

Main names:
  `IOR.OpensLe R o`, with four numbers `o : OpenB`: for every ρ and every finite set U of positions
    of the new implicit instance (the queries of whoever comes later):
      `tot`: the verifier's own positions and all sources of U, in the prover's oracles and in the
        implicit instance together, number at most n + bl · |U|;
      `ext`: those of them in the implicit instance number at most nE + bE · |U|.
  `opensLe_seq`: the rule: R₁.OpensLe a → R₂.OpensLe b → (R₁.seq R₂).OpensLe (a.seq b).

Why sets U and not a bound for each position in each kind of oracle: where the new implicit instance
is "the old one, unchanged, beside oracles sent", a later query costs one position, in the one kind
or in the other. Two separate bounds would be 1 and 1, and a chain of k such steps would count k
positions for a query. Here bl = 1, and the numbers of a chain of such steps add up:
`(OpenB.seq a b).n = a.n + b.n` if `a.bl ≤ 1`.

Notation: `ρ`, of type `Rho R.shape` (Iop/Shape.lean): the verifier's randomness of a whole
execution; `reads`, `extReads` (Ior/Ior.lean): the positions that the verifier reads in the prover's
oracles, and in the implicit instance; `srcO`, `srcE` (Ior/Ior.lean): from which symbols a symbol of
the new implicit instance is computed; of the four numbers of `OpenB`: `n`: own positions, in the
prover's oracles and the implicit instance together; `nE`: own positions in the implicit instance;
`bl`: positions for one query to the new implicit instance; `bE`: of these, in the implicit
instance.

Limits: the numbers are upper bounds; nothing says that they are attained. Who reads what: on the
way to the compiler's side conditions only n of the whole chain is read;
nE and bE serve the rule for n alone. In the middle of a chain "the implicit instance" holds all
oracles that earlier steps left, so nE of a chain is not the number of positions read in the encoded
index. The compiler's condition on reads of an encoded index (Compile/Spec.lean: `Budget`) reads the
numbers qT, qpar, qch, qon and b of `LH.Nums`.
It reads none of the four numbers here. For a first
step with bl > 1 (a fold) the rule charges bl for each position that the second reads in the middle
instance and 1 for each that it reads in its own oracles; that is exact only if the sources of
distinct positions are disjoint.

Terms: lean/GLOSSARY.md.
-/
import Ior.Batch
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace Iop

/-- The numbers of openings of an IOR. -/
structure OpenB where
  /-- own positions, in the prover's oracles and the implicit instance together -/
  n  : ℕ
  /-- own positions in the implicit instance -/
  nE : ℕ
  /-- positions for one query to the new implicit instance -/
  bl : ℕ
  /-- of these, in the implicit instance -/
  bE : ℕ

/-- The numbers of "the first, then the second". -/
def OpenB.seq (a b : OpenB) : OpenB where
  n  := a.n + b.n + (a.bl - 1) * b.nE
  nE := a.nE + a.bE * b.nE
  bl := b.bl + (a.bl - 1) * b.bE
  bE := a.bE * b.bE

/-- Where a later query to what the first leaves costs at most one position, the numbers add up. -/
theorem OpenB.seq_n_of_le_one {a b : OpenB} (h : a.bl ≤ 1) :
    (a.seq b).n = a.n + b.n ∧ (a.seq b).bl = b.bl := by
  have h0 : a.bl - 1 = 0 := by omega
  exact ⟨by simp [OpenB.seq, h0], by simp [OpenB.seq, h0]⟩

namespace IOR
variable {X₁ X₂ X₃ Xi Xo X : Type} {E₁ E₂ E₃ Ei Eo E : ExtSpec}

open Classical in
/-- The bound on openings, with the four numbers o. The head tells its two clauses in words. -/
structure OpensLe (R : IOR Xi Ei Xo Eo) (o : OpenB) : Prop where
  tot : ∀ (ρ : Rho R.shape) (U : Finset Eo.Pos), (R.reads ρ ∪ U.biUnion (R.srcO ρ)).card +
      (R.extReads ρ ∪ U.biUnion (R.srcE ρ)).card ≤
    o.n + o.bl * U.card
  ext : ∀ (ρ : Rho R.shape) (U : Finset Eo.Pos),
    (R.extReads ρ ∪ U.biUnion (R.srcE ρ)).card ≤ o.nE + o.bE * U.card

end IOR

namespace Spec
open IOR

/-- How a block shows `OpensLe`. -/
def opensLe_of_bounds : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (o : OpenB),
    (∀ ρ, (R.reads ρ).card + (R.extReads ρ).card ≤ o.n) → (∀ ρ, (R.extReads ρ).card ≤ o.nE) →
    (∀ ρ q, (R.srcO ρ q).card + (R.srcE ρ q).card ≤ o.bl) →
    (∀ ρ q, (R.srcE ρ q).card ≤ o.bE) → R.OpensLe o

/-- States `OpensLe` at ⟨n, 0, k, 1⟩, for 1 ≤ k, of a preamble in the sense of the parameter lists
(Hiop/RecSubs.lean: `noReads`, `srcIdx`, `srcAux`) that reads at most n positions of the prover's
oracles: it reads nothing of the implicit instance; the new implicit instance is the old one,
unchanged, beside oracles each symbol of which is computed from at most k symbols that the prover
sent. At k = 1 a later query costs one position. -/
def opensLe_copy : Prop :=
  ∀ (X Xl : Type) (E0 Ej : ExtSpec) (F : IOR X E0 Xl (E0.prod Ej)) (n k : ℕ), 1 ≤ k →
    (∀ ρ, F.extReads ρ = ∅) → (∀ ρ p, F.srcE ρ (Sum.inl p) = {p} ∧ F.srcO ρ (Sum.inl p) = ∅) →
    (∀ ρ q, F.srcE ρ (Sum.inr q) = ∅) → (∀ ρ, (F.reads ρ).card ≤ n) →
    (∀ ρ q, (F.srcO ρ (Sum.inr q)).card ≤ k) → F.OpensLe ⟨n, 0, k, 1⟩

/-- The rule for "R₁; then R₂". -/
def opensLe_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (a b : OpenB),
    R₁.OpensLe a → R₂.OpensLe b → (R₁.seq R₂).OpensLe (a.seq b)

/-- States that larger numbers are weaker. -/
def opensLe_mono : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (o o' : OpenB),
    o.n ≤ o'.n → o.nE ≤ o'.nE → o.bl ≤ o'.bl → o.bE ≤ o'.bE → R.OpensLe o → R.OpensLe o'

/-- States, for an R at the end of a chain with `R.OpensLe o`: o.n is a number such as the compiler
asks for, and o.nE bounds the number of positions read in the external oracles. -/
def opens_toProto : Prop :=
  ∀ (X : Type) (E : ExtSpec) (R : IOR X E Unit extNone) (o : OpenB), R.OpensLe o →
    (∀ x ρ pl, (R.toInteractiveOracleProof.reads x ρ pl).card + (R.toInteractiveOracleProof.extReads x ρ).card ≤ o.n) ∧
    ∀ x ρ, (R.toInteractiveOracleProof.extReads x ρ).card ≤ o.nE

end Spec

open Classical in
theorem opensLe_of_bounds : Spec.opensLe_of_bounds := by
  intro Xi Xo Ei Eo R o h1 h2 h3 h4
  have hO : ∀ ρ (U : Finset Eo.Pos),
      (U.biUnion (R.srcO ρ)).card + (U.biUnion (R.srcE ρ)).card ≤ o.bl * U.card := fun ρ U => by
    calc
      (U.biUnion (R.srcO ρ)).card + (U.biUnion (R.srcE ρ)).card ≤
          (∑ q ∈ U, (R.srcO ρ q).card) + ∑ q ∈ U, (R.srcE ρ q).card :=
        Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ = ∑ q ∈ U, ((R.srcO ρ q).card + (R.srcE ρ q).card) := Finset.sum_add_distrib.symm
      _ ≤ ∑ _q ∈ U, o.bl := Finset.sum_le_sum fun q _ => h3 ρ q
      _ = o.bl * U.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  refine ⟨fun ρ U => ?_, fun ρ U => ?_⟩
  · have a1 := Finset.card_union_le (R.reads ρ) (U.biUnion (R.srcO ρ))
    have a2 := Finset.card_union_le (R.extReads ρ) (U.biUnion (R.srcE ρ))
    have a3 := hO ρ U
    have a4 := h1 ρ
    omega
  · have a2 := Finset.card_union_le (R.extReads ρ) (U.biUnion (R.srcE ρ))
    have a3 : (U.biUnion (R.srcE ρ)).card ≤ o.bE * U.card := by
      rw [Nat.mul_comm]
      exact Finset.card_biUnion_le_card_mul _ _ _ fun q _ => h4 ρ q
    have a4 := h2 ρ
    omega

theorem opensLe_copy : Spec.opensLe_copy := by
  intro X Xl E0 Ej F n k hk h1 h2 h3 h4 h5
  refine opensLe_of_bounds _ _ _ _ F ⟨n, 0, k, 1⟩ (fun ρ => ?_) (fun ρ => ?_)
    (fun ρ q => ?_) (fun ρ q => ?_)
  · rw [h1 ρ]
    exact h4 ρ
  · rw [h1 ρ]
    exact Nat.le_refl _
  · cases q with
    | inl p =>
      rw [(h2 ρ p).1, (h2 ρ p).2]
      exact hk
    | inr q =>
      rw [h3 ρ q]
      exact h5 ρ q
  · cases q with
    | inl p =>
      rw [(h2 ρ p).1]
      exact Nat.le_refl _
    | inr q =>
      rw [h3 ρ q]
      exact Nat.zero_le _

theorem opensLe_mono : Spec.opensLe_mono := by
  intro Xi Xo Ei Eo R o o' h1 h2 h3 h4 h
  exact ⟨fun ρ U => le_trans (h.tot ρ U) (Nat.add_le_add h1 (Nat.mul_le_mul_right _ h3)),
    fun ρ U => le_trans (h.ext ρ U) (Nat.add_le_add h2 (Nat.mul_le_mul_right _ h4))⟩

open Classical in
theorem opensLe_seq : Spec.opensLe_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ a b h₁ h₂
  -- what the second asks of the middle implicit instance, and what it opens of its own oracles
  have key : ∀ (ρ : Rho (R₁.shape ++ R₂.shape)) (U : Finset E₃.Pos),
      ((R₁.seq R₂).extReads ρ ∪ U.biUnion ((R₁.seq R₂).srcE ρ) ⊆
        R₁.extReads (Rho.fst ρ) ∪
          (R₂.extReads (Rho.snd (s := R₁.shape) ρ) ∪
              U.biUnion (R₂.srcE (Rho.snd (s := R₁.shape) ρ))).biUnion
            (R₁.srcE (Rho.fst ρ))) ∧
      ((R₁.seq R₂).reads ρ ∪ U.biUnion ((R₁.seq R₂).srcO ρ) ⊆
        (R₁.reads (Rho.fst ρ) ∪
              (R₂.extReads (Rho.snd (s := R₁.shape) ρ) ∪
                  U.biUnion (R₂.srcE (Rho.snd (s := R₁.shape) ρ))).biUnion
                (R₁.srcO (Rho.fst ρ))).image OPos.left ∪
          (R₂.reads (Rho.snd (s := R₁.shape) ρ) ∪
              U.biUnion (R₂.srcO (Rho.snd (s := R₁.shape) ρ))).image
            (OPos.right (s := R₁.shape))) := by
    intro ρ U
    constructor
    · intro p hp
      rcases Finset.mem_union.1 hp with h | h
      · have h' : p ∈
            R₁.extReads (Rho.fst ρ) ∪
              (R₂.extReads (Rho.snd (s := R₁.shape) ρ)).biUnion (R₁.srcE (Rho.fst ρ)) := h
        rcases Finset.mem_union.1 h' with h | h
        · exact Finset.mem_union_left _ h
        · obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.1 h
          exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨q, Finset.mem_union_left _ hq, hpq⟩)
      · obtain ⟨u, hu, h⟩ := Finset.mem_biUnion.1 h
        have h' : p ∈ (R₂.srcE (Rho.snd (s := R₁.shape) ρ) u).biUnion (R₁.srcE (Rho.fst ρ)) := h
        obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.1 h'
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.2
            ⟨q, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, hu, hq⟩), hpq⟩)
    · intro p hp
      rcases Finset.mem_union.1 hp with h | h
      · have h' : p ∈
          (R₁.reads (Rho.fst ρ) ∪
            (R₂.extReads (Rho.snd (s := R₁.shape) ρ)).biUnion (R₁.srcO (Rho.fst ρ))).image OPos.left
            ∪ (R₂.reads (Rho.snd (s := R₁.shape) ρ)).image (OPos.right (s := R₁.shape)) := h
        rcases Finset.mem_union.1 h' with h | h
        · obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 h
          refine Finset.mem_union_left _ (Finset.mem_image_of_mem _ ?_)
          rcases Finset.mem_union.1 hp' with h | h
          · exact Finset.mem_union_left _ h
          · obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.1 h
            exact Finset.mem_union_right
              _ (Finset.mem_biUnion.2 ⟨q, Finset.mem_union_left _ hq, hpq⟩)
        · obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 h
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hp'))
      · obtain ⟨u, hu, h⟩ := Finset.mem_biUnion.1 h
        have h' : p ∈
            ((R₂.srcE (Rho.snd (s := R₁.shape) ρ) u).biUnion (R₁.srcO (Rho.fst ρ))).image
                OPos.left ∪
              (R₂.srcO (Rho.snd (s := R₁.shape) ρ) u).image (OPos.right (s := R₁.shape)) := h
        rcases Finset.mem_union.1 h' with h | h
        · obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 h
          obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.1 hp'
          exact Finset.mem_union_left _
            (Finset.mem_image_of_mem _
              (Finset.mem_union_right _
                (Finset.mem_biUnion.2
                  ⟨q, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, hu, hq⟩), hpq⟩)))
        · obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 h
          exact Finset.mem_union_right _
            (Finset.mem_image_of_mem _
              (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, hu, hp'⟩)))
  refine ⟨fun ρ U => ?_, fun ρ U => ?_⟩
  · obtain ⟨k1, k2⟩ := key ρ U
    have c1 := Finset.card_le_card k1
    have c2 := le_trans (Finset.card_le_card k2)
      (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add Finset.card_image_le Finset.card_image_le))
    have t1 := h₁.tot (Rho.fst ρ)
      (R₂.extReads (Rho.snd (s := R₁.shape) ρ) ∪ U.biUnion (R₂.srcE (Rho.snd (s := R₁.shape) ρ)))
    have t2 := h₂.tot (Rho.snd (s := R₁.shape) ρ) U
    have e2 := h₂.ext (Rho.snd (s := R₁.shape) ρ) U
    generalize (R₂.extReads (Rho.snd (s := R₁.shape) ρ) ∪
        U.biUnion (R₂.srcE (Rho.snd (s := R₁.shape) ρ))).card = V at t1 t2 e2
    have hbl : a.bl * V ≤ V + (a.bl - 1) * (b.nE + b.bE * U.card) := by
      calc a.bl * V ≤ ((a.bl - 1) + 1) * V := Nat.mul_le_mul_right _ (by omega)
        _ = V + (a.bl - 1) * V := by ring
        _ ≤ V + (a.bl - 1) * (b.nE + b.bE * U.card) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ e2) _
    show _ ≤ (a.n + b.n + (a.bl - 1) * b.nE) + (b.bl + (a.bl - 1) * b.bE) * U.card
    have r1 : (a.bl - 1) * (b.nE + b.bE * U.card) =
        (a.bl - 1) * b.nE + (a.bl - 1) * b.bE * U.card := by ring
    have r2 : (b.bl + (a.bl - 1) * b.bE) * U.card = b.bl * U.card + (a.bl - 1) * b.bE * U.card := by
      ring
    omega
  · obtain ⟨k1, -⟩ := key ρ U
    have c1 := Finset.card_le_card k1
    have t1 := h₁.ext (Rho.fst ρ)
      (R₂.extReads (Rho.snd (s := R₁.shape) ρ) ∪ U.biUnion (R₂.srcE (Rho.snd (s := R₁.shape) ρ)))
    have e2 := h₂.ext (Rho.snd (s := R₁.shape) ρ) U
    generalize (R₂.extReads (Rho.snd (s := R₁.shape) ρ) ∪
        U.biUnion (R₂.srcE (Rho.snd (s := R₁.shape) ρ))).card = V at t1 e2
    have hb : a.bE * V ≤ a.bE * (b.nE + b.bE * U.card) := Nat.mul_le_mul_left _ e2
    show _ ≤ (a.nE + a.bE * b.nE) + a.bE * b.bE * U.card
    have r1 : a.bE * (b.nE + b.bE * U.card) = a.bE * b.nE + a.bE * b.bE * U.card := by ring
    omega

open Classical in
theorem opens_toProto : Spec.opens_toProto := by
  intro X E R o h
  refine ⟨fun x ρ pl => ?_, fun x ρ => ?_⟩
  · have := h.tot ρ ∅
    simpa using this
  · have := h.ext ρ ∅
    simpa using this

end Iop
