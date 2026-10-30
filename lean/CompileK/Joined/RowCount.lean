-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Joined/RowCount.lean: how many positions the verifier of a file reads, if it is made from
three interactive oracle reductions in a row.

A second form of the compiler's verifier side, beside the library's own. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.


The laws of a wire record ask for a number that bounds how many positions the verifier opens. For a
file's verifier that is made from a row (CompileK/Joined/Row.lean) that number follows from numbers
of the three chains. A later chain reads the implicit part that an earlier chain has handed on; the
row reads in its place the positions from which the symbols read are computed. So the count needs,
beside each chain's own number of reads, a bound on how many positions a handed-on symbol is
computed from: 1 where it is a copy.

Main names:
  `Opens R n`: the reduction R reads at most n positions, of the implicit part and of its prover's
    oracles together.
  `Src R k`: each symbol that R hands on is computed from at most k positions.
  `opens_seq`: two reductions in a row read at most n₁ + k * n₂ positions.
  `Row.opens`: a row reads at most n₁ + k₁ * (n₂ + k₂ * n₃) positions; `Row.desc_opens`: so does the
    file's verifier.

Limits: the bound counts a position twice if two chains read it, while a set of positions holds it
once: so a number chosen by this bound may lie above what is opened. The numbers of the three chains
are owed of the description.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Joined.Row

set_option autoImplicit false

noncomputable section

namespace CompileK.Joined
open Iop
open _root_.Compile.Joined (Chains Desc)

/-! ## Two reductions in a row -/

section Two
variable {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec}

/-- the reduction reads at most n positions -/
def Opens {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) (n : ℕ) : Prop :=
  ∀ ρ, (R.reads ρ).card + (R.extReads ρ).card ≤ n

/-- each symbol that the reduction hands on is computed from at most k positions -/
def Src {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) (k : ℕ) : Prop :=
  ∀ ρ q, (R.srcE ρ q).card + (R.srcO ρ q).card ≤ k

open Classical in
/-- Two reductions in a row: what the first reads, and for each position that the second reads in
what was handed on at most k positions, and what the second reads of its own prover's oracles. -/
theorem opens_seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {n₁ n₂ k : ℕ}
    (h₁ : Opens R₁ n₁) (hk : Src R₁ k) (hk1 : 1 ≤ k) (h₂ : Opens R₂ n₂) :
    Opens (R₁.seq R₂) (n₁ + k * n₂) := by
  intro ρ
  have hO := Finset.card_biUnion_le (s := R₂.extReads (Rho.snd (s := R₁.shape) ρ))
    (t := R₁.srcO (Rho.fst ρ))
  have hE := Finset.card_biUnion_le (s := R₂.extReads (Rho.snd (s := R₁.shape) ρ))
    (t := R₁.srcE (Rho.fst ρ))
  have hsum : ∑ p ∈ R₂.extReads (Rho.snd (s := R₁.shape) ρ),
      ((R₁.srcE (Rho.fst ρ) p).card + (R₁.srcO (Rho.fst ρ) p).card) ≤
        (R₂.extReads (Rho.snd (s := R₁.shape) ρ)).card * k := by
    simpa [smul_eq_mul] using Finset.sum_le_card_nsmul _ _ k fun p _ => hk (Rho.fst ρ) p
  rw [Finset.sum_add_distrib] at hsum
  have hr : ((R₁.seq R₂).reads ρ).card ≤ (R₁.reads (Rho.fst ρ)).card +
      ((R₂.extReads (Rho.snd (s := R₁.shape) ρ)).biUnion (R₁.srcO (Rho.fst ρ))).card +
      (R₂.reads (Rho.snd (s := R₁.shape) ρ)).card :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_image_le.trans (Finset.card_union_le _ _)) Finset.card_image_le)
  have he : ((R₁.seq R₂).extReads ρ).card ≤ (R₁.extReads (Rho.fst ρ)).card +
      ((R₂.extReads (Rho.snd (s := R₁.shape) ρ)).biUnion (R₁.srcE (Rho.fst ρ))).card :=
    Finset.card_union_le _ _
  have a₁ := h₁ (Rho.fst ρ)
  have a₂ := Nat.mul_le_mul_right k (h₂ (Rho.snd (s := R₁.shape) ρ))
  rw [Nat.add_mul] at a₂
  have a₃ : (R₂.reads (Rho.snd (s := R₁.shape) ρ)).card ≤
      (R₂.reads (Rho.snd (s := R₁.shape) ρ)).card * k := Nat.le_mul_of_pos_right _ hk1
  rw [Nat.mul_comm k n₂]
  omega

end Two

/-! ## A row -/

namespace Row
variable {G : Chains} {Y : Type} {E : ExtSpec} (Rw : Row G Y E)

/-- a row reads at most n₁ + k₁ * (n₂ + k₂ * n₃) positions -/
theorem opens {n₁ n₂ n₃ k₁ k₂ : ℕ} (h₁ : Opens Rw.S₁.ior n₁) (h₂ : Opens Rw.S₂.ior n₂)
    (h₃ : Opens Rw.S₃.ior n₃) (s₁ : Src Rw.S₁.ior k₁) (s₂ : Src Rw.S₂.ior k₂) (p₁ : 1 ≤ k₁)
    (p₂ : 1 ≤ k₂) : Opens Rw.ior (n₁ + k₁ * (n₂ + k₂ * n₃)) :=
  opens_seq h₁ s₁ p₁ (opens_seq h₂ s₂ p₂ h₃)

/-- the same of the file's verifier, in the form in which the laws of a wire record ask for it -/
theorem desc_opens {n : ℕ} (h : Opens Rw.ior n) (pre : Y → Y) (x : Y) (ρ : Rho G.sh)
    (pl : Plains G.sh) :
    ((Rw.desc pre).reads x ρ pl).card + ((Rw.desc pre).extReads x ρ).card ≤ n := h ρ

end Row

end CompileK.Joined
