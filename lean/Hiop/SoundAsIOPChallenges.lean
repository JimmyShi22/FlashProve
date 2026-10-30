-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/SoundAsIOPChallenges.lean: what the verifier draws in the whole run of Hiop/SoundAsIOP.lean: two
points of out-of-domain samples, and the challenges of the offline, the link and the online part.
Nothing else.

Why. Completeness as an IOP speaks of "all that a whole run draws": two seeds, the challenges of the
three parts, and the prover's coins. Here the verifier's randomness of the whole run is shown to be
two points and three lists of challenges (VerifierDraw), by a one-to-one map, and a uniform draw of the
one to be a uniform draw of the other. This file imports no file on completeness: the type is written
out. That VerifierDraw is the verifier's part of that statement's draw is so by the two texts; no
theorem says it.

  `HolographicProtocol.VerifierDraw L`: (point, point) and the three lists of challenges.
  `HolographicProtocol.wholeRunDraw`: the verifier's randomness of a whole run, read; an equivalence.
  `wholeRunDraw_uniform`: uniform randomness of the whole run, read, is a uniform draw.
  `wholeRunOf_draw`: the samples' points and the three parts' challenges in a full transcript, as
    `wholeRunOf` reads it, are those of the transcript's randomness, read.

Limits. Equations on what is drawn. Nothing on soundness, completeness or what a view shows. The
three further rounds of the whole run (two answers, the naming of a request) have one challenge each,
the empty one.
-/
import Hiop.SoundAsIOP
import Iop.ShapeKit

set_option autoImplicit false

noncomputable section

namespace Iop
open Prob Blocks

variable {Index Request : Type}

namespace HolographicProtocol

/-- All that the verifier draws in a whole run: the points of the two out-of-domain samples, and the
challenges of the three parts. -/
abbrev VerifierDraw (L : HolographicProtocol Index Request) : Type :=
  (L.OutOfDomainSeed × L.OutOfDomainSeed) × (Rho L.offline.shape × Rho L.link.shape × Rho L.onlineBatch.loc.shape)

/-- **The verifier's randomness of a whole run is that draw**: one to one and onto. -/
def wholeRunDraw (L : HolographicProtocol Index Request) (fill : L.Fill) :
    Rho (L.wholeRunShape fill) ≃ L.VerifierDraw where
  toFun ρ :=
    ((ρ.1, (Rho.snd (s := L.offline.shape) ρ.2.2).1),
      (Rho.fst ρ.2.2, Rho.fst (Rho.snd (s := L.offline.shape) ρ.2.2).2.2,
        (Rho.snd (s := L.link.shape) (Rho.snd (s := L.offline.shape) ρ.2.2).2.2).2))
  invFun d :=
    (d.1.1, (), Rho.app (s := L.offline.shape) d.2.1
      (d.1.2, (), Rho.app (s := L.link.shape) d.2.2.1 ((), d.2.2.2)))
  left_inv := by
    rintro ⟨p₁, ⟨⟩, ρ⟩
    obtain ⟨a, σ, rfl⟩ : ∃ (a : Rho L.offline.shape) (σ : Rho (L.tableRounds fill ++ (L.link.shape ++
           (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)))), ρ = Rho.app a σ :=
      ⟨Rho.fst ρ, Rho.snd (s := L.offline.shape) ρ, (Rho.app_fst_snd (s := L.offline.shape) ρ).symm⟩
    obtain ⟨p₂, ⟨⟩, σ⟩ := σ
    obtain ⟨b, υ, rfl⟩ : ∃ (b : Rho L.link.shape)
        (υ : Rho (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)), σ = Rho.app b υ :=
      ⟨Rho.fst σ, Rho.snd (s := L.link.shape) σ, (Rho.app_fst_snd (s := L.link.shape) σ).symm⟩
    obtain ⟨⟨⟩, c⟩ := υ
    simp only [Rho.fst_app, Rho.snd_app]
  right_inv := by
    rintro ⟨⟨p₁, p₂⟩, a, b, c⟩
    simp only [Rho.fst_app, Rho.snd_app]

end HolographicProtocol

/-- Uniform randomness of the whole run, read, is a uniform draw. -/
theorem wholeRunDraw_uniform (L : HolographicProtocol Index Request) (fill : L.Fill) :
    (unif (Rho (L.wholeRunShape fill))).map (L.wholeRunDraw fill) = unif L.VerifierDraw :=
  map_unif_equiv (L.wholeRunDraw fill)

/-- The points and the challenges that `wholeRunOf` reads in a full transcript are those of the
transcript's randomness, read. -/
theorem wholeRunOf_draw (L : HolographicProtocol Index Request) (fill : L.Fill) (τ : Tr (L.wholeRunShape fill)) :
    (((L.wholeRunOf fill τ).firstSample.1, (L.wholeRunOf fill τ).copySample.1),
      ((L.wholeRunOf fill τ).offline.rho, (L.wholeRunOf fill τ).link.rho,
        (L.wholeRunOf fill τ).online.rho)) = L.wholeRunDraw fill τ.rho := by
  obtain ⟨m₁, p₁, m₂, ⟨⟩, τ⟩ := τ
  obtain ⟨a, σ, rfl⟩ : ∃ (a : Tr L.offline.shape) (σ : Tr (L.tableRounds fill ++ (L.link.shape ++
         (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)))), τ = Tr.app a σ :=
    ⟨Tr.fst τ, Tr.snd (s := L.offline.shape) τ, (Tr.app_fst_snd (s := L.offline.shape) τ).symm⟩
  obtain ⟨m₃, p₂, m₄, ⟨⟩, σ⟩ := σ
  obtain ⟨b, υ, rfl⟩ : ∃ (b : Tr L.link.shape)
      (υ : Tr (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape)), σ = Tr.app b υ :=
    ⟨Tr.fst σ, Tr.snd (s := L.link.shape) σ, (Tr.app_fst_snd (s := L.link.shape) σ).symm⟩
  obtain ⟨m₅, ⟨⟩, c⟩ := υ
  simp only [HolographicProtocol.wholeRunOf, Tr.fst_app, Tr.snd_app]
  have h₂ : Tr.rho (Tr.app (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) b
      (m₅, (), c)) =
      Rho.app (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) b.rho ((), c.rho) :=
    Tr.rho_app b _
  have h₁ : Tr.rho (Tr.app (t := L.tableRounds fill ++ (L.link.shape ++
        (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape))) a
      (m₃, p₂, m₄, (), Tr.app (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) b
        (m₅, (), c))) =
      Rho.app (t := L.tableRounds fill ++ (L.link.shape ++
        (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape))) a.rho
      (p₂, (), Rho.app (t := plainRound Request Unit fill.request :: L.onlineBatch.loc.shape) b.rho
        ((), c.rho)) :=
    (Tr.rho_app a _).trans (congrArg (fun z => Rho.app (t := L.tableRounds fill ++ (L.link.shape ++
        (plainRound Request Unit fill.request :: L.onlineBatch.loc.shape))) a.rho (p₂, (), z)) h₂)
  exact ((L.wholeRunDraw fill).apply_symm_apply ((p₁, p₂), a.rho, b.rho, c.rho)).symm.trans
    (congrArg (fun z => L.wholeRunDraw fill ((p₁, (), z) : Rho (L.wholeRunShape fill))) h₁.symm)

end Iop

#print axioms Iop.HolographicProtocol.wholeRunDraw
#print axioms Iop.wholeRunDraw_uniform
#print axioms Iop.wholeRunOf_draw
