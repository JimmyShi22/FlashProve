-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendPow.lean: the written errors of the piece that holds a sending are
shares of at most 2^-k, from ONE comparison of natural numbers on the round of the seeds: with e the
count of bad seeds that the piece bears, V the number of the place's joint seeds, b the round's hash
blocks and w its bits of work: (2^128 + 1)^b * e * 2^k ≤ (2^128)^b * V * 2^w. By the library's rule
on written counts at natural numbers (Maps.below_pow, OnBytes/Flat/CarrySNum.lean), at the share
e / V. At numerals the comparison can be evaluated.

Main names: nVals_seed; send_below_pow, open_below_pow.

What is not claimed. THE COMPARISON IS A PREMISE: that it holds at a place of a plan is not said
here. Without it the law of a sending (send_goodIn and its kin) is worth nothing: at errors as large
as the number of the seeds it holds of every block. One seed. Nothing on soundness of a protocol, on
an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendEarlierMessages
import OnBytes.Flat.CarrySNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)
open scoped ENNReal

/-- The library's number of the written round's typed values is the number of the joint seeds. -/
theorem nVals_seed (P : Par) (h1 : P.seeds = 1) (d : RDT) (he : d.entry = seedEntry P)
    (hk : d.kind = .seeds) :
    nVals (Fmt.dsOf d.entry d.kind) = Fintype.card ((Fin P.coordinates → GE) × GEˣ) := by
  rw [← vals_seed P h1 d he hk, card_vals_all]

theorem seeds_pos (v : Nat) : 0 < Fintype.card ((Fin v → GE) × GEˣ) :=
  Fintype.card_pos_iff.2 ⟨(fun _ => 0, 1)⟩

variable {T Cl W : Type} {F : Frame}

/-- **The errors of a sending's piece are at most 2^-k, from one comparison in ℕ.** -/
theorem send_below_pow (P : Par) (h1 : P.seeds = 1) (b : Block T Cl) (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) (e k : Nat)
    (h : (2 ^ 128 + 1) ^ (bsRound .two d₁.entry d₁.kind).b * e * 2 ^ k ≤
      (2 ^ 128) ^ (bsRound .two d₁.entry d₁.kind).b *
        Fintype.card ((Fin P.coordinates → GE) × GEˣ) * 2 ^ d₁.entry.work) :
    Err.Below (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).err
      ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws P h1 d₁ he₁ hk₁
  show Err.Below ((seedMaps d₁ d₂ P.coordinates).err ((e, ()) : Nat × Unit)) _
  refine Maps.below_pow (seedMaps d₁ d₂ P.coordinates) (seedMaps_ok d₂ a1 a2 a3 a4 a5)
    ((e, ()) : Nat × Unit) ⟨⟨e, Fintype.card ((Fin P.coordinates → GE) × GEˣ),
      seeds_pos P.coordinates, ?_, h⟩, trivial⟩
  rw [nVals_seed P h1 d₁ he₁ hk₁]

/-- The like for a sending whose block goes on. -/
theorem open_below_pow (P : Par) (h1 : P.seeds = 1) (b : Block T Cl) (base : Nat) (d₁ : RDT)
    (ds : List RDT) (back : List Fmt.RoundView) (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds)
    (e k : Nat)
    (h : (2 ^ 128 + 1) ^ (bsRound .two d₁.entry d₁.kind).b * e * 2 ^ k ≤
      (2 ^ 128) ^ (bsRound .two d₁.entry d₁.kind).b *
        Fintype.card ((Fin P.coordinates → GE) × GEˣ) * 2 ^ d₁.entry.work) :
    Err.Below (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).err
      ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws P h1 d₁ he₁ hk₁
  show Err.Below ((seedMapsL d₁ ds P.coordinates).err ((e, ()) : Nat × Unit)) _
  refine Maps.below_pow (seedMapsL d₁ ds P.coordinates) (seedMapsL_ok ds a1 a2 a3 a4 a5)
    ((e, ()) : Nat × Unit) ⟨⟨e, Fintype.card ((Fin P.coordinates → GE) × GEˣ),
      seeds_pos P.coordinates, ?_, h⟩, Maps.heldN_skips k ds⟩
  rw [nVals_seed P h1 d₁ he₁ hk₁]


end VerifiableInference.Desc.K1
