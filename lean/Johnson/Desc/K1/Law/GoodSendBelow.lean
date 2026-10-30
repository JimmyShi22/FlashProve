-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendBelow.lean: the written round of a place's seeds has as many typed
values as the place has joint seeds; and so a share of the joint seeds that bears the number e
bears, by the library's rule on written counts (Maps.below_err), the written errors of the piece
that holds a sending.

Main names: ds_seed, vals_seed; send_below.

What is not claimed. NO PRICE IS NAMED: c is a letter: that e is at most c times the number of the
joint seeds, and that c with the sampler's bias and the round's work is at most the bound, are
premises. One seed. Nothing on soundness of a protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSend4
import Johnson.Desc.K1.Law.Price
import OnBytes.Slice.NoWorkRatesRound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)
open scoped ENNReal

/-- What the place's entry of the seeds draws, at one seed. -/
theorem ds_seed (P : Par) (h1 : P.seeds = 1) :
    Fmt.dsOf (seedEntry P) .seeds =
      List.replicate P.coordinates Fmt.Draw.elem ++ [.elemNZ, .trits 0] := by
  have hE : (seedEntry P).drawE = P.coordinates + 1 := by
    show P.seeds * (P.coordinates + 1) = _
    rw [h1, Nat.one_mul]
  have hN : (seedEntry P).drawNZ = 1 := h1
  unfold Fmt.dsOf
  rw [dsElems_seed _ hN, dsSeeds_one, hE]
  show List.replicate 0 _ ++ _ = _
  simp [seedEntry]

/-- A count of a product of a power and the units, on plain numbers. -/
theorem card_seed (v : Nat) :
    Fintype.card ((Fin v → GE) × GEˣ) = Fintype.card GE ^ v * (Fintype.card GE - 1) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_units]

/-- **The written round has as many typed values as the place has joint seeds.** -/
theorem vals_seed (P : Par) (h1 : P.seeds = 1) (d : RDT) (he : d.entry = seedEntry P)
    (hk : d.kind = .seeds) :
    Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) =
      Fintype.card ((Fin P.coordinates → GE) × GEˣ) := by
  rw [he, hk, card_vals_all, ds_seed P h1, nVals_repE, card_seed, card_GE]
  simp only [nVals]
  ring

variable {T Cl W : Type} {F : Frame}

/-- **The written errors of a sending's piece are shares of at most εs**, where e is a share of at
most c of the seeds and c, with the sampler's bias and the round's work, is at most εs. -/
theorem send_below (P : Par) (h1 : P.seeds = 1) (b : Block T Cl) (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) (e : Nat) (c εs : ℝ≥0∞)
    (hc : (e : ℝ≥0∞) ≤ c * (Fintype.card ((Fin P.coordinates → GE) × GEˣ) : ℝ≥0∞))
    (hε : kapSl 128 ^ (bsRound .two d₁.entry d₁.kind).b * (c / 2 ^ d₁.entry.work) ≤ εs) :
    Err.Below (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).err εs := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws P h1 d₁ he₁ hk₁
  show Err.Below ((seedMaps d₁ d₂ P.coordinates).err ((e, ()) : Nat × Unit)) εs
  refine Maps.below_err (seedMaps d₁ d₂ P.coordinates) (seedMaps_ok d₂ a1 a2 a3 a4 a5)
    ((e, ()) : Nat × Unit) ?_
  refine ⟨⟨c, ?_, hε⟩, trivial⟩
  rw [vals_seed P h1 d₁ he₁ hk₁]
  exact hc

end VerifiableInference.Desc.K1
