-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PowB.lean: the one comparison of natural numbers from which the written errors
of a sending's piece are shares of at most 2^-k (send_below_pow, GoodSendPow.lean), as a test that
can be evaluated at a place: the bound on the place's bad seeds (errPort, Port6.lean) as a number
that computes, and the comparison as a Boolean.

Main names:
  qN           the field's size, as the format has it.
  rest_card    what a message does not read of one joint seed: qN ^ (v - the message's cube's bits).
  eNat         the bound on the place's bad seeds, computed; errPort_eNat: it is errPort.
  powB P rad k   the comparison at the place's own entry of the seeds (its work is P.work).
  powB_send, powB_open   a yes gives Err.Below at 2^-k, at the count errPort P rad.

What is not claimed. A yes of powB at a place is known by evaluation, or is a premise. One seed; one
answer a message. Nothing on soundness of a protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendPow
import Johnson.Desc.K1.Law.Price

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)
open scoped ENNReal

/-- The field's size. -/
def qN : Nat := Fmt.Fld.two.p ^ 3

theorem card_seeds_one (P : Par) (h1 : P.seeds = 1) :
    Fintype.card (Seeds P) = allSeeds qN P.coordinates := by
  rw [Fintype.card_fun, Fintype.card_fin, h1, pow_one, card_seed, card_GE]
  rfl

theorem qN_pos : 2 ≤ qN := by
  rw [qN, ← card_GE]
  exact Fintype.one_lt_card

/-- **What a message does not read of one joint seed.** -/
theorem rest_card (P : Par) (h1 : P.seeds = 1) (k : Fin (shapesOf P).length)
    (hk : sampledAt P k) :
    Fintype.card (Rest GE GEˣ P.seeds 1 P.coordinates (bitsZ P.codes (shapeAt P k))) =
      qN ^ (P.coordinates - bitsZ P.codes (shapeAt P k)) := by
  have h := seeds_total P k hk
  rw [card_seeds_one P h1, pow_one, card_GE] at h
  have hv := bits_le_coordinates P k hk
  have hq := qN_pos
  have hpos : 0 < allSeeds qN (bitsZ P.codes (shapeAt P k)) :=
    Nat.mul_pos (pow_pos (by omega) _) (by omega)
  refine Nat.eq_of_mul_eq_mul_left hpos (h.trans ?_)
  unfold allSeeds
  have e : qN ^ P.coordinates = qN ^ bitsZ P.codes (shapeAt P k) *
      qN ^ (P.coordinates - bitsZ P.codes (shapeAt P k)) := by
    rw [← pow_add, Nat.add_sub_cancel' hv]
  rw [e]
  ring

/-- The bound on the place's bad seeds, computed. -/
def eNat (P : Par) (rad : Nat → Nat) : Nat :=
  (List.ofFn fun k : Fin (shapesOf P).length => if sampledAt P k then
    (lOf P.codes (shapeAt P k) (rad k.val)).choose 2 *
      clashSeeds qN (bitsZ P.codes (shapeAt P k)) *
      qN ^ (P.coordinates - bitsZ P.codes (shapeAt P k)) else 0).sum

theorem errPort_eNat (P : Par) (h1 : P.seeds = 1) (rad : Nat → Nat) :
    errPort P rad = eNat P rad := by
  rw [errPort_eq, eNat, List.sum_ofFn]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : sampledAt P k
  · rw [if_pos hk, if_pos hk, rest_card P h1 k hk, pow_one, card_GE]
    rfl
  · rw [if_neg hk, if_neg hk]

/-- **The comparison, at the place's own entry of the seeds.** -/
def powB (P : Par) (rad : Nat → Nat) (k : Nat) : Bool :=
  decide ((2 ^ 128 + 1) ^ (bsRound .two (seedEntry P) .seeds).b * eNat P rad * 2 ^ k ≤
    (2 ^ 128) ^ (bsRound .two (seedEntry P) .seeds).b * allSeeds qN P.coordinates * 2 ^ P.work)

variable {T Cl W : Type} {F : Frame}

theorem powB_cmp (P : Par) (h1 : P.seeds = 1) (rad : Nat → Nat) (k : Nat)
    (h : powB P rad k = true) (d₁ : RDT) (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) :
    (2 ^ 128 + 1) ^ (bsRound .two d₁.entry d₁.kind).b * errPort P rad * 2 ^ k ≤
      (2 ^ 128) ^ (bsRound .two d₁.entry d₁.kind).b *
        Fintype.card ((Fin P.coordinates → GE) × GEˣ) * 2 ^ d₁.entry.work := by
  have h' := of_decide_eq_true h
  rw [he₁, hk₁, errPort_eNat P h1, card_seed, card_GE]
  exact h'

/-- **A yes gives the written errors at most 2^-k**, at the count errPort P rad. -/
theorem powB_send (P : Par) (h1 : P.seeds = 1) (rad : Nat → Nat) (k : Nat)
    (h : powB P rad k = true) (b : Block T Cl) (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) :
    Err.Below (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates (errPort P rad)).err
      ((2 : ℝ≥0∞)⁻¹ ^ k) :=
  send_below_pow P h1 b base d₁ d₂ he₁ hk₁ _ k (powB_cmp P h1 rad k h d₁ he₁ hk₁)

theorem powB_open (P : Par) (h1 : P.seeds = 1) (rad : Nat → Nat) (k : Nat)
    (h : powB P rad k = true) (b : Block T Cl) (base : Nat) (d₁ : RDT) (ds : List RDT)
    (back : List Fmt.RoundView) (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) :
    Err.Below (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates (errPort P rad)).err
      ((2 : ℝ≥0∞)⁻¹ ^ k) :=
  open_below_pow P h1 b base d₁ ds back he₁ hk₁ _ k (powB_cmp P h1 rad k h d₁ he₁ hk₁)


end VerifiableInference.Desc.K1
