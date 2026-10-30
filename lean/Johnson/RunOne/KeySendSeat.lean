-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendSeat.lean: A THEOREM. **One call for the seat of a sending**: the law (sendGood) at the count e := errPort P rad, and beside it that the piece's own errors, as shares of the
written challenges, are at most 2 ^ -128 (below_send).
  send_seat   for a block that Pays, at one seed, codes with lengths that are powers of two, radii that meet the library's test, a first written round that is the round of seeds, and the two tests with code (shareB, belowB) at some K:
              GoodIn between the borders' letters, the promise behind strengthened by «each new sampled message is sealed»; and Err.Below of the piece's errors
What is not claimed. The premises. That a frame's piece at the seat is sendPiece. Nothing on soundness.

-/
import Johnson.RunOne.KeySendBelow

set_option autoImplicit false

namespace Johnson.RunOne.KeySendGood

open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice Johnson.Pack Cb Cb.Ood Iop Prob Run
open Johnson.RunOne.KeySendErr
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.K1 (Par errPort sendPiece Sealed shapeAt shapesOf sampledAt)
open scoped ENNReal

variable {T Cl W : Type} {F : Frame}

theorem send_seat (K : Nat) (P : Par) (rad : Nat → Nat) (h1 : P.seeds = 1) (b : Block T Cl) (stOf : T → Statement) (hb : Pays P stOf b)
    (hl : P.codes.lengthsOk = true) (hm : ∀ k, sampledAt P k → meetsB P.codes (shapeAt P k) (rad k.val) = true)
    (hs : shareB K P rad = true) (hB : belowB K P = true)
    (base : Nat) (d₁ d₂ : RDT) (hd : SeedRound P d₁)
    (fOf : F.E.Str → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates (errPort P rad)).ior.imp y τ) = fIn y τ.1)
    (On On' : T × F.E.Str → Prop) (R R' : T × F.E.Str → W → Prop)
    (hkeep : ∀ a τ x, On a → (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates (errPort P rad)).ior.red.out a τ = some x → On' x)
    (hback : ∀ a τ x w, On a → (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates (errPort P rad)).ior.red.out a τ = some x → R' x w → R a w) :
    (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates (errPort P rad)).GoodIn On
      (fun x => On' x ∧ ∀ k, sampledAt P k →
        Sealed P.codes (shapeAt P k) (rad k.val) (fOf x.2 k) (stOf x.1) ((stOf x.1).oracles.size - (shapesOf P).length + k.val)) R R' ∧
      Err.Below (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates (errPort P rad)).err ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  ⟨sendGood P rad h1 b stOf hb hl hm base d₁ d₂ hd (errPort P rad) (Nat.le_refl _) fOf fIn hf On On' R R' hkeep hback,
    below_send K P rad h1 d₁ d₂ hd hs hB⟩

end Johnson.RunOne.KeySendGood

#print axioms Johnson.RunOne.KeySendGood.send_seat
