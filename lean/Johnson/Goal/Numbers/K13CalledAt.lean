-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K13CalledAt.lean: the law of the kind K13's batching (K13/Law/PinA.lean:
atM3_goodInA) called at the typed numbers and at written rounds with the entries and kinds of the
written lists' stretch: its one premise on public numbers and written rounds (Declared) is paid, and
the piece's errors are shares of at most 2^-128.

  K13Called P Wr i: for every stretch of written rounds with the entries and kinds of Wr's 2 + kCol
      rounds from place i on, and for all letters that are left: the piece pieceM3 is GoodIn from on
      to FrontOk P at the relation RowsHoldA rw Pin on both sides; and Err.Below at 2^-128 of its
      errors
  k13Called_of: from K13Rounds
  k13_called_real: in a proof file (13 rows)
  k13_called_key: at a key file's numbers (24 rows) and written rounds. MIND: IT IS NOT THE KEY
      FILE's PLACE, AND BY TYPE IT CANNOT BE SPENT THERE: pieceM3 and atM3 stand over the proof
      file's first chain's record; a key file's description seats the kind through a lens on another
      record: what fits there is goodIn_any of pieceAt (K13/Law/GoodAny.lean):
      Johnson/Goal/Numbers/K13CapLawAt.lean

IT IS AN INSTANCE AT THE TYPED NUMBERS AND THE WRITTEN ROUNDS, NO MORE. THE LETTERS THAT ARE LEFT,
each with its premise as in the law: the frame F and the base; the number nR of the matrix's rows;
the reader rw of the witness; the pin Pin with hdet (two witnesses that are pinned at one state
agree on what the batching reads) and hback (the pin goes back over the piece); the condition on in
front. That these can be laid together at a description is not shown here.

What is not claimed. What the heads of the law's file and of Johnson/Goal/Numbers/K13CondAt.lean and
K13RoundsAt.lean do not claim. Nothing on soundness of a verifier, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K13RoundsAt
import Johnson.Desc.K13.Law.PinA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Params (Rounds LinSized)
open OnBytes.Params.Prices (AtRecord)
open Johnson.G (dryProofFull dryKeyFull codesFull2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull)
open scoped ENNReal

/-- **What the call gives.** -/
def K13Called (P : Where) (Wr : Rounds) (i : ℕ) : Prop :=
  ∀ (dZ d0 : RDT) (ds : List RDT),
    (dZ :: d0 :: ds).map (fun d => (d.entry, d.kind)) = stretch Wr i (2 + P.lin.kCol) →
    ∀ (Cl W : Type) (nR : ℕ) (F : Frame) (base : ℕ) (rw : W → Wit GE nR ds.length)
      (Pin : S × F.E.Str → W → Prop) (on : S × F.E.Str → Prop)
      (_ : ∀ a w w', on a → Pin a w → Pin a w' → AgreeAt a.1.out.indexMasks (rw w) (rw w'))
      (_ : ∀ a τ b w, (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).ior.red.out a τ = some b →
        Pin b w → Pin a w),
      (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn on (FrontOk P)
        (RowsHoldA rw Pin) (RowsHoldA rw Pin) ∧
      Err.Below (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).err ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem k13Called_of {P : Where} {Wr : Rounds} {i : ℕ} (h : K13Rounds P Wr i) :
    K13Called P Wr i := by
  intro dZ d0 ds hd Cl W nR F base rw Pin on hdet hback
  obtain ⟨hD, -, hB⟩ := h dZ d0 ds hd
  exact ⟨atM3_goodInA F P base dZ d0 ds hD ds.length rfl rw Pin on hdet hback, hB Cl W F base⟩

/-- **In a proof file.** -/
theorem k13_called_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ P : Where, P.rows = 13 → P.lin = x.shape → P.work = (0, 0, 0) →
      K13Called P dryProofFull.1 48270 := by
  obtain ⟨x, a1, a2, a3⟩ := k13_rounds_real
  exact ⟨x, a1, a2, fun P h1 h2 h3 => k13Called_of (a3 P h1 h2 h3)⟩

/-- At a key file's numbers and written rounds; not the key file's place (see the head). -/
theorem k13_called_key (P : Where) (h1 : P.rows = keyFull.ranges.pending)
    (h2 : P.lin = keyFull.once.shape) (h3 : P.work = (0, 0, 0)) :
    K13Called P dryKeyFull.1 18828 := k13Called_of (k13_rounds_key P h1 h2 h3)

end VerifiableInference.Desc.K13.Law
