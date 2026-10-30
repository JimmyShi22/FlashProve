-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/DoorAtV.lean: `DoorStays` AT THE ONE HEAD'S OWN LETTERS AND AT THE LAST TABLE'S OWN SEATS
`LLT25.vAt Zp (At.N Zp cF)`. Three theorems: two by unfolding, one call.

  `vAt_index`, `vAt_w`: the first two of vAt's four are the numbers' own seats: by unfolding.
  **`doorStays_at_vAt`**: `doorStays_at_head` (Johnson/Desc/Last/DoorAtHead.lean) at V := LLT25.vAt Zp (At.N Zp cF): the two
    seats fall; the two counts of answers stay.

What stays a premise. h6, h7: the two shapes of vAt have one answer each: two equations of numbers on the public part.
Limits. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.DoorAtHead
import Johnson.LLT25R.LastAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Last
open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers)

theorem vAt_index (Z : ProofFile.Pub) (N₁ : Numbers) : (LLT25.vAt Z N₁).index = N₁.index := rfl

theorem vAt_w (Z : ProofFile.Pub) (N₁ : Numbers) : (LLT25.vAt Z N₁).w = N₁.w := rfl

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **`DoorStays` at the last table's own seats.** -/
theorem doorStays_at_vAt (h : P5J.AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    (h6 : (LLT25.vAt Zp (P5J.At.N Zp cF)).indexShape.answers = 1)
    (h7 : (LLT25.vAt Zp (P5J.At.N Zp cF)).wShape.answers = 1) :
    DoorStays (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks P5J.At.ps (h.𝔇 𝔇₀).pubD.P13
      (LLT25.vAt Zp (P5J.At.N Zp cF)) :=
  doorStays_at_head h 𝔇₀ _ rfl rfl h6 h7

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.vAt_index
#print axioms VerifiableInference.Desc.Last.vAt_w
#print axioms VerifiableInference.Desc.Last.doorStays_at_vAt
