-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/DoorAtHead.lean: `DoorStays` (Johnson/Desc/Last/ShapeDoorFold.lean) AT THE ONE HEAD'S OWN LETTERS, GENERAL
IN THE OWN SEATS V. One theorem: a call.

  **`doorStays_at_head`**: DoorStays (At.N Zp cF) (h.mq 𝔇₀) fullLinks At.ps (h.𝔇 𝔇₀).pubD.P13 V, for V whose two seats are
    the table's numbers' own and whose two shapes have one answer each: `doorStays_mgAll`
    (Johnson/Desc/Last/ShapeDoorAtAll.lean) carried along `P5J.mgAt_is_mq`.

What stays a premise. hi, hw: V's two seats are (At.N Zp cF).index and .w. h6, h7: its two shapes have one answer each.
Limits. It reads neither `AtMg.rc` nor `AtMg.rch`. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorAtAll
import Johnson.P5J.RowsAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Last
open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.Sound

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **`DoorStays` at the one head's own letters.** -/
theorem doorStays_at_head (h : P5J.AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    (V : OwnSeats) (hi : V.index = (P5J.At.N Zp cF).index) (hw : V.w = (P5J.At.N Zp cF).w)
    (h6 : V.indexShape.answers = 1) (h7 : V.wShape.answers = 1) :
    DoorStays (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks P5J.At.ps (h.𝔇 𝔇₀).pubD.P13 V := by
  rw [← P5J.mgAt_is_mq h 𝔇₀]
  exact doorStays_mgAll (h.𝔇 𝔇₀) mgBase (P5J.At.N Zp cF) V hi hw h6 h7

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.doorStays_at_head
