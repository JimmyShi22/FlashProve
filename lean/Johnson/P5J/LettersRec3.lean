-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LettersRec3.lean: FIVE MORE PARAMETERS OF THE COMPOSED MEANING, LAID INTO ITS STRUCTURE.
One definition; two equations, proved by the make.

  `At.𝔇At3 Zp 𝔇₁`: over a structure 𝔇₁ (meant: `At.𝔇At …`, LettersRec.lean): d1 · P13 · mat13 · rq
    (LettersAt3.lean; LettersAt2.lean) · digitsPart := `digitsPartK3 (X Zp) 𝔇₁.sent 𝔇₁.l3`
    (Johnson/Desc/First/Look/K3FillDigits.lean): what the relation says of a segment's digits, AT
    𝔇₁'s OWN codes, shape, layout, arrays, arr, rad3 and seat3 (`MgData.sent`, `MgData.l3`): no
    second copy of a value stands in it.
  `digitsPart_own`: so the field is `digitsPartK3` at the laid structure's own sent and l3.
  `𝔇At3_keeps`: it leaves cs · arr · ms · N · decT.
Limits. A definition. Nothing on soundness.

-/
import Johnson.P5J.LettersAt3
import Johnson.Desc.First.Look.K3FillDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc.Sound (MgData)
open VerifiableInference.OnPublicFiles (digitsPartK3)

/-- **The five, laid.** -/
noncomputable def 𝔇At3 (Zp : ProofFile.Pub) {nR : ℕ}
    (𝔇₁ : MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp)) :
    MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp) :=
  { 𝔇₁ with
    d1 := d1 Zp, P13 := P13 Zp, mat13 := mat13 Zp nR
    digitsPart := digitsPartK3 (X Zp) 𝔇₁.sent 𝔇₁.l3, rq := rq Zp }

theorem digitsPart_own (Zp : ProofFile.Pub) {nR : ℕ}
    (𝔇₁ : MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp)) :
    (𝔇At3 Zp 𝔇₁).digitsPart = digitsPartK3 (X Zp) (𝔇At3 Zp 𝔇₁).sent (𝔇At3 Zp 𝔇₁).l3 := rfl

theorem 𝔇At3_keeps (Zp : ProofFile.Pub) {nR : ℕ}
    (𝔇₁ : MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull) nR (X Zp)) :
    (𝔇At3 Zp 𝔇₁).cs = 𝔇₁.cs ∧ (𝔇At3 Zp 𝔇₁).arr = 𝔇₁.arr ∧ (𝔇At3 Zp 𝔇₁).ms = 𝔇₁.ms ∧
      (𝔇At3 Zp 𝔇₁).N = 𝔇₁.N ∧ (𝔇At3 Zp 𝔇₁).decT = 𝔇₁.decT :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end P5J.At

#print axioms P5J.At.digitsPart_own
#print axioms P5J.At.𝔇At3_keeps
