-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/PlanLeftBase.lean: two of the last table's tests on the plan, `fence` and `placeB`
(fields of `LLT25.LastPlan8`, Johnson/LLT25R/LastLedger.lean, which `PlanOk₃` extends), name the
number of the last chain's first own tree as `baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)`. A sheet
that evaluates the two tests writes that number as `D.t₁ + D.t₂`. Here: each field says the same at
the one spelling as at the other. Four theorems. No definition.

Why. An evaluated "true" at `D.t₁ + D.t₂` says nothing of a field that is spelled with
`baseTwoAt …` until the two numbers are known to be one.

  `fence_iff_base`, `placeB_eq_base`: the field at `baseTwoAt …` against the same text at
    `D.t₁ + D.t₂`.
  `fence_of_base`, `placeB_of_base`: from the text at `D.t₁ + D.t₂` to the field, sign for sign.
Each proof is one rewrite by `LLT25.baseTwo_pure` (Johnson/LLT25R/LastNum.lean), which has no
premise: the two sub-protocols in front of the own proximity test declare no round, so they send no
tree.

Every letter is free: o, mk, Z, A, N, c, D, mine, num, dB, dt. `PlanOk₃` lays A := `seatK Z N`, mine
:= `mineOf ms₁ ms₂ N₁ Ns`, num := `numAt D.t₁ D.t₂ 2`.

Limits. That either test says yes at any plan is not shown here. Nothing on soundness.
-/
import Johnson.LLT25R.LastLedger
import Johnson.LLT25R.LastNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P2Law.PlanLeft
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open LLT25
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (S)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
  (c : Chain S Cl) (D : WholeD)

/-- The field `fence` says the same at either spelling of the number. -/
theorem fence_iff_base (mine : List Mem) :
    Fenced (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) mine ↔ Fenced (D.t₁ + D.t₂) mine := by
  rw [baseTwo_pure o mk Z A N c D]

/-- **From the text at `D.t₁ + D.t₂` to the field `fence`.** -/
theorem fence_of_base (mine : List Mem) (h : Fenced (D.t₁ + D.t₂) mine) :
    Fenced (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) mine :=
  (fence_iff_base o mk Z A N c D mine).2 h

/-- The test `PlaceB` returns the same at either spelling of the number. -/
theorem placeB_eq_base (num : Fmt.TreeSource → ℕ) (dB : RDT) (dt : List RDT) :
    PlaceB (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3, none, 2,
                                        .K12⟩ N.W) num (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) dB dt =
    PlaceB (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3, none, 2,
                                        .K12⟩ N.W) num (D.t₁ + D.t₂) dB dt := by
  rw [baseTwo_pure o mk Z A N c D]

/-- **From the test's yes at `D.t₁ + D.t₂` to the field `placeB`.** -/
theorem placeB_of_base (num : Fmt.TreeSource → ℕ) (dB : RDT) (dt : List RDT)
    (h : PlaceB (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3, none, 2,
                                        .K12⟩ N.W) num (D.t₁ + D.t₂) dB dt = true) :
    PlaceB (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3, none, 2,
                                        .K12⟩ N.W) num (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) dB dt = true :=
  (placeB_eq_base o mk Z A N c D num dB dt).trans h

end P2Law.PlanLeft

#print axioms P2Law.PlanLeft.fence_iff_base
#print axioms P2Law.PlanLeft.fence_of_base
#print axioms P2Law.PlanLeft.placeB_eq_base
#print axioms P2Law.PlanLeft.placeB_of_base
