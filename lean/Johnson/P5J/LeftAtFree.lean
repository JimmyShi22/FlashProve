-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LeftAtFree.lean: THE MEMBER: `h.ThreeLeft h.free`, AND WITH IT `h.Three h.free`.
Two theorems.

`AtMg.left_of_parts` (Johnson/P5J/LeftOfParts.lean) gives `h.ThreeLeft 𝔇₀ 𝔏`, for every 𝔏, from its
seven parts. At the value `h.free` (Johnson/P5J/FreeAll.lean) five of the seven are paid here:

  TP · PW: `Desc.K14.Law.Sh.TP_at_free` | `PW_at_free`
    (Johnson/Desc/K14/Law/SharedConstAtFree.lean); from the head alone.
  POf · POb: `Desc.K14.Law.Sh.POf_at_free` | `POb_at_free` (the same file); from the window hw.
  stepQ: `AtMg.stepQ_field` (Johnson/P5J/StepQAtMg.lean); its equation on h.free.Q₂ by rfl.

WHAT STAYS A PREMISE, BY NAME:
  head_cuts: the field itself, named by its projection.
  hw: two comparisons of numbers (the shared table's tree of the message Ω lies in the shared
    chain's window), in the letters of `POf_at_free`.
  S : h.toAtMg.Sh3Owed h.𝔇 h.free (Johnson/P5J/Sh3AtMg.lean): some R, Pw, V, X meet the five
    premises of the field SH₃ together.

  **`left_at_free`**: these three give h.ThreeLeft h.free.
  **`three_at_free_of`**: and so h.Three h.free (by `three_at_free`, Johnson/P5J/ThreeAtFree.lean).

Read against Johnson/P5J/FreeAll.lean, Johnson/P5J/FreeShared.lean and
Johnson/Desc/K14/Law/SharedConstAtFree.lean, which may still turn.
Limits. A joining: it pays no field by itself. That the three premises can be met is not shown here.
At the second hash function `OnBytes.secondHashFunction` alone. No soundness follows from it. Nothing on hiding.

-/
import Johnson.P5J.LeftOfParts
import Johnson.P5J.ThreeAtFree
import Johnson.Desc.K14.Law.SharedConstAtFree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ

open VerifierAndGoals.AtTheName
open VerifiableInference.Desc (Chain KindName)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

set_option quotPrecheck false in
/-- The shared table's constant's numbers, at the head. -/
local notation "NS" => Desc.K14.Law.Sh.nums h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)

set_option quotPrecheck false in
/-- The three rows of pieces, at the value's letters. -/
local notation "TF" => (h.toAtMg.threeOf h.free.e₁ h.free.e₂ h.free.e₃ h.free.dW h.free.wEnd)

/-- **The member.** -/
theorem left_at_free
    (head_cuts : fieldAt fun V : h.ThreeLeft h.free => ThreeLeftF.head_cuts V)
    (hw : (NS).lo ≤ ((NS).tenant .oOmega).1 ∧
      ((NS).tenant .oOmega).1 < hiAt (1 + (TF).l₂.length) (TF).p₂ (TF).l₂)
    (S : h.toAtMg.Sh3Owed h.𝔇 h.free) : h.ThreeLeft h.free :=
  h.toAtMg.left_of_parts h.𝔇 h.free head_cuts
    (by exact Desc.K14.Law.Sh.TP_at_free h 0 h.free.ML h.free.PLm h.free.e₁ h.free.e₂ h.free.e₃
          h.free.dW h.free.wEnd)
    (by exact Desc.K14.Law.Sh.PW_at_free h 0 h.free.ML h.free.PLm h.free.e₁ h.free.e₂ h.free.e₃
          h.free.dW h.free.wEnd)
    (by exact Desc.K14.Law.Sh.POf_at_free h 0 h.free.ML h.free.PLm h.free.e₁ h.free.e₂ h.free.e₃
          h.free.dW h.free.wEnd hw)
    (by exact Desc.K14.Law.Sh.POb_at_free h 0 h.free.ML h.free.PLm h.free.e₁ h.free.e₂ h.free.e₃
          h.free.dW h.free.wEnd hw)
    S _ (by exact rfl)

/-- **`h.Three h.free`** from the same three. -/
theorem three_at_free_of
    (head_cuts : fieldAt fun V : h.ThreeLeft h.free => ThreeLeftF.head_cuts V)
    (hw : (NS).lo ≤ ((NS).tenant .oOmega).1 ∧
      ((NS).tenant .oOmega).1 < hiAt (1 + (TF).l₂.length) (TF).p₂ (TF).l₂)
    (S : h.toAtMg.Sh3Owed h.𝔇 h.free) : h.Three h.free :=
  three_at_free h (left_at_free h head_cuts hw S)

end P5J

#print axioms P5J.left_at_free
#print axioms P5J.three_at_free_of
