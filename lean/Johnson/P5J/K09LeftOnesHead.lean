-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09LeftOnesHead.lean: oneCells AND oneMask OF `LeftRest` AT THE CLOSED CONSTANT's
LETTERS, FROM THE HEAD ALONE: K09LeftOnes.lean's two with their one premise h6 paid. Statements with
their proofs; no definition.

Main names (namespace `P5J`).
  `oneShapeB_of_door`: the test `OnPublicFiles.oneShapeB` (Johnson/Desc/First/Look/K3MaskOkTools.lean)
    accepts wherever `H2K5.Door.oneShapeB` (Johnson/Desc/First/Att/Door/Law/K5MemOfSome.lean) does:
    two texts of one test ("any two members of the list at one seat have one shape") in two
    namespaces: they part in `decide (a = b)` against `a == b` alone.
  `AtMgA.left_h6`: `OnPublicFiles.oneShapeB h.𝔇.ms = true` from the head: by
    `H2K5.Door.oneShape_field` (Johnson/Desc/First/Att/Door/Law/K5HeadPaid.lean).
  **`AtMgA.left_oneCells_head`** · **`AtMgA.left_oneMask_head`**: the two fields from h, m < 25 and
    hx alone.

Limits. Those of K09LeftOnes.lean, less h6. NO MEMBER: that the head is met is not shown here.
Nothing on soundness or on hiding.

-/
import Johnson.P5J.K09LeftOnes
import Johnson.Desc.First.Att.Door.Law.K5HeadPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (OneReader ReadMsgOf)
open VerifiableInference.Desc.LinkJoin (rdC)
open OnBytes.Maker (WholeD)

/-- Two texts of one test. -/
theorem oneShapeB_of_door {ms : List Mem} (h : H2K5.Door.oneShapeB ms = true) :
    OnPublicFiles.oneShapeB ms = true := by
  unfold H2K5.Door.oneShapeB at h
  unfold OnPublicFiles.oneShapeB
  rw [List.all_eq_true] at h ⊢
  intro y hy
  have h1 := h y hy
  rw [List.all_eq_true] at h1 ⊢
  intro y' hy'
  have h2 := h1 y' hy'
  rw [Bool.or_eq_true] at h2 ⊢
  rcases h2 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (beq_iff_eq.2 (of_decide_eq_true h3))

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place}

/-- h6, from the head. -/
theorem AtMgA.left_h6 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    OnPublicFiles.oneShapeB h.𝔇.ms = true :=
  oneShapeB_of_door (H2K5.Door.oneShape_field h)

/-- **oneCells, from the head alone.** -/
theorem AtMgA.left_oneCells_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ}
    (hm : m < 25) {xx : Desc.First.Look.Place} (hx : lookAt (At.X Zp) m true = some xx)
    (tlD : HTailF2) :
    ∀ w : Desc.Wit (CellsM OnBytes.Flat.numsFull) At.Tok MsgT,
      OneReader (ReadMsgOf (cellAddr tlD) (seatOf h.𝔇.sent xx.link)) h.𝔇.sent.codes
        (digList xx h.𝔇.sent h.𝔇.l3.rad) (fun j => h.𝔇.l3.seat xx.link true j.1)
        (msgsOf h.𝔇.sent.codes (digList xx h.𝔇.sent h.𝔇.l3.rad)
          (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr w)
        (rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms w) :=
  h.left_oneCells hm hx tlD h.left_h6

/-- **oneMask, from the head alone.** -/
theorem AtMgA.left_oneMask_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ}
    (hm : m < 25) {xx : Desc.First.Look.Place} (hx : lookAt (At.X Zp) m true = some xx) :
    ∀ w : Desc.Wit (CellsM OnBytes.Flat.numsFull) At.Tok MsgT,
      OneReader (ReadMsgOf (maskAddr xx.arrays.ns) (seatOf h.𝔇.sent xx.link)) h.𝔇.sent.codes
        (digList xx h.𝔇.sent h.𝔇.l3.rad) (fun j => h.𝔇.l3.seat xx.link true j.1)
        (msgsOf h.𝔇.sent.codes (digList xx h.𝔇.sent h.𝔇.l3.rad)
          (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr w)
        (rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms w) :=
  h.left_oneMask hm hx h.left_h6

end P5J

#print axioms P5J.oneShapeB_of_door
#print axioms P5J.AtMgA.left_h6
#print axioms P5J.AtMgA.left_oneCells_head
#print axioms P5J.AtMgA.left_oneMask_head
