-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09LeftOnes.lean: TWO OF THE NINE FIELDS OF `LeftRest`
(Johnson/Desc/First/Link/Law/LeftOfRest.lean: the named rest of K9's hLeft), oneCells AND oneMask,
AT THE CLOSED CONSTANT's LETTERS, FROM THE HEAD AND ONE NAMED TEST ON THE TABLE's LIST OF MEMBERS.
Beside Johnson/P5J/K09LeftPub.lean (dig, first, maskPub). Statements with their proofs; no
definition. No state stands in them.

Main names (namespace `P5J`).
  `AtMgA.left_memAt`: at a head h, a segment m < 25 and the digits' lookup's place there (hx :
    `lookAt (At.X Zp) m true = some xx`): EVERY member k of the digits' list, at the seats `fun j =>
    h.𝔇.l3.seat xx.link true j.1`, has in the table's list of members `h.𝔇.ms` a member that sits at
    its seat and has its shape (`MemAt`). By `k03_digits_seats` (K03SeatsAt.lean; its first
    clause: a member alike lies in the list) and `memAt_of_some`.
  `AtMgA.left_oneReader`: so, at whichever members Ks names: the exchange's reading of the witness
    (`msgsOf …`) and the link law's own reader `rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms w` are one (`OneReader Ks
    …`), at sT := these seats. By `oneReader_rdC` (Johnson/Desc/First/Link/Law/OneReaderClamp.lean)
    at `left_memAt`. That `h.𝔇.sent.codes` is `h.𝔇.cs`, that `h.𝔇.l3.arr` is `h.𝔇.arr`, and that
    `k03_digits_seats`' `h.toAtMg.𝔇 h.𝔇` has `h.𝔇`'s fields, closes by unfolding: Lean's to say.
  **`AtMgA.left_oneCells`** · **`AtMgA.left_oneMask`**: the two fields: its instances at the
    messages that hold the read cells, and at the mask row's.

How it joins: where `LeftRest` is wanted under `digAt (At.X Zp) m = some (xx, tlD)`, hx is
`look_of_dig` of it (K09LeftPub.lean; not imported here). In `left_oneCells` tlD IS A FREE LETTER:
it holds at every tail.
What stays a premise: h6 : `OnPublicFiles.oneShapeB h.𝔇.ms = true`: a closed test on the table's list of
members: any two members of the list at one seat have one shape.
Limits. `MemAt` is had at ALL members of the list, more than the fields read. NO MEMBER: that the
head is met, and that h6 holds at the release's files, is not shown here. At o := `OnBytes.secondHashFunction`
(as K09LeftPub.lean). Nothing on soundness or on hiding.

-/
import Johnson.P5J.K03SeatsAt
import Johnson.Desc.First.Link.Law.OneReaderClamp
import Johnson.Desc.First.Look.K3MaskOkTools

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
open VerifiableInference.Desc.First.Att.P (OneReader ReadMsgOf MemAt)
open VerifiableInference.Desc.LinkJoin (rdC oneReader_rdC)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place}

/-- Every member of the digits' list has its like in the table's list of members. -/
theorem AtMgA.left_memAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : Desc.First.Look.Place} (hx : lookAt (At.X Zp) m true = some xx)
    (h6 : OnPublicFiles.oneShapeB h.𝔇.ms = true)
    (k : Fin (digList xx h.𝔇.sent h.𝔇.l3.rad).length) :
    MemAt h.𝔇.ms (digList xx h.𝔇.sent h.𝔇.l3.rad) (fun j => h.𝔇.l3.seat xx.link true j.1) k :=
  memAt_of_some ((k03_digits_seats h hm hx).1 k) h6

/-- **The two readers are one at the digits' list**, at whichever members Ks names. -/
theorem AtMgA.left_oneReader (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : Desc.First.Look.Place} (hx : lookAt (At.X Zp) m true = some xx) (Ks : ℕ → Prop)
    (h6 : OnPublicFiles.oneShapeB h.𝔇.ms = true) :
    ∀ w : Desc.Wit (CellsM OnBytes.Flat.numsFull) At.Tok MsgT,
      OneReader Ks h.𝔇.sent.codes
        (digList xx h.𝔇.sent h.𝔇.l3.rad) (fun j => h.𝔇.l3.seat xx.link true j.1)
        (msgsOf h.𝔇.sent.codes (digList xx h.𝔇.sent h.𝔇.l3.rad)
          (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr w)
        (rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms w) :=
  fun w => oneReader_rdC Ks h.𝔇.sent.codes h.𝔇.l3.arr _ _ h.𝔇.ms w
    fun k _ => h.left_memAt hm hx h6 k

/-- **oneCells.** -/
theorem AtMgA.left_oneCells (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : Desc.First.Look.Place} (hx : lookAt (At.X Zp) m true = some xx) (tlD : HTailF2)
    (h6 : OnPublicFiles.oneShapeB h.𝔇.ms = true) :
    ∀ w : Desc.Wit (CellsM OnBytes.Flat.numsFull) At.Tok MsgT,
      OneReader (ReadMsgOf (cellAddr tlD) (seatOf h.𝔇.sent xx.link)) h.𝔇.sent.codes
        (digList xx h.𝔇.sent h.𝔇.l3.rad) (fun j => h.𝔇.l3.seat xx.link true j.1)
        (msgsOf h.𝔇.sent.codes (digList xx h.𝔇.sent h.𝔇.l3.rad)
          (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr w)
        (rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms w) :=
  h.left_oneReader hm hx _ h6

/-- **oneMask.** -/
theorem AtMgA.left_oneMask (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : Desc.First.Look.Place} (hx : lookAt (At.X Zp) m true = some xx)
    (h6 : OnPublicFiles.oneShapeB h.𝔇.ms = true) :
    ∀ w : Desc.Wit (CellsM OnBytes.Flat.numsFull) At.Tok MsgT,
      OneReader (ReadMsgOf (maskAddr xx.arrays.ns) (seatOf h.𝔇.sent xx.link)) h.𝔇.sent.codes
        (digList xx h.𝔇.sent h.𝔇.l3.rad) (fun j => h.𝔇.l3.seat xx.link true j.1)
        (msgsOf h.𝔇.sent.codes (digList xx h.𝔇.sent h.𝔇.l3.rad)
          (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr w)
        (rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms w) :=
  h.left_oneReader hm hx _ h6

end P5J

#print axioms P5J.AtMgA.left_memAt
#print axioms P5J.AtMgA.left_oneReader
#print axioms P5J.AtMgA.left_oneCells
#print axioms P5J.AtMgA.left_oneMask
