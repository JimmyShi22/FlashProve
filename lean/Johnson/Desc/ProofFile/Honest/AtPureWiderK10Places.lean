-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureWiderK10Places.lean: the places of the closings' list
(`closeLotAt`, Honest/AtPureWiderK10.lean), at the letters of the opened description (`IM.Open`,
Johnson/IMR/SeatOpen.lean): none of its sides stands at a place that the description's first chain
lacks; no two stand at one place. Three lemmas; no definition. Each is one call of its authors' law
on `K10.seatLotC` (Honest/K10/LotAll.lean, LotPlaces.lean: another thread's files, which this one
imports), brought over by `closeLotAt_of_open`.

  `closeLotAt_clean`      `strays F.first.blocksInOrder ((closeLotAt I S).halves Z G) = []`
  `closeLotAt_once`       the sides' places have no double
  `closeLotAt_no_twice`   `twice ((closeLotAt I S).halves Z G) = []`

What it is for. `onlineProverFromPublicFiles` (Honest/AtPure.lean) refuses where a side of the first chain is a stray:
the first lemma is what the eleventh list owes to `onlineProverFromPublicFiles`'s return at `widerFillOwnC`. `ready`
(Honest/Frame.lean) refuses where two sides stand at one place: the third is the eleventh list's
share of that; that none of the ten stands at a place of the kind K10, and that the ten have no
double among themselves, are the other shares, and are not here.

Limits.
  * The one premise, `IM.Open`, holds wherever `onlineDescription` returns (the library's `IM.seat_open`). It
    is NOT got from `onlineProverFromPublicFiles`'s return here: that would be a circle for the first lemma's use.
  * All three say that something is absent: they hold also where the list lays nothing, there for
    nothing (so their authors say of the laws that are called). That the list lays a side at any
    place is not stated here.
  * Public data alone; of a side these statements read its place alone.
  * That `onlineProverFromPublicFiles` or `ready` returns at any choice of fields is not stated here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10
import Johnson.Desc.ProofFile.Honest.K10.LotAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription)

variable {W₀ X : Type}

/-- **No side of the closings' list is a stray.** -/
theorem closeLotAt_clean (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (G : Ground)
    {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub}
    {Bs : ProofFile.PureBase} {base : List (Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : Chain VerifiableInference.Desc.First.S ProofFile.Cl} {Sh : ProofFile.SharedSeat}
    {Se : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c Sh Se) :
    strays F.first.blocksInOrder ((closeLotAt (X := X) I S).halves Z G) = [] := by
  rw [closeLotAt_of_open I S G O]
  exact K10.seatLotC_clean _ _ _ G O

/-- **No two sides of the closings' list stand at one place.** -/
theorem closeLotAt_once (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (G : Ground)
    {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub}
    {Bs : ProofFile.PureBase} {base : List (Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : Chain VerifiableInference.Desc.First.S ProofFile.Cl} {Sh : ProofFile.SharedSeat}
    {Se : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c Sh Se) :
    (((closeLotAt (X := X) I S).halves Z G).map (·.place)).Nodup := by
  rw [closeLotAt_of_open I S G O]
  exact K10.seatLotC_once _ _ _ G O

/-- The frame's own test finds no double among them. -/
theorem closeLotAt_no_twice (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (G : Ground)
    {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub}
    {Bs : ProofFile.PureBase} {base : List (Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : Chain VerifiableInference.Desc.First.S ProofFile.Cl} {Sh : ProofFile.SharedSeat}
    {Se : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c Sh Se) :
    twice ((closeLotAt (X := X) I S).halves Z G) = [] := by
  rw [closeLotAt_of_open I S G O]
  exact K10.seatLotC_no_twice _ _ _ G O

end ProofFile.Honest

#print axioms ProofFile.Honest.closeLotAt_clean
#print axioms ProofFile.Honest.closeLotAt_once
#print axioms ProofFile.Honest.closeLotAt_no_twice
