-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/ReplyTiedN.lean.
It imports Desc/Sound/TiedSeat.lean for the one name SeatOf, not Law/K7Seated.lean: the files that
stand on this one (P4R/Back341N.lean and those above it) need nothing of the next token's tie.



WHAT IT DOES NOT SHOW. No soundness. NOT THE TIE OF THE NEXT TOKEN's BLOCK: OF THE SMALLER BILL OF
THAT TIE (Johnson/Desc/Kinds/Law/K7Seated.lean: K7Left) TWO FIELDS ARE PAID HERE, "yes" AND "front",
AND THE PREMISE SeatOf OF THE CARRIAGE BESIDE IT; the other fields (place, next, head · fresh ·
book, told · req · dec · tok · order, pub, pubP, held, shown · frames) are paid by nobody here. That
a piece of the description's row holds this block beneath the lift over the public part: not here.
That onlineDescription returns in scope: a premise (through the opening O). NO MEMBER. SeatOf IS PAID AT Bst
:= b: ITS FIRST HALF ("b narrows what the seat lays") IS THEN IDLE (b narrows b): the carriage
(Johnson/Desc/Sound/TiedLays.lean: tiedBy_of_seatE) reads Bst in SeatOf alone, and the bill asks
what the seat lays through its own field "yes"; the second half (a yes of b bears no mark) is what
weighs.
LETTERS. Under "there is": Lk: pinned by c.links[24]? = some Lk · b: by Lk.hear[0]? = some b · rs',
gs' (inside "yes"): the front of the caller's rounds and groups: handed out by P4.k7_place's clause
"same".
OBJECT. ProofFile.onlineDescription's value at the second hash function, opened (IMR/SeatOpen.lean: Open
OnBytes.secondHashFunction): the block number 338 of the first chain's flat list; and the two halves of the
seated constant (IMR/K7Seat.lean: k7Block): k7Front, then Stored/ReplySeatAt.lean's blockOf W 24.
USER. Whoever hands a description's piece at number 338 to Law/K7Seated.lean's k7_tied_seat.
WHAT IT IS.
  k7Front           the seated constant's first half: the entry of the head's link as a block
                    without a round, under the guard on the reply's seat.
  k7Block_is        the seated constant is k7Front, then the next token's block: by definition.
  k7_front          a yes of k7Front is a yes of the entry's own function (the base's
                    guarded_under).
  k7_left_seat      at the block that the description holds: the cut at 338 · SeatOf b b · "yes" ·
                    "front", in the bill's own letters (front := k7Front W · name := "H:1" · l := 24
                    · tl := W.H.tl).

-/
import Johnson.P4R.ReplyAtPlaceN
import Johnson.Desc.Sound.TiedSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4

open VerifiableInference.Desc (Block Chain Link FileDescription roundlessBlock)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (headFrontQ)
open VerifiableInference.Desc.Kinds (Reply.blockOf)
open VerifiableInference.Desc.Sound (SeatOf)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

/-- The seated constant's first half. -/
def k7Front (W : OnBytes.Model.Verify.Public) : Block S Unit :=
  Block.guarded ProofFile.sameReply (fun _ => false)
    ({ (roundlessBlock "H:1" 1 (some 24) 1 (headFrontQ W.H.tl) : Block S Unit) with
      place := (Reply.blockOf W 24).place })

/-- The seated constant is that half, then the next token's block. -/
theorem k7Block_is (W : OnBytes.Model.Verify.Public) :
    IM.k7Block W 24 = (k7Front W).andThen "H:1" (Reply.blockOf W 24) := rfl

/-- A yes of the first half is a yes of the entry's own function. -/
theorem k7_front (W : OnBytes.Model.Verify.Public) :
    ∀ x rs gs x1, (k7Front W).decide x rs gs = .ok x1 → headFrontQ W.H.tl x = .ok x1 :=
  fun x rs gs x1 h =>
    VerifiableInference.Desc.guarded_under ProofFile.sameReply (fun _ => false) _ x rs gs x1 h

/-- **TWO FIELDS OF THE BILL, AND THE CARRIAGE's PREMISE, AT THE BLOCK THAT THE DESCRIPTION
HOLDS.** -/
theorem k7_left_seat {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (b : Block S Cl), c.links[24]? = some Lk ∧ Lk.hear[0]? = some b ∧
      c.blocksInOrder = c.blocksInOrder.take 338 ++ b :: c.blocksInOrder.drop (338 + 1) ∧ SeatOf b b ∧
      (∀ x rs gs t, b.decide x rs gs = .ok t →
        ∃ rs' gs', ((k7Front Bs.G₀.W).andThen "H:1" (Reply.blockOf Bs.G₀.W 24)).decide x rs' gs' =
          .ok t) ∧
      ∀ x rs gs x1, (k7Front Bs.G₀.W).decide x rs gs = .ok x1 →
        headFrontQ Bs.G₀.W.H.tl x = .ok x1 := by
  obtain ⟨Lk, b, e1, e2, H⟩ := k7_place hS hR O
  refine ⟨Lk, b, e1, e2, H.cut,
    ⟨⟨rfl, fun _ _ _ _ h => h⟩, fun s rs gs t h => (H.same s rs gs t h).2⟩,
    fun x rs gs t h => ⟨rs.take (IM.k7Block Bs.G₀.W 24).rounds.length,
      gs.take (IM.k7Block Bs.G₀.W 24).openings, ?_⟩, k7_front Bs.G₀.W⟩
  rw [← k7Block_is]
  exact (H.same x rs gs t h).1

end P4

#print axioms P4.k7Block_is
#print axioms P4.k7_front
#print axioms P4.k7_left_seat
