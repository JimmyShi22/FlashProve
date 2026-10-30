-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/MemberAtW.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: **NUMBER 356 OF THE FIRST CHAIN's FLAT LIST, IN SCOPE, IS W's SENDING**: the
member has the place, rounds and oracle messages of the plan K1.parW at the message that the shape
gives; it is a sending of that plan; it books as one. The like of k1_two_inScope and
k1_fifty_inScope (Honest/K1/Law/MemberInScope.lean) at W's place; and of their fellows on the mark.
Two statements with their proofs; no definition. PUBLIC: blocks of the description and their
decisions.

  k1_w_inScope   THE STATEMENT: what the record K1Seated (Honest/K1/Seated.lean) asks of the member
                 alone (its fields shape · isSend · books), at the plan of the job wJobAt
                 (Honest/K1/PlaceW.lean)
  k1_w_noMark    under the same premises: a yes of the member's decision leaves no mark
                 (t.failed = none): the seat's own guard says so (IM.yes_alone)

By IM.back_of, IM.back_numbers (Johnson/IMR/BackSeat.lean: the fourth block behind the links is the
lot's own block atM4 (whereOf Z) w, laid alone; it is number 356 of the flat list, with another test
on the plan); IM.alone_place, alone_rounds, alone_oracles, alone_underR, yes_alone
(Johnson/IMR/SeatForm.lean);
planOk_underR (Johnson/Desc/AtSeats/K13SitsJoin.lean); isSend_atM4, atM4_booked
(Johnson/Desc/K13/Law/AtRecord.lean); K1.isSend_underR, isSend_retype
(Johnson/Desc/K1/Law/SitsLaw.lean); books_under (MemberInScope.lean).

Limits. In scope, at an opening (IM.Open): premises. The block that the lot joins behind W's sending
(K13's rowsB) has no round and no oracle message; what it asks of the state is not told here.
Nothing on a prover, on data or on coins. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.MemberInScope
import Johnson.Desc.ProofFile.Honest.K1.PlaceW
import Johnson.Desc.AtSeats.K13SitsJoin
import Johnson.Desc.K13.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **NUMBER 356, IN SCOPE**: the shape gives a message with W; the member has the place, rounds and
oracle messages of W's plan at it; it is a sending of that plan; it books as one. -/
theorem k1_w_inScope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {blk : Block S ProofFile.Cl}
    (hb : c.blocksInOrder[356]? = some blk) :
    ∃ msg, linMessageW Z.first.lin = some msg ∧
      (blk.place = (K1.parW Z.first (wGp Z) 4 msg).place ∧
        blk.rounds = K1.rounds (K1.parW Z.first (wGp Z) 4 msg) ∧
        blk.oracles = K1.oracles (K1.parW Z.first (wGp Z) 4 msg)) ∧
      K1.IsSend (K1.parW Z.first (wGp Z) 4 msg) (fun s : S => s.st) blk ∧
      ∀ s s' r₁ r₂ gs, blk.decide s [r₁, r₂] gs = .ok s' →
        K1.Booked (K1.parW Z.first (wGp Z) 4 msg) s.book s.st.oracles.size s'.book
          s'.st.oracles.size := by
  obtain ⟨-, -, -, b, b', w, hb3, -, hw, rfl, hl⟩ := IM.back_of O
  have hfl := (IM.back_numbers hS hR O).1 3 b hb3
  obtain rfl := Option.some.inj (hfl.symm.trans hb)
  unfold K13.wBlock K1.wAt at hw
  obtain ⟨msg, hm, rfl⟩ := Option.map_eq_some_iff.1 hw
  have hu : Block.UnderR { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }
      ((K13.atM4 (K13.whereOf Z) (K1.sendAtS (K1.parW Z.first (wGp Z) 4 msg)) :
        Block S Unit).retype : Block S ProofFile.Cl) :=
    (K13.Law.planOk_underR b _).trans (IM.alone_underR hl)
  refine ⟨msg, hm, ⟨(IM.alone_place hl : b.place = _), ?_, ?_⟩,
    K1.isSend_underR hu (K1.isSend_retype (K13.Law.isSend_atM4 _ _)),
    books_under hu.2 fun s s' r₁ r₂ gs hd => K13.Law.atM4_booked hd⟩
  · show b.rounds = _
    rw [IM.alone_rounds hl]
    show (K1.sendAtS (K1.parW Z.first (wGp Z) 4 msg) : Block S Unit).rounds ++ [] = _
    rw [List.append_nil]
    rfl
  · show b.oracles = _
    rw [IM.alone_oracles hl]
    show (K1.sendAtS (K1.parW Z.first (wGp Z) 4 msg) : Block S Unit).oracles ++ [] = _
    rw [List.append_nil]
    rfl

/-- **A yes of number 356 leaves no mark.** -/
theorem k1_w_noMark (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {blk : Block S ProofFile.Cl}
    (hb : c.blocksInOrder[356]? = some blk) :
    ∀ s rs gs t, blk.decide s rs gs = .ok t → t.failed = none := by
  intro s rs gs t hy
  obtain ⟨-, -, -, b, b', w, hb3, -, -, -, hl⟩ := IM.back_of O
  have hfl := (IM.back_numbers hS hR O).1 3 b hb3
  obtain rfl := Option.some.inj (hfl.symm.trans hb)
  exact ((IM.yes_alone hl (show KindName.K1 ≠ KindName.K7 by decide) s t rs gs).1 hy).2.1

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_w_inScope
#print axioms ProofFile.Honest.K1.k1_w_noMark
