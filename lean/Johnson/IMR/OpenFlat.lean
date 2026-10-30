-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/OpenFlat.lean: Johnson/IMR/OpenWalk.lean's WALK CARRIED FROM THE PART IN
FRONT OF THE LAST LINK's END TO THE WHOLE FIRST CHAIN, at an opening's own letters
(Johnson/IMR/SeatOpen.lean).
  open_flat: SeatKeeps R okB okP and SeatBack R (Johnson/IMR/SeatKeeps.lean): every entry of c.blocksInOrder
    THAT
    PASSES ITS OWN TEST ON THE LIST OF ROUNDS keeps R.
  open_fold_all: so a fold over the first k entries of c.blocksInOrder, AT EVERY k, from any state of the
    verifier: under "every entry of c.blocksInOrder passes that test".
WHERE SeatBack LIES TODAY: at the sentences on the state's list of commitment trees
(seatBack_sentence, Johnson/IMR/BookSeat.lean: "in order" with k12_ordered,
Johnson/IMR/BookPaid.lean; BookFits with
k12_fits, Johnson/IMR/BookFitsPaid.lean), at the codes (seatBack_codes, Johnson/IMR/CodesSeat.lean).
At PlacesStay
under a premise on kind K12 (seatBack_places, Johnson/IMR/BookFitsSeat.lean). Not at RecRel, OwnRel,
Grows,
"has".
OBJECT: ProofFile.onlineDescription's value, at every o. No soundness.
-/
import Johnson.IMR.OpenWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Pub Cl)

variable {R : S → S → Prop} {okB : Array Stages.LinkH → Prop} {okP : K2.HeadPar → Prop}
  {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem open_flat (H : SeatKeeps R okB okP) (Hb : SeatBack R)
    (O : IM.Open o pol lay KL F Z Bs base c A B) (hB : okB Z.p.built.links)
    (hP : ∀ l Q, P1K2.pureLetters Bs.G₀ l = some Q → okP Q) :
    ∀ b ∈ c.blocksInOrder, b.planOk = true → Decides R b := by
  have hall := all_of_made (IM.base_made O.made).2.2.2
  have h0 := pub_firstTree (o := o) (pol := pol) (lay := lay) (KL := KL) O.pub
  have K₀ : LotsKeep R (ProofFile.pureSeat o Z).lots Bs.G₀ := thePure_keeps H Z hB h0 Bs.G₀ hP
  have Ka : LotsAll R (ProofFile.pureSeat o Z).lots Bs.G₀ := thePure_all H Hb Z hB h0 Bs.G₀ hP
  intro b hb hp
  rw [flat_eq (chainBy_noFront O.chain)] at hb
  rcases List.mem_append.1 hb with k | k
  · exact (open_front H O hB hP).2 b k
  · exact chainBy_back H.trans O.chain (partsAt_baseAll H.refl Ka hall O.places)
      (partsAt_frames K₀ hall) b k hp

theorem open_fold_all (H : SeatKeeps R okB okP) (Hb : SeatBack R)
    (O : IM.Open o pol lay KL F Z Bs base c A B) (hB : okB Z.p.built.links)
    (hP : ∀ l Q, P1K2.pureLetters Bs.G₀ l = some Q → okP Q)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (k : Nat) {ft : Nat} {s : S} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r) : R s r.1 :=
  Keeps.foldBlocks_keeps R H.refl H.trans ft _
    (fun b hb => open_flat H Hb O hB hP b (List.mem_of_mem_take hb)
      (hp b (List.mem_of_mem_take hb))) s rs cols r h

#print axioms open_flat
#print axioms open_fold_all

end Meaning.K2
