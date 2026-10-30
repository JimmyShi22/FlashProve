-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/FirstMemberSent.lean: the index-mask member of the last
chain's test and its sender in the wide filling.
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.

  `firstOfLot`  the sender's job term: the one that K1's lot lays at the first opening
  `first_lot_is_sender`   (i) A LOT OF THE FILLING HAS THAT HALF FIRST, by rfl
  `first_member_rows`   (iii) ACROSS THE TWO TEXTS OF THE RIDE: at a message without main rows the
                 member's rows at a carried stretch are the sender's at its purse, at every data,
                 input and front

(ii), that the message has no main row under the head, is FirstAtHeadW.lean's (AtFullSide/K12/).

Limits.
- `hf`, `he`: that the purse agrees with the stretch on the message's coins are premises: that is
  (h6). THIS MEMBER IS ALL COINS, THE INDEX's MASKS.
- The job of the member is `K1.firstJob`, of the lot `placeJob`: two terms: they have one plan and
  one ride (`first_member_is_sender`, SendersW.lean), not one data: no row reads it.
- At jobW's first member: (ii) and (iii) are not joined here: at k := sent.size - 1, `hm` is (ii),
  `hk` wants a message at all. (ii) stands at `Bs.G₀`, `filling_at_head` at `A.G`: that these are
  one under the head is said in neither file. That no other lot has a half at the first opening's place
  is not said.
- Nothing on what a half plays. No run is named.
- What may be said of this pair on hiding stands in the head of HalfW.lean in this folder.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WMemberSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open Johnson.Prover.Send (shapeAt)

variable {W₀ : Type}

/-- The first opening's plan. -/
abbrev firstParOf (Z : Pub) (G : Ground) : VerifiableInference.Desc.K1.Par :=
  VerifiableInference.Desc.K1.firstPar G.first (VerifiableInference.Desc.K1.gpOf Z)

/-- The sender's job term at the first opening. -/
def firstOfLot {X : Type} (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) :
    K1.SendJob (K1.PlaceIn Inst) X :=
  K1.placeJob (firstParOf Z G) (K1.lotNo o Z ⟨1, some 0, 1, .K1⟩) (K1.firstFold G.first)
    (K1.lotData S Z G)

/-- **(i) Some lot of the filling has the sender's half first.** -/
theorem first_lot_is_sender (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    ∃ M ∈ (onlineProverPartsInUse I o S O).lots, ∃ rest, M.halves Z G =
      K1.placeHalf (inOf (lettersW I Z)) (firstOfLot o S Z G) :: rest :=
  ⟨_, List.mem_cons_self .., _, rfl⟩

/-- **(iii) At a message without main rows the member's rows at a carried stretch are the sender's
at its purse**, at every data, input and front: across the two texts of the ride. -/
theorem first_member_rows {W X Xi : Type} (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground)
    (readers : W → Readers) (at_ : Addr) (fs : Option Nat × Option Nat) (first : Nat)
    (D : RowDataOf Xi) (part : Nat) (w : W) (fr gr : Front X) (v : K1.PlaceIn Xi) (k : Nat)
    (hk : k < (firstParOf Z G).sent.size) (hm : (shapeAt (firstParOf Z G) k).mainRows = 0)
    (St : Stretch) (c : Cs (K1.dueR (firstParOf Z G) (K1.rideOf (K1.firstFold G.first))))
    (hf : ∀ i, i < (K1.dueMsg (firstParOf Z G).codes (shapeAt (firstParOf Z G) k)
        (K1.rideOf (K1.firstFold G.first) k)).f →
      K1.cf c ((K1.startR (firstParOf Z G) (K1.rideOf (K1.firstFold G.first)) k).f + i) = St.f i)
    (he : ∀ i, i < (K1.dueMsg (firstParOf Z G).codes (shapeAt (firstParOf Z G) k)
        (K1.rideOf (K1.firstFold G.first) k)).e →
      K1.ce c ((K1.startR (firstParOf Z G) (K1.rideOf (K1.firstFold G.first)) k).e + i) = St.e i) :
    (memK1 (K1.firstJob S Z G) readers at_ k fs).rows w fr St =
      psOfRows (firstParOf Z G) k (K1.rowsR (firstParOf Z G) (K1.rideOf (K1.firstFold G.first))
        ((K1.placeJob (X := X) (firstParOf Z G) first (K1.firstFold G.first) D part).data v gr)
        c k) := by
  show psOfRows (firstParOf Z G) k (K1.rowsR (firstParOf Z G) (K1.firstRide G.first)
    ((K1.firstJob S Z G : K1.SendJob Readers X).data (readers w) fr)
    (csAt _ (K1.startR (firstParOf Z G) (K1.firstRide G.first) k) St) k) = _
  rw [firstRide_eq, rowsR_no_main _ _ _ ((K1.placeJob (X := X) (firstParOf Z G) first
    (K1.firstFold G.first) D part).data v gr) _ k hm, rowsR_csAt _ _ _ k hk St c hf he]

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.firstOfLot
#print axioms ProofFile.Honest.K12.AtProof.first_lot_is_sender
#print axioms ProofFile.Honest.K12.AtProof.first_member_rows
