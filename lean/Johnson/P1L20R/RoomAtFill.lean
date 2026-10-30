-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomAtFill.lean:
THE TWO FIELDS OF FoldFacts ON THE INDEX MASKS' ROOM (room, roomEarly), AT
THE TWO NUMBERS THAT THE CLOSED FoldData OF THE COMPOSED MEANING'S HEAD HAS: free0 :=
FillP1.free0Of Z.first.codes M ix at M := the first proof chain's listed oracle messages' shapes,
fvs := FillP1.fvsAt Z: where the public test FillP1.startB accepts at M and ix. In the goals' scope,
at the proof file's own first state. The premises: room_field_paid's (RoomKeepAll.lean) and
that accept.

  room_at_fill, roomEarly_at_fill   the two fields, where the condition "reached" gives Reach over
                    the chain's own flat list
  room_at_fill_below, roomEarly_at_fill_below   the like where it gives Reach over the wrapped list
                    (c.blocksInOrder.map below), by reach_raw (Johnson/Top/H0/Walk/Reach.lean)

By free0_is (Free0Is.lean): the two terms for the fresh ledger's free count are one number
where startB accepts; fvsAt is fvsOf by its definition.
Limits. RoomKeepAll.lean's: laws from accepts: "reached" may be empty. startB's accept is a premise.
No soundness statement.

-/
import Johnson.P1L20R.RoomKeepAll
import Johnson.P1L20R.Free0Is
import Johnson.Desc.K12.Door.MsgShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.FillP1 (startB fvsAt)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.Desc.Sound (linksFull below)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The field "room" at the head's closed numbers.** -/
theorem room_at_fill (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    {X : Type} {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × S}
    (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) {ix : ℕ}
    (hB : startB Z (msgsOfChain Z.made.proof.1) ix = true) :
    ∀ k a p m, Rch k a → (at_ a).2.failed = none →
      (flatPlacesOf linksFull true)[k]? = some p → p.link = some m → 2 ≤ p.piece →
      roomIsB (VerifiableInference.Desc.First.FillP1.free0Of Z.first.codes
        (msgsOfChain Z.made.proof.1) ix) (fvsAt Z) m (at_ a).2 = true := by
  rw [← free0_is O hB]
  exact room_field_paid hS hR O hp hRch

/-- **Its twin at a segment's first two places.** -/
theorem roomEarly_at_fill (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    {X : Type} {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × S}
    (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) {ix : ℕ}
    (hB : startB Z (msgsOfChain Z.made.proof.1) ix = true) :
    ∀ k a p m, Rch k a → (at_ a).2.failed = none →
      (flatPlacesOf linksFull true)[k]? = some p → p.link = some m → p.piece < 2 → 0 < m →
      roomIsB (VerifiableInference.Desc.First.FillP1.free0Of Z.first.codes
        (msgsOfChain Z.made.proof.1) ix) (fvsAt Z) m (at_ a).2 = true := by
  rw [← free0_is O hB]
  exact roomEarly_field_paid hS hR O hp hRch

/-- "room", where "reached" gives Reach over the wrapped list. -/
theorem room_at_fill_below (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    {X : Type} {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × S}
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (at_ a)) {ix : ℕ}
    (hB : startB Z (msgsOfChain Z.made.proof.1) ix = true) :
    ∀ k a p m, Rch k a → (at_ a).2.failed = none →
      (flatPlacesOf linksFull true)[k]? = some p → p.link = some m → 2 ≤ p.piece →
      roomIsB (VerifiableInference.Desc.First.FillP1.free0Of Z.first.codes
        (msgsOfChain Z.made.proof.1) ix) (fvsAt Z) m (at_ a).2 = true :=
  room_at_fill hS hR O hp (fun k a h => reach_raw (hRch k a h)) hB

/-- "roomEarly", where "reached" gives Reach over the wrapped list. -/
theorem roomEarly_at_fill_below (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    {X : Type} {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × S}
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (at_ a)) {ix : ℕ}
    (hB : startB Z (msgsOfChain Z.made.proof.1) ix = true) :
    ∀ k a p m, Rch k a → (at_ a).2.failed = none →
      (flatPlacesOf linksFull true)[k]? = some p → p.link = some m → p.piece < 2 → 0 < m →
      roomIsB (VerifiableInference.Desc.First.FillP1.free0Of Z.first.codes
        (msgsOfChain Z.made.proof.1) ix) (fvsAt Z) m (at_ a).2 = true :=
  roomEarly_at_fill hS hR O hp (fun k a h => reach_raw (hRch k a h)) hB

end

end P1L20

#print axioms P1L20.room_at_fill
#print axioms P1L20.roomEarly_at_fill
#print axioms P1L20.room_at_fill_below
#print axioms P1L20.roomEarly_at_fill_below
