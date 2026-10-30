-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomKeepAll.lean:
THE KEEPING BENEATH room_at_reach, THE WHOLE JOIN: IN THE GOALS' SCOPE, AT
THE PROOF FILE'S OWN FIRST STATE: KeepShares (RoomKeep.lean): ALL THIRTEEN FIELDS ARE PAID;
SO RoomOwes AND THE TWO FIELDS OF FoldFacts ON THE INDEX MASKS' ROOM HAVE NO PREMISE BUT THE SCOPE,
THE OPENING AND "every sub-protocol passes its test on the plan"; AND THE COUNT "303 of the 303
numbers are paid" BY LEAN'S KERNEL, on the written list of places.

  keepShares_paid   in scope, at start := ProofFile.startS Z: KeepShares: thirteen fields are laid in
  roomOwes_paid, room_field_paid, roomEarly_field_paid   THE ENDS: RoomOwes at the fresh ledger's
                    own free count, and the two fields of FoldFacts: the make is paid too
                    (room_make_both, RoomMake.lean)
  owedNumber k, kindAtW k, paidKinds, isLinkEnd k   a number of the keeping; the kind that the
                    written list has at a number; the kinds whose field is paid; a number of a
                    link's batching, of the runs behind it or of its closing's three
  owed_total        303 numbers are the keeping's: by Lean's kernel
  paid_total        all 303 of them are paid: by Lean's kernel

Limits. The count runs over the written list of places (flatPlacesOf linksFull true), by kinds and
by numbers, not by theorems at the chain's own flat list. Nine of the thirteen fields are other
files' (k1, k4, k5, k6, k7, k12, batch, behind, close), k3 stands on another file's lemma
and text, and the make is another file's: called. Laws from accepts: "reached" may be empty.
No soundness statement.

-/
import Johnson.P1L20R.RoomKeepK1
import Johnson.P1L20R.RoomKeepK2
import Johnson.P1L20R.RoomKeepK3
import Johnson.P1L20R.RoomKeepK5
import Johnson.P1L20R.RoomKeepK6K7
import Johnson.P1L20R.RoomKeepK8
import Johnson.P1L20R.RoomKeepK11
import Johnson.P1L20R.RoomEarly
import Johnson.P1L20R.RoomMake
import Johnson.Road.K4.RoomKeepK4
import Johnson.Loose.H2K12.RoomAcross
import Johnson.LPFK9R.RoomHead
import Johnson.LPFK10R.HeadLinkJoins

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block Chain Link KindName)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K1 (free0Of gpOf)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **KeepShares: all thirteen fields.** -/
theorem keepShares_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    KeepShares Z Bs.G₀ c (ProofFile.startS Z) where
  k1 := k1_keeps Z Bs.G₀ c (ProofFile.startS Z)
  k2 := k2_keeps Z Bs.G₀ c (ProofFile.startS Z)
  k3 := k3_keeps Z Bs.G₀ c (ProofFile.startS Z)
  k4 := OnBytes.Road.K4.k4_keeps Z Bs.G₀ c (ProofFile.startS Z)
  k5 := k5_keeps Z Bs.G₀ c (ProofFile.startS Z)
  k6 := k6_keeps Z Bs.G₀ c (ProofFile.startS Z)
  k7 := k7_keeps Z Bs.G₀ c (ProofFile.startS Z)
  k8 := k8_keeps Z Bs.G₀ c (ProofFile.startS Z)
  k11 := k11_keeps Z Bs.G₀ c (ProofFile.startS Z)
  k12 := H2K12.k12_keeps Z Bs.G₀ c (ProofFile.startS Z)
  batch := LPFK9.field_batch_home hS hR O (ProofFile.startS Z)
  behind := LPFK9.field_behind_home hS hR O (ProofFile.startS Z)
  close := LPFK10.room_close_all hS hR O

/-- **RoomOwes.** -/
theorem roomOwes_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    RoomOwes c (ProofFile.startS Z) (free0Of Bs.G₀.first (gpOf Z)) :=
  roomOwes_of_keep hS hR O (room_kept_of_shares hS hR O (keepShares_paid hS hR O))

/-- **The field "room" of FoldFacts.** -/
theorem room_field_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    {X : Type} {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × S}
    (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) :
    ∀ k a p m, Rch k a → (at_ a).2.failed = none →
      (flatPlacesOf linksFull true)[k]? = some p → p.link = some m → 2 ≤ p.piece →
      roomIsB (free0Of Bs.G₀.first (gpOf Z))
        (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) m (at_ a).2 = true :=
  room_field hS hR O hp (roomOwes_paid hS hR O) hRch

/-- **Its twin at a segment's first two places.** -/
theorem roomEarly_field_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    {X : Type} {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × S}
    (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) :
    ∀ k a p m, Rch k a → (at_ a).2.failed = none →
      (flatPlacesOf linksFull true)[k]? = some p → p.link = some m → p.piece < 2 → 0 < m →
      roomIsB (free0Of Bs.G₀.first (gpOf Z))
        (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) m (at_ a).2 = true :=
  roomEarly_field hS hR O hp (roomOwes_paid hS hR O) hRch

end

/-- A number of the keeping. -/
def owedNumber (k : ℕ) : Bool := decide (3 ≤ k) && decide (k < 355) && !isOurs k

/-- The kind that the written list has at a number. -/
def kindAtW (k : ℕ) : Option KindName := ((flatPlacesOf linksFull true)[k]?).map (·.kind)

/-- The kinds whose field is paid. -/
def paidKinds : List KindName := [.K1, .K2, .K3, .K4, .K5, .K6, .K7, .K8, .K11, .K12]

/-- A number of a link's batching, of the runs behind it or of its closing's three. -/
def isLinkEnd (k : ℕ) : Bool :=
  (List.range 25).any fun l => decide (14 * l + nA l + 2 ≤ k) && decide (k ≤ 14 * l + nA l + 6)

set_option maxRecDepth 1000000 in
theorem owed_total : ((List.range 358).filter owedNumber).length = 303 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem paid_total : ((List.range 358).filter fun k =>
    owedNumber k && ((kindAtW k).any (fun K => paidKinds.contains K) || isLinkEnd k)).length =
      303 := by
  decide +kernel

end P1L20

#print axioms P1L20.keepShares_paid
#print axioms P1L20.roomOwes_paid
#print axioms P1L20.room_field_paid
#print axioms P1L20.roomEarly_field_paid
#print axioms P1L20.owed_total
#print axioms P1L20.paid_total
