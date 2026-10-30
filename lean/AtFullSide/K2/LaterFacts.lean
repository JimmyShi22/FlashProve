-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/LaterFacts.lean: closed facts by Lean's kernel on the two later senders of a segment.

1. laterOk, laterW: at each written place and each later message of the segment that it closes: the
   address of the own message, its field, its kind, that the sender has a message, how much its data
   has heard, and the order of the rounds.
2. laterCarried, laterCarriedW: at the written entries: the entry that a switch carries for that
   message names the sender, the start and the message's count.

Limits. The facts run in Lean's kernel and no independent checker replays them here. The controls on
laterOk bend the address and the hearing; the limbs on the field, the kind and the order of rounds
have none. The control on laterCarried bends the entry's number alone. The written entries are those
of rawAheadW, at mergesByName's merges. The full size and the format's second hash function alone.
-/
import AtFullSide.K2.CarriedAtTheBook
import AtFullSide.K2.HeardAtSwitches
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNo
import Johnson.Unfolds.SplitOn
import Johnson.Unfolds.SliceFoldl

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open VerifiableInference.Desc.K1 (noL placeL)
open Johnson.Prover.Send (shapeAt)
open Johnson.G (layoutFull)
open OnBytes.HonestTrace.U3.Fit (seatsW)
open ProofFile.Honest
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law
open AtFullSide.K14 (rawAheadW rawSegW)

/-- The address of message 0 of the later sender at link m; da bends the number for a control. -/
def laterAddr (m : Nat) (d : Bool) (da : Nat) : MsgAddr := ⟨⟨(placeL m d).place, 0⟩, da⟩

/-- The number, among the own messages of segment m, of the later message q. -/
def laterOwnNo (m : Nat) (Sg : SegmentPub) (q : Nat) : Nat :=
  (Sg.sent.headD #[]).size - 1 - (if m = 0 then 0 else 1 + Sg.sizes.kept.length) + q

/-- **A PUBLIC TEST** at a written place and a later message q of the segment that it closes. da and
dh bend the address and the hearing for a control; 0 in earnest. -/
def laterOk (da dh : Nat) (p : SwitchPlace) (q : Nat) : Bool :=
  (segsW[p.link - 1]?).any fun Sg =>
    decide (p.link - 1 < 25) &&
    decide (p.addrs (p.link - 1) (laterOwnNo (p.link - 1) Sg q) =
      some (laterAddr (p.link - 1) (q == 1) da)) &&
    (((Sg.ownShapes (p.link - 1 == 0)).getD (laterOwnNo (p.link - 1) Sg q) {}).mainDeg ==
      (shapeAt (placeL (p.link - 1) (q == 1)) 0).mainDeg) &&
    decide ((placeL (p.link - 1) (q == 1)).place.kind ≠ .K2) &&
    decide (0 < (placeL (p.link - 1) (q == 1)).sent.size) &&
    decide (heardAll (seatsW "U3") (seatsW "BZ") layoutFull heardRngW
        (laterAddr (p.link - 1) (q == 1) 0) + dh ≤
      roundsCutW (noL (p.link - 1) (q == 1))) &&
    decide (roundsCutW (noL (p.link - 1) (q == 1)) ≤ roundsCutW (switchNo p))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The test says yes at each written place**; two controls: with the address bent, and with the
hearing bent, it says no at each. -/
theorem laterW : (placesW.all fun p => (List.range 2).all fun q => laterOk 0 0 p q) = true ∧
    (placesW.all fun p => (List.range 2).all fun q => !laterOk 1 0 p q) = true ∧
    (placesW.all fun p => (List.range 2).all fun q => !laterOk 0 100000 p q) = true := by
  decide +kernel

/-- **A PUBLIC TEST** at a list of entries and a written place: among the entries carried to the
switch's part, those behind the segments in front and behind the first sending of the segment that
it closes are the two later messages: owner, start and count. b bends the entry's number for a
control; 0 in earnest. -/
def laterCarried (es : List Ahead) (b : Nat) (p : SwitchPlace) : Bool :=
  (segsW[p.link - 1]?).any fun Sg => (List.range 2).all fun q =>
    entryRunIs ((es.filter fun e => e.spender == ⟨p.place, 0⟩).filter fun e => !e.once)
      (((segsW.take (p.link - 1)).map (·.messages)).sum + ((Sg.sent.headD #[]).size - 1) + 1 + q + b)
      ⟨(placeL (p.link - 1) (q == 1)).place, 0⟩
      (K1.startR (placeL (p.link - 1) (q == 1)) (K1.rideOf none) 0)
      (K1.dueMsg (placeL (p.link - 1) (q == 1)).codes (shapeAt (placeL (p.link - 1) (q == 1)) 0)
        (K1.rideOf none 0))

/-- The test reads the written book as it reads the list. -/
theorem laterCarried_lit {b : Nat} {p : SwitchPlace} (hp : p ∈ placesW) :
    laterCarried rawAheadW b p = laterCarried carriedLitA b p := by
  have e := carry_at_place hp
  simp only [carryOf] at e
  simp only [laterCarried, e]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By Lean's kernel, at the list. -/
theorem laterCarriedLitW : placesW.all (laterCarried carriedLitA 0) = true := by
  decide +kernel

/-- **At the written entries the test says yes at each written place.** -/
theorem laterCarriedW : placesW.all (laterCarried rawAheadW 0) = true :=
  (all_congr_mem fun _ hp => laterCarried_lit hp).trans laterCarriedLitW

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By Lean's kernel, at the list. -/
theorem laterCarriedNextLitW : (placesW.all fun p => !laterCarried carriedLitA 1 p) = true := by
  decide +kernel

/-- A control: at the entry one further it says no at each written place. -/
theorem laterCarriedW_next : (placesW.all fun p => !laterCarried rawAheadW 1 p) = true :=
  (all_congr_mem fun _ hp => by rw [laterCarried_lit hp]).trans laterCarriedNextLitW

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.laterAddr
#print axioms AtFullSide.K2.laterOwnNo
#print axioms AtFullSide.K2.laterOk
#print axioms AtFullSide.K2.laterW
#print axioms AtFullSide.K2.laterCarried
#print axioms AtFullSide.K2.laterCarriedW
#print axioms AtFullSide.K2.laterCarriedW_next
