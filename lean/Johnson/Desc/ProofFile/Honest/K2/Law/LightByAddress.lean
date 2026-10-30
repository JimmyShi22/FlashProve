-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LightByAddress.lean: the kind "the code switch" (K2): THE LOT's
PUBLIC TEST ON A FILLING (`publicOk`, Honest/K2/Sim.lean) AT THE SWITCHES' OWN DATA JOINED TO THE
SHARED SENDING's (`withSwitchData` S (`K1.lotData` S)): THAT FILLING IS FOUR DATA JOINED BY ADDRESS,
AND THE TEST's YES FOLLOWS FROM SIX PUBLIC TESTS: ONE FOR EACH DATUM, AT ITS OWN ADDRESSES ALONE,
ONE THAT EVERY MESSAGE HAS AN ADDRESS, AND ONE ON THE SWITCH's OWN SENDING. Definitions with code;
two statements with their proofs.

  `mineSwitch`, `mineFirst`, `mineDigits`, `mineReads`   whose an address is: a switch's own seat ·
                    else the opening's sender's · else a seat of the array "BZ" · else the rest.
                    Each address is just one's
  `addressed`       every own message of every segment of the list has an address at the place
  `lightAt`         the light test on a message (`arraysLaidLight`, LaidLight.lean of this folder)
                    at ONE datum, asked at the own messages whose address a given test calls its own
  `ownShare`        of each own message of the switch's own sending: its address has a switch's
                    seat, the light test says yes at the switches' own data, and that data is ready
                    there at no challenge
  `lotData_lays`    where the shared sending's data lay an element, by address
  `publicOk_of_six`   THE SPLIT

By: `publicOk_with`, `arraysLaidLight_lays` (PublicAtJoined.lean of this folder).

Limits. ONE WAY ALONE, AS THE LIGHT TEST IS: its no means nothing. THE SIX TESTS ARE PREMISES: SHOWN
HERE AT NO PLACE AND NO FILLING. `lightAt` says yes where no address is its datum's. Of the six, the
test at the reads' data alone reads the public instance. Nothing on what the data hold: the light
test reads where a datum lays an element, not what. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtJoined
import Johnson.Desc.ProofFile.Honest.K1.LotData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open OnBytes.HonestTrace (Sz seatsOf mineOf)
open OnBytes.HonestTrace.U3 (u3RowsOf)

/-- The address has a seat among the switches' own. -/
def mineSwitch (Z : Pub) (G : Ground) (a : MsgAddr) : Bool := (switchSeat Z G a).isSome

/-- It has none, and its sender is the opening's. -/
def mineFirst (Z : Pub) (G : Ground) (a : MsgAddr) : Bool :=
  !mineSwitch Z G a && a.sender == K1.firstAddr

/-- Neither, and it is a seat's of the array "BZ". -/
def mineDigits (Z : Pub) (G : Ground) (a : MsgAddr) : Bool :=
  !mineSwitch Z G a && !(a.sender == K1.firstAddr) && mineOf (seatsOf Z G "BZ") a

/-- None of the three. -/
def mineReads (Z : Pub) (G : Ground) (a : MsgAddr) : Bool :=
  !mineSwitch Z G a && !(a.sender == K1.firstAddr) && !mineOf (seatsOf Z G "BZ") a

/-- **Every own message of every segment of the list has an address.** -/
def addressed (p : SwitchPlace) (segs : List SegmentPub) : Bool :=
  segs.zipIdx.all fun y =>
    (y.1.ownShapes (y.2 == 0)).zipIdx.all fun s => (p.addrs y.2 s.2).isSome

/-- **The light test at one datum, at the own messages whose address is `mine`.** -/
def lightAt (D : RowData) (mine : MsgAddr → Bool) (lay : OnBytes.Params.ReqLayout)
    (p : SwitchPlace) (segs : List SegmentPub) : Bool :=
  segs.zipIdx.all fun y =>
    (y.1.ownShapes (y.2 == 0)).zipIdx.all fun s =>
      (p.addrs y.2 s.2).all fun a =>
        !mine a || arraysLaidLight D lay y.1.sizes.codes s.1 y.2 s.2 a

/-- **The switch's own sending's share.** -/
def ownShare (S : Sz) (Z : Pub) (G : Ground) (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace) :
    Bool :=
  (p.others.toList.take (p.others.size - 1)).zipIdx.all fun n =>
    mineSwitch Z G (p.ownAddr n.2) &&
      arraysLaidLight (switchData S Z G) lay p.sizes.codes n.1.shape p.link n.2 (p.ownAddr n.2) &&
      (switchData S Z G).readyAt [] (p.ownAddr n.2)

namespace Law

/-- **Where the shared sending's data lay an element, by address.** -/
theorem lotData_lays (S : Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst) (a : MsgAddr) :
    (K1.lotData S Z G x).lays a =
      if a.sender == K1.firstAddr then (K1.firstFill S G.first).lays a
      else if mineOf (seatsOf Z G "BZ") a then (K1.digitsFill Z G (K3.matsOwn G.W)).lays a
      else (u3RowsOf Z G x).lays a := rfl

/-- **THE SPLIT.** -/
theorem publicOk_of_six (S : Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst)
    (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace) (segs : List SegmentPub)
    (ha : addressed p segs = true)
    (h1 : lightAt (switchData S Z G) (mineSwitch Z G) lay p segs = true)
    (h2 : lightAt (K1.firstFill S G.first) (mineFirst Z G) lay p segs = true)
    (h3 : lightAt (K1.digitsFill Z G (K3.matsOwn G.W)) (mineDigits Z G) lay p segs = true)
    (h4 : lightAt (u3RowsOf Z G x) (mineReads Z G) lay p segs = true)
    (ho : ownShare S Z G lay p = true) :
    publicOk (withSwitchData S (K1.lotData S) Z G) lay p segs x = true := by
  refine publicOk_with S (K1.lotData S) Z G x lay p segs (fun y hy s hs => ?_) fun n hn => ?_
  · have get : ∀ {D : RowData} {mine : MsgAddr → Bool}, lightAt D mine lay p segs = true →
        ∀ a, p.addrs y.2 s.2 = some a → mine a = true →
          arraysLaidLight D lay y.1.sizes.codes s.1 y.2 s.2 a = true := by
      intro D mine hD a ea hm
      have t := List.all_eq_true.1 (List.all_eq_true.1 hD y hy) s hs
      rw [ea] at t
      have t' : (!mine a || arraysLaidLight D lay y.1.sizes.codes s.1 y.2 s.2 a) = true := t
      rw [hm] at t'
      exact t'
    obtain ⟨a, ea⟩ := Option.isSome_iff_exists.1
      (List.all_eq_true.1 (List.all_eq_true.1 ha y hy) s hs)
    refine ⟨a, ea, ?_⟩
    by_cases c1 : (switchSeat Z G a).isSome = true
    · rw [if_pos c1]
      exact get h1 a ea c1
    · rw [if_neg c1]
      have n1 : mineSwitch Z G a = false := Bool.eq_false_iff.2 c1
      by_cases c2 : (a.sender == K1.firstAddr) = true
      · rw [arraysLaidLight_lays (D' := K1.firstFill S G.first)
          (by rw [lotData_lays, if_pos c2])]
        exact get h2 a ea (by unfold mineFirst; rw [n1, c2]; rfl)
      · have n2 : (a.sender == K1.firstAddr) = false := Bool.eq_false_iff.2 c2
        by_cases c3 : mineOf (seatsOf Z G "BZ") a = true
        · rw [arraysLaidLight_lays (D' := K1.digitsFill Z G (K3.matsOwn G.W))
            (by rw [lotData_lays, if_neg c2, if_pos c3])]
          exact get h3 a ea (by unfold mineDigits; rw [n1, n2, c3]; rfl)
        · have n3 : mineOf (seatsOf Z G "BZ") a = false := Bool.eq_false_iff.2 c3
          rw [arraysLaidLight_lays (D' := u3RowsOf Z G x)
            (by rw [lotData_lays, if_neg c2, if_neg c3])]
          exact get h4 a ea (by unfold mineReads; rw [n1, n2, n3]; rfl)
  · have t := List.all_eq_true.1 ho n hn
    rw [Bool.and_eq_true, Bool.and_eq_true] at t
    exact ⟨t.1.1, t.1.2, t.2⟩

end Law

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.mineSwitch
#print axioms ProofFile.Honest.K2.mineFirst
#print axioms ProofFile.Honest.K2.mineDigits
#print axioms ProofFile.Honest.K2.mineReads
#print axioms ProofFile.Honest.K2.addressed
#print axioms ProofFile.Honest.K2.lightAt
#print axioms ProofFile.Honest.K2.ownShare
#print axioms ProofFile.Honest.K2.Law.lotData_lays
#print axioms ProofFile.Honest.K2.Law.publicOk_of_six
