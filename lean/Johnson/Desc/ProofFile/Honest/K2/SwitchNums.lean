-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/SwitchNums.lean: WHICH SEAT, AND WHICH NUMBER, OF THE PLAN's LIST
OF SEATS MESSAGE NUMBER n OF A SWITCH's SENDING HAS. Three definitions on public data; no theorem;
definitions claim nothing.

  `switchSeatIn` ps l n   the first seat of the list ps that stands in the sending "link l, moment
                          0" at the place n there
  `switchNumIn` ps l n    the number that the plan's numbering `P5T.arrOf` ps gives that seat's tree
                          and tenant
  `switchNum` Zp p n      that number at the public part's own list `P5J.At.pseatsAll` Zp and the
                          place's field link

Why so. The seat is read off the plan's own list, by the sending's segment and the member's place in
it: so neither the sending's number nor the declared rounds are letters here. `switchNum` Zp p is
meant as the letter num of `switchMsgLots` (ScriptLots.lean of this folder); the seat's fields j and
t as the letters tree and tenant of `switchPadLots`. `P5J.At.arr` Zp is `P5T.arrOf` at that list: so
at a seat q the number is `P5J.At.arr` Zp q.j q.t by unfolding.

MIND. Where the list has no such seat `switchNumIn` answers the number of keys, as `P5T.arrOf`
itself does where no seat is: one number for all n. Law/SwitchNumsWritten.lean and
Law/SwitchNumsAtHead.lean say that at a place of the kind's list a seat is there, and just one, at
every n below the number of the place's messages. Beyond that number `switchNum` means nothing.
`switchNumIn` hands the seat's tree and tenant to `P5T.arrOf`, which seeks the first holder of that
tree and tenant anew: that this holder has the seat's own key is said in the same two files.

Limits. Definitions. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Half
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2

/-- The first seat of ps in the sending "link l, moment 0", at the place n there. -/
def switchSeatIn (ps : List P5T.PSeat) (l n : Nat) : Option P5T.PSeat :=
  ps.find? fun q => q.seg == some (l, 0) && q.idx == n

/-- The number that the plan's numbering gives that seat; where there is none, the number of keys.
-/
def switchNumIn (ps : List P5T.PSeat) (l n : Nat) : Nat :=
  match switchSeatIn ps l n with
  | some q => P5T.arrOf ps q.j q.t
  | none => ((ps.map P5T.keyOf).eraseDups).length

/-- **The number of message n of the switch at p**, at the public part's own list of seats. -/
def switchNum (Zp : ProofFile.Pub) (p : SwitchPlace) (n : Nat) : Nat :=
  switchNumIn (P5J.At.pseatsAll Zp) p.link n

end ProofFile.Honest.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.switchSeatIn
#print axioms ProofFile.Honest.K2.switchNumIn
#print axioms ProofFile.Honest.K2.switchNum
