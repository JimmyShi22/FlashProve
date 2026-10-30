-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Carried.lean: which oracle messages the part of the closing of a segment (K10)
carries, and how many coins each has: of public data alone. This file defines part of the honest prover. Definitions
with code, and tests at a made-up shape; no theorem.

Which. The fold sums over the messages of the rows of the segment's group. From the second segment
on two of these rows are the carrying message's, and its message holds what the closing in front has
left (OnBytes/Iop/Cs.lean, `switchParts`): the folded main row's message and tail; the folded old
mask row's and the folded fresh mask's messages and tails; the kept rows' tails and the kept
members' old pads, as they were. Between them these read every coin of every member of the group in
front and of that closing's fresh mask (at a target with room for them, as every lawful one has). So
the part at segment l carries every oracle message of the groups 0 .. l, and the fresh masks of the
closings 0 .. l - 1. Its own fresh mask it spends. The index-mask message, which goes out last in
the very first sending, behind the first segment's own messages and its fresh mask
(`ReqShape.atStart`), is in no segment's group and is not listed.

The order: segment by segment; in a segment the order of sending (`ReqFrame.first`, `ReqFrame.later`,
OnBytes/Iop/Req.lean): in the first sending the carrying message, the kept messages that are sent
anew, the segment's own messages of moment 0, the fresh mask; then the later moments' sendings.

The counts are made by `msgDue` (Honest/BookRows.lean): an oracle message's coins, of its notice
and the chain's codes: this file counts no coin itself.
  `dueOf`      all coins of a message of a shape, by that function. k: the row variables of the fold that
               spends a fresh mask: read at such a shape alone
  `freshShape` the shape of a fold's fresh mask, as the verifier announces it
  `shapesIn`   a segment's messages' shapes, sending by sending
  `borneIn`, `borneOf`   the list, of a request's shape, the chain's codes, and the addresses of the parts
               that hold the sendings (by segment and moment)
  `borneKnown` a test with code: that function yields a count for every listed message

Limits. Where that function yields nothing (a shape names a code that the chain has not) `dueOf` is ⟨0, 0⟩: `borneKnown`
asks that it does not come to that, for whoever lists the halves. Beyond the shape's groups and links `shapesIn` takes
defaults and still lists messages (its docstring): no test here asks that a segment's number is below the number of
segments. The order is the order of sending. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Half
import Johnson.Desc.ProofFile.Honest.BookRows
import OnBytes.Iop.Req

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Code Codes OracleShape reqGroups)
open OnBytes.Params (ReqShape)

/-- **All coins of an oracle message of a shape**: `msgDue`'s count; ⟨0, 0⟩ where that yields nothing
(`borneKnown` is the test for it). -/
def dueOf (codes : Codes) (k : Nat) (sh : OracleShape) : Due :=
  ((ProofFile.Honest.msgDue codes k ⟨sh, 0⟩).map (·.all)).getD ⟨0, 0⟩

/-- The shape of the fresh mask of a fold with 2^h mask rows. -/
def freshShape (maskCode h : Nat) : OracleShape :=
  { code := OnBytes.noId, mainRows := 0, maskRows := 2 ^ h, maskCode := maskCode, answers := 0 }

/-- The shapes of segment j's oracle messages, sending by sending, each with the row variables of the fold that spends
it, if it is a fresh mask (0 stands there else), each sending with its moment's number. withMask: the fresh mask of the
segment's closing is listed too. Beyond the shape's groups and links the default group and no own message are taken:
from j = 1 on a message of the default shape is then listed, whose count is ⟨0, 0⟩, and `borneKnown` says yes of it:
nothing here asks that j is below the number of segments. -/
def shapesIn (s : ReqShape) (withMask : Bool) (j : Nat) : List (Nat × List (OracleShape × Nat)) :=
  let G := (reqGroups s).getD j {}
  let own := ((s.link[j]?).map (·.messages)).getD []
  let first := (if j == 0 then [] else [G.target.shape]) ++ G.target.kept.toList.map (·.shape) ++
    (own.filter (·.moment == 0)).map (·.shape)
  (0, first.map (·, 0) ++ (if withMask then [(freshShape s.maskCode G.h, G.k)] else [])) ::
    (List.range ((own.map (·.moment)).foldl max 0)).map fun t =>
      (t + 1, ((own.filter (·.moment == t + 1)).map (·.shape)).map (·, 0))

/-- The oracle messages of segment j. sender j t: the part that holds the sending of moment t. -/
def borneIn (s : ReqShape) (codes : Codes) (sender : Nat → Nat → Addr) (withMask : Bool) (j : Nat) :
    List Borne :=
  (shapesIn s withMask j).flatMap fun x =>
    x.2.zipIdx.map fun y => (⟨sender j x.1, y.2, dueOf codes y.1.2 y.1.1⟩ : Borne)

/-- **What the part at segment l carries.** -/
def borneOf (s : ReqShape) (codes : Codes) (sender : Nat → Nat → Addr) (l : Nat) : List Borne :=
  (List.range (l + 1)).flatMap fun j => borneIn s codes sender (decide (j < l)) j

/-- **`msgDue` yields a count for every message that the part at segment l carries.** -/
def borneKnown (s : ReqShape) (codes : Codes) (l : Nat) : Bool :=
  (List.range (l + 1)).all fun j => (shapesIn s (decide (j < l)) j).all fun x =>
    x.2.all fun y => (ProofFile.Honest.msgDue codes y.2 ⟨y.1, 0⟩).isSome

/-! ### Tests at a made-up shape -/

namespace Toy.Carried

/-- Two segments. The first: at moment 0 a message of three rows over the base field with the mask
row, and one of two rows that the next segment reads; at moment 1 a row over the extension field.
The second: one message, with its mask row. One answer a sample. -/
def shape : ReqShape :=
  { (default : ReqShape) with
    code := 0, maskCode := 0, answers := 1
    link := [
      { plain := 0, messages := [
          ⟨{ code := 0, mainRows := 3, mainDeg := 1, maskRows := 1, maskCode := 0, answers := 1 },
            0, 0, 0⟩,
          ⟨{ code := 0, mainRows := 2, mainDeg := 1, maskRows := 0, answers := 1 }, 0, 0, 1⟩,
          ⟨{ code := 0, mainRows := 1, mainDeg := 3, maskRows := 0, answers := 1 }, 0, 1, 0⟩] },
      { plain := 0, messages := [
          ⟨{ code := 0, mainRows := 1, mainDeg := 1, maskRows := 1, maskCode := 0, answers := 1 },
            0, 0, 0⟩] }] }

/-- A code of 8 places with a tail of 3. No lawful plan has it for this shape: a carrying message of
such rows has no room for what a fold leaves (said here without a theorem). The lines here try lists
and counts, which hang on the tails' lengths, the mask code and the shapes alone. -/
def cd : Code := ⟨4, 8, 3⟩
def codes : Codes := { base := #[cd], mask := #[cd] }
def at_ (j t : Nat) : Addr := ⟨⟨1, some j, 1 + t, if j == 0 || t != 0 then .K1 else .K2⟩, 0⟩
def short (l : List Borne) : List (Nat × Nat × Nat × Nat × Nat) :=
  l.map fun m => ((m.sender.place.link.getD 99), m.sender.place.piece, m.msg, m.count.f, m.count.e)

-- the first segment's closing: its three messages; not its own fresh mask. Three tails of three;
-- eight entries and a tail of three · two tails and a pad of three · a tail and a pad of one
#guard short (borneOf shape codes at_ 0) == [(0, 1, 0, 9, 11), (0, 1, 1, 9, 0), (0, 2, 0, 0, 4)]
-- the second's: these, with the first closing's fresh mask as message 2 of the first sending (the
-- first group has 4 + 1 rows in blocks: k = 3, h = 0: seven coefficients and a tail of three); then
-- the carrying message (two tails and a pad of one), the kept message anew, the segment's own
#guard short (borneOf shape codes at_ 1) == [(0, 1, 0, 9, 11), (0, 1, 1, 9, 0), (0, 1, 2, 0, 10),
  (0, 2, 0, 0, 4), (1, 1, 0, 0, 7), (1, 1, 1, 9, 0), (1, 1, 2, 3, 11)]
#guard ((reqGroups shape).toList.map fun G => (G.k, G.h)).take 2 == [(3, 0), (3, 0)]
-- `msgDue` knows every listed shape; with a shape that names a code which the chain has not:
-- no
#guard borneKnown shape codes 0 && borneKnown shape codes 1
#guard !borneKnown shape { base := #[], mask := #[cd] } 0

end Toy.Carried

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.dueOf
#print axioms ProofFile.Honest.K10.freshShape
#print axioms ProofFile.Honest.K10.shapesIn
#print axioms ProofFile.Honest.K10.borneIn
#print axioms ProofFile.Honest.K10.borneOf
#print axioms ProofFile.Honest.K10.borneKnown
#print axioms ProofFile.Honest.K10.Toy.Carried.shape
#print axioms ProofFile.Honest.K10.Toy.Carried.cd
#print axioms ProofFile.Honest.K10.Toy.Carried.codes
#print axioms ProofFile.Honest.K10.Toy.Carried.at_
#print axioms ProofFile.Honest.K10.Toy.Carried.short
