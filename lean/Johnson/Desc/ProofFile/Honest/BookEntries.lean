-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookEntries.lean: the third of the files that compute the book of
coins (`ProverCoinCounts`, Honest/Frame.lean): the entries by which a part spends coins of another part: who
spends which range of whose oracle message. From public data alone: a description's list of
sub-protocols, and where an oracle message's entries begin among its sender's coins
(Honest/BookRows.lean). It names no prover's side. Executable definitions, and tests at made-up
lists; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

What is spent, by the format's pages.
  a segment's mask row   every scalar of a segment's own rounds has a number, from 0, in the order
     of sending, and the mask row has an entry for each number (docs/format/11-1-machinery.md,
     "Scalars and their numbers"): the part that sends the scalars number j to j + s - 1 spends the
     entries of these numbers
  the index-mask message   its free entries are taken by increasing number, each once: at a merge
     the end value is put under the next of them, and the mask row's entry of that scalar's number
     is added to no scalar that is sent
  a fold's fresh table   the fold spends its 2k + 1 coefficients: the table's first coins

The ranges of one part, by the names of its rounds (the cut is that of Honest/BookOf.lean).
  a masked sumcheck   "sum": all its scalars but those of "PSC values"; "ends": these
  a fold   "fold": 2k + 1, where its "FOLD epsilon" sends no root of its own
  any other round with scalars of the segment's own   "scalars"
A round whose name is in `frameNames` has no number and spends nothing of the mask row.

  1  `MsgAt`, `Want`, `Want.entry`   an oracle message as an owner; a range that is wanted; the
     entry
  2  `PartAt`, `planParts`, `PartAt.ownScalars`, `PartAt.endScalars`   a sub-protocol's parts, with
     names and scalars
  3  `segmentWants`   a segment's ranges
  4  `Want.free`, `wantsFree`   an executable test: every range lies within its message's free
     entries
  5  `ownerOf`, `isMaskRowMsg`, `isIndexMaskMsg`   an oracle message as an owner, from the library's
     list of sendings

Which parts are merges is not read from the names: it is an argument (`merges`): public data that
the caller supplies, by address.

Limits.
  * The entries by which a part carries a whole message are not computed here.
  * A fold's entries are not computed here.
  * A sumcheck outside a segment (the one that spends the index-mask message alone) is not computed
    here.
  * That each scalar is put under the entry of its own number is the format's rule, assumed here:
    nothing here compares it with a program.
  * `ownerOf` takes the number k of a fold's rounds as `(foldK …).getD 0`: where no fold follows
    the sending, k is 0, and a fresh table in front of the message is counted at one coefficient;
    `ownerOf` does not return `none` for that. Where the sending is no switch, `rowsIn`
    (Honest/BookRows.lean) and `foldEntries` (Honest/BookFolds.lean) return an error there; they
    leave the switches out, and `ownerOf` does not.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookRows
import Johnson.Desc.ProofFile.Honest.ForKinds
import OnBytes.Iop.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

variable {S Cl : Type}

/-! ## 1 A range that is wanted -/

/-- **An oracle message as an owner of entries.** -/
structure MsgAt where
  /-- one of the owners' names of Honest/ForKinds.lean -/
  name : String
  /-- the part that sends it -/
  owner : Addr
  /-- where its entries begin among that part's coins (`maskStart`) -/
  base : Due
  /-- how many of its entries are free: those in front of the pad's first place, in the order in
  which the format takes them -/
  free : Nat
  deriving DecidableEq

/-- **One range that a part spends.** `number`: the first entry's RANK, from 0, among the message's
entries in the order in which the format takes them. It is the number that the verifier's side gives
the entry (`nextEntry`, Johnson/Desc/First/Pend/Row.lean, passes over numbers that name no row) just
where the message's mask rows are a power of two in number. -/
structure Want where
  spender : Addr
  use : String
  msg : MsgAt
  number : Nat
  count : Nat
  deriving DecidableEq

/-- **The book's entry.** -/
def Want.entry (w : Want) : Ahead :=
  ⟨runName w.msg.name w.spender w.use, w.msg.owner, w.msg.base.plus ⟨0, w.number⟩, ⟨0, w.count⟩,
    w.spender, true⟩

/-! ## 2 A sub-protocol's parts -/

/-- A part by what the plan says of its rounds: each round's name and number of scalars. -/
structure PartAt where
  addr : Addr
  rounds : List (String × Nat)
  deriving DecidableEq

/-- A list cut into consecutive lists of given lengths. -/
def stretchesBy {α : Type} : List α → List Nat → List (List α)
  | _, [] => []
  | l, k :: ks => l.take k :: stretchesBy (l.drop k) ks

/-- **A sub-protocol's parts**, by the cut of Honest/BookOf.lean. -/
def planParts (b : Block S Cl) : List PartAt :=
  (stretchesBy (b.rounds.map fun r => (r.entry.name, scalarsIn r)) (partsCut b)).zipIdx.map fun x =>
    ⟨⟨b.place, x.2⟩, x.1⟩

/-- The scalars of a part's rounds that are the segment's own. -/
def PartAt.ownScalars (p : PartAt) : Nat :=
  p.rounds.foldl (fun n r => if frameNames.contains r.1 then n else n + r.2) 0

/-- The scalars of its rounds "PSC values". -/
def PartAt.endScalars (p : PartAt) : Nat :=
  p.rounds.foldl (fun n r => if r.1 == "PSC values" then n + r.2 else n) 0

/-- It is a masked sumcheck. -/
def PartAt.isSum (p : PartAt) : Bool := p.rounds.head?.map (·.1) == some "PSC epsilon"

/-! ## 3 A segment -/

/-- One part's ranges. `j`: the number of its first scalar in the segment. `t`: the next free entry
of the index-mask message. It returns the ranges and the next t. -/
def partWants (row idx : MsgAt) (merge : Bool) (p : PartAt) (j t : Nat) : List Want × Nat :=
  let s := p.ownScalars
  let n := p.endScalars
  if s == 0 then ([], t)
  else if !p.isSum then ([⟨p.addr, "scalars", row, j, s⟩], t)
  else if n == 0 then ([⟨p.addr, "sum", row, j, s⟩], t)
  else if merge then ([⟨p.addr, "sum", row, j, s - n⟩, ⟨p.addr, "ends", idx, t, n⟩], t + n)
  else ([⟨p.addr, "sum", row, j, s - n⟩, ⟨p.addr, "ends", row, j + (s - n), n⟩], t)

/-- Parts one after another. -/
def partsWants (row idx : MsgAt) (merges : List Addr) :
    List PartAt → Nat → Nat → List Want × Nat
  | [], _, t => ([], t)
  | p :: ps, j, t =>
    let x := partWants row idx (merges.contains p.addr) p j t
    let y := partsWants row idx merges ps (j + p.ownScalars) x.2
    (x.1 ++ y.1, y.2)

/-- **A segment's ranges**: those of the sub-protocols of a list that are in link number l, in their
order. `row`: the segment's mask row. `idx`: the index-mask message. `merges`: the parts whose end
values are put under the index-mask message. `t`: that message's next free entry. -/
def segmentWants (bs : List (Block S Cl)) (l : Nat) (row idx : MsgAt) (merges : List Addr)
    (t : Nat) : List Want × Nat :=
  partsWants row idx merges ((bs.filter fun b => b.place.link == some l).flatMap planParts) 0 t

/-! ## 4 An executable test -/

/-- The range lies within its message's free entries. -/
def Want.free (w : Want) : Bool := decide (w.number + w.count ≤ w.msg.free)

/-- **Every range lies within one message's free entries, and no two of one message meet.** -/
def wantsFree (ws : List Want) : Bool :=
  ws.all (·.free) && ws.zipIdx.all fun a => ws.zipIdx.all fun b =>
    a.2 == b.2 || a.1.msg != b.1.msg || !meets a.1.number a.1.count b.1.number b.1.count

/-! ## 5 An oracle message as an owner, from the library's list of sendings -/

/-- **The oracle message of a sending that meets a test, as an owner.** `label`: the sending's, as
the library lists it. `pick`: the first message of that sending that meets it. `later`: as at
`rowsIn`. Its free entries: the programs' own count, by a call: `Send.freeMaskEntries`
(OnBytes/Iop/Send.lean) at the message's mask rows, its mask code's length and its answers: all
below the pad's first place, which is at the end of the last row; in an entry's number the row's
number is low. `none` where there is no such sending or message, or `maskStart` returns `none`.
Where no fold follows, k is taken as 0; `rowsIn` returns an error there. -/
def ownerOf (name : String) (bs : List (Block S Cl)) (c : Johnson.G.ChainSends)
    (later : List Fmt.DeclaredRound) (label : String) (pick : OnBytes.OracleNotice → Bool) :
    Option MsgAt :=
  (((seedRounds bs).zip c.sends).find? fun x => x.2.label == label).bind fun x =>
    let j := x.2.sent.findIdx pick
    let k := (foldK ((bs.flatMap (·.rounds) ++ later).drop (x.1 + 1))).getD 0
    (addrOfRound bs x.1).bind fun a => (maskStart c.codes k x.2.sent j).bind fun st =>
      (x.2.sent[j]?.bind fun n => (msgDue c.codes k n).map fun _ =>
        OnBytes.Send.freeMaskEntries n.shape.maskRows
          (c.codes.mask.getD n.shape.maskCode default).ell n.shape.answers).map
        fun free => ⟨name, a, st, free⟩

/-- The message that holds a segment's mask row: main rows and mask rows. -/
def isMaskRowMsg (n : OnBytes.OracleNotice) : Bool :=
  n.shape.mainRows != 0 && n.shape.maskRows != 0

/-- The index-mask message: mask rows alone, with a sample. -/
def isIndexMaskMsg (n : OnBytes.OracleNotice) : Bool :=
  n.shape.mainRows == 0 && n.shape.maskRows != 0 && n.shape.answers != 0

/-! ### Tests at made-up lists -/

def toyRow : MsgAt := ⟨maskRowRun, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨15, 4⟩, 20⟩
def toyIdx : MsgAt := ⟨indexMaskRun, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨15, 40⟩, 5⟩

/-- A sub-protocol by its rounds' names and bytes. -/
def toyBlock (piece : Nat) (kind : VerifiableInference.Desc.KindName) (rs : List (String × Nat)) :
    Block Unit Unit :=
  { name := "toy", place := ⟨1, some 0, piece, kind⟩, planOk := true
    rounds := rs.map fun r => { entry := { name := r.1, msg := r.2 } }
    oracles := rs.map fun _ => [], before := [], decide := fun s _ _ => .ok s
    claims := [], after := [] }

/-- A round by itself with two scalars; a sumcheck with ends (1 + 2 + 2 scalars, 3 end values); the
frame's reply; a merge (1 + 2 scalars, 1 end value). -/
def toySeg : List (Block Unit Unit) :=
  [toyBlock 2 .K3 [("LKP", 48), ("PSC epsilon", 24), ("PSC round", 48), ("PSC Y", 48),
      ("PSC values", 72)],
   toyBlock 3 .K7 [("REPLY", 24)],
   toyBlock 4 .K11 [("PSC epsilon", 24), ("PSC round", 48), ("PSC values", 24)]]

def toyWants : List Want × Nat :=
  segmentWants toySeg 0 toyRow toyIdx [⟨⟨1, some 0, 4, .K11⟩, 0⟩] 2

-- use, owner's name, number, count: the merge's end value takes the index-mask message's next free
-- entry, and its own number in the segment (13) is spent by nobody; the reply has no number
#guard toyWants.1.map (fun w => (w.use, w.msg.name == maskRowRun, w.number, w.count)) ==
  [("scalars", true, 0, 2), ("sum", true, 2, 5), ("ends", true, 7, 3), ("sum", true, 10, 3),
    ("ends", false, 2, 1)]
#guard toyWants.2 == 3
-- the numbers add up to the count of the segment's scalars by Honest/BookOf.lean
#guard segmentScalars toySeg 0 == 14
-- the entry: the name, the owner, the start among the owner's coins, the count, spent
#guard (toyWants.1.map (·.entry))[1]?.map (fun e => (e.name, e.start, e.count, e.once)) ==
  some (runName maskRowRun ⟨⟨1, some 0, 2, .K3⟩, 1⟩ "sum", ⟨15, 6⟩, ⟨0, 5⟩, true)
-- the test: true here; false where the row has fewer free entries than the segment has scalars;
-- false where two ranges meet
#guard wantsFree toyWants.1
#guard !wantsFree (segmentWants toySeg 0 { toyRow with free := 12 } toyIdx
  [⟨⟨1, some 0, 4, .K11⟩, 0⟩] 2).1
#guard !wantsFree (toyWants.1 ++ [⟨⟨⟨1, some 0, 9, .K9⟩, 0⟩, "scalars", toyRow, 4, 1⟩])
-- without the merge's address its end value is put under the mask row
#guard ((segmentWants toySeg 0 toyRow toyIdx [] 2).1.map fun w => (w.use, w.number)).getLast? ==
  some ("ends", 13)

end ProofFile.Honest
