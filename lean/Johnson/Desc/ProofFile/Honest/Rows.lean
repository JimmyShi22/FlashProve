-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Rows.lean: the rows that a program can print of an honest run
(Honest/Frame.lean) beside a stored run of the same description, while the kinds' prover's sides are
written one at a time. Executable definitions; no theorem.

  row 1  told k of n    of the n sub-protocols whose rounds send something, k have a prover's side;
                        the others are played from the stored run. A prover's side is counted whole:
                        a list of parts has a move for every round of its sub-protocol, or `run`
                        returns an error
  row 2  equal e of k   of these k, e send what the stored run shows: their items in the clear,
                        round by round, and every column that is read of a table of theirs;
         idle i         and at i of the k nothing could be compared: they count as neither
  row 3  the decision   `FileDescription.say` on the played views
  row 4  stored         how many columns were read of each stored table
  and two notes that are on every print: whose the coins are; what a yes does not show

  `senders`         the places of the sub-protocols that send something
  `toldPlaces`      the places at which a prover's side made a round of the run
  `partsToldAt`     the numbers of the parts that made a round at a place
  `equalAt`, `comparedAt`   row 2 at one place; how much was compared there
  `Rows`, `rows`, `Rows.print`

How the rows can fail. Row 2 fails at a place if its prover's side sends another item or another
word at a position that is read. Row 3 says no if the description rejects the played views. A place
of whose tables no column is read and whose rounds have no item in the clear is counted as idle, not
as equal. What a prover's side made is counted from the played run, not from the prover's lists.

Limits.
  * The stored run's coins and input have to be supplied: nothing here finds them.
  * Where the coins are not the stored run's own, row 2 is not expected to hold, and what is left is
    row 3: the caller says which it is (`ownCoins`), and the print repeats it.
  * Row 2 sees a table only at the positions that the stored run's challenges read.
  * Row 2 does not see the stored tables' columns: no place sends them (`Read.sender` is `none`).
    Another word of the committer's shows in row 3 alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place OpenedColumn)

variable {S Cl Xi W₀ Rc Ky Tr X₀ X : Type}

/-- The places of the sub-protocols whose rounds send something. -/
def senders (bs : List (Block S Cl)) : List Place :=
  (bs.filter fun b => b.rounds.any fun r => r.entry.msg != 0).map (·.place)

/-- At the rounds played at the place `a`, the items in the clear are the stored run's. -/
def plainAt (a : Place) (l : List Played) (rs : List Fmt.RoundView) : Bool :=
  (l.zip rs).all fun x => x.1.place != a || x.1.vals == x.2.vals

/-- Every column that is read of a table sent at the place `a` is the stored run's column: key,
position and words. -/
def colsAt (a : Place) (l : List Read) (cs : List OpenedColumn) : Bool :=
  (l.zip cs).all fun x => x.1.sender != some a ||
    (x.1.key == x.2.1 && x.1.pos == x.2.2.1 && x.1.words == some x.2.2.2)

/-- Row 2 at one place, over the three chains. -/
def equalAt (r : Run) (U : Views) (a : Place) : Bool :=
  plainAt a r.played.1 U.1.rounds && plainAt a r.played.2.1 U.2.1.rounds &&
    plainAt a r.played.2.2 U.2.2.rounds && colsAt a r.reads.1 U.1.opened &&
    colsAt a r.reads.2.1 U.2.1.opened && colsAt a r.reads.2.2 U.2.2.opened

/-- How much row 2 compares at one place: the rounds played there that have an item in the clear, in
the run or in the stored run, and the columns that are read of its tables. -/
def comparedAt (r : Run) (U : Views) (a : Place) : Nat :=
  let p (l : List Played) (rs : List Fmt.RoundView) : Nat :=
    ((l.zip rs).filter fun x => x.1.place == a && !(x.1.vals.isEmpty && x.2.vals.isEmpty)).length
  let q (l : List Read) : Nat := (l.filter fun x => x.sender == some a).length
  p r.played.1 U.1.rounds + p r.played.2.1 U.2.1.rounds + p r.played.2.2 U.2.2.rounds +
    q r.reads.1 + q r.reads.2.1 + q r.reads.2.2

/-- The places at which a prover's side made a round of the run. -/
def toldPlaces (r : Run) : List Place :=
  (((r.played.1 ++ r.played.2.1 ++ r.played.2.2).filter (·.told)).map (·.place)).eraseDups

/-- The numbers of the parts that made a round of the run at a place. -/
def partsToldAt (r : Run) (a : Place) : List Nat :=
  (((r.played.1 ++ r.played.2.1 ++ r.played.2.2).filter fun p => p.told && p.place == a).map
    (·.part)).eraseDups

/-- The run and the stored run have as many rounds (the first chain's sealing round aside) and read
as many columns. -/
def sameSize (r : Run) (U : Views) : Bool :=
  r.played.1.length == U.1.rounds.length + 1 && r.played.2.1.length == U.2.1.rounds.length &&
    r.played.2.2.length == U.2.2.rounds.length && r.reads.1.length == U.1.opened.length &&
    r.reads.2.1.length == U.2.1.opened.length && r.reads.2.2.length == U.2.2.opened.length

/-- The rows. -/
structure Rows where
  /-- the sub-protocols that send something -/
  all : Nat
  /-- those that have a prover's side -/
  told : Nat
  /-- those of them that send what the stored run shows, where something was compared -/
  equal : Nat
  /-- those of them at which nothing was compared -/
  idle : Nat
  /-- the places at which row 2 fails -/
  falls : List Place
  /-- the description's decision on the played views -/
  verdict : String
  /-- the columns read of each stored table: the statement's item, the number -/
  stored : List (Nat × Nat)
  /-- what the caller states: the coins are the stored run's own -/
  ownCoins : Bool

/-- **The rows**, at a stored run `U`, at its challenges. `ownCoins`: what the caller states on
whether `c` is the stored run's own coins. No default: the print repeats it, so a caller has to say
it. -/
def rows (ownCoins : Bool) (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀)
    (rc : Rc) (x : Xi) (c : Coins B) (U : Views) : Except String Rows :=
  match run F B H w₀ rc x c (drawsOf U) (some U) with
  | .error e => .error e.words
  | .ok r =>
    if !sameSize r U then .error "the run and the stored run differ in size" else
      let all := senders F.first.blocksInOrder ++ senders F.shared.blocksInOrder ++ senders F.second.blocksInOrder
      let told := all.filter (toldPlaces r).contains
      let idle := told.filter fun a => comparedAt r U a == 0
      let falls := told.filter fun a => !equalAt r U a
      .ok ⟨all.length, told.length, told.length - falls.length - idle.length, idle.length, falls,
        F.say x r.views.1 r.views.2.1 r.views.2.2, r.storedRead, ownCoins⟩

/-- The four rows in one line, without the two notes. -/
def Rows.short (R : Rows) : String :=
  s!"told {R.told} of {R.all} · equal {R.equal} of {R.told} · idle {R.idle} · " ++
    s!"the decision: {R.verdict} · stored columns read: {R.stored}"

/-- **The print**: the four rows and the two notes. -/
def Rows.print (R : Rows) : String :=
  R.short ++ " · the coins: " ++
    (if R.ownCoins then "the stored run's own"
      else "NOT the stored run's: «equal» is not due; what is left is the decision") ++
    " · A YES SHOWS NOTHING OF WHAT WAS TAKEN FROM THE STORED RUN"

end ProofFile.Honest
