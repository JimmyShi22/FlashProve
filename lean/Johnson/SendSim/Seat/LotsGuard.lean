-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/LotsGuard.lean: the premise on the book for the senders of the kind K1 on the
first chain, by address and in three parts: which owners it covers, a guard at each of them, and a
further test. The file holds definitions only.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". For runs, the guard and the two-part
test: the head of Johnson/SendSim/At/GuardTest.lean. Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. Z is the public part and G the ground, as in Johnson/SendSim/Seat/LotsTest.lean.
An owner is given by its address o: a place, and the part's number at that place. Our sender is part
number 0 at its place.
  lotPlacesApartB Z G   accepts if no two jobs of the two lists are at one place.
  lotAt Z G o        the public numbers and the tables sent along of the first job of lotPars Z G at
                     o's place, if o is part number 0 there; else none.
  lotsMine Z G o     which owners are covered: accepts if o is the sender of a job of the two lists.
  lotsGuardE Z G o   the guard at such an owner, on runs of the extension field (sendGuardE): from
                     the spent runs to the runs that must not be known. At any other address it
                     returns the runs unchanged.
  lotsOwnerFitsB Z G   the further test: lotPlacesApartB, and what that sender asks of the book
                     apart from the guard (ownerFitsB). It rejects at an address that is no sender
                     of ours. It is not lotsFitB (LotsTest.lean), which tests that the jobs fit
                     their places and reads no book.
  lotsOkB Z G        combines them at one owner: lotsOwnerFitsB, and at every address that spends
                     something of the sender's coins: nothing that it spends is known there
                     (spentApartB), and nothing in the guard of what it spends. The guard leaves the
                     base-field runs as they are and is lotsGuardE on the extension-field runs.

How it fits. A caller that holds one book for many kinds of owners can ask each kind for these three
parts and run one test over all owners. What the parts give is proved in
Johnson/SendSim/Seat/LotsGuardTie.lean. The tests serve lemmas that are meant as steps toward index
privacy (Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them.
None is one of the release's goal statements.

Limits. No test is evaluated here. lotAt takes the first job at a place. lotPlacesApartB accepts at
every public part and ground (lotPlacesApart, LotPlaces.lean), so that job is the only one at its
place. Our senders let nobody spend a coin of the base field, and lotsOwnerFitsB tests that. Only
the places of the kind K1 on the first chain are covered. That chain has other sendings of new
tables, of the kinds K2 and K12.
-/
import Johnson.SendSim.Seat.LotsTest
import Johnson.SendSim.At.GuardTest

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

/-- Accepts if no two jobs of the two lists are at one place. -/
def lotPlacesApartB (Z : ProofFile.Pub) (G : ProofFile.Ground) : Bool :=
  decide ((lotPars Z G).map (·.1.place)).Nodup

/-- The public numbers and the tables sent along of the first job at o's place, if o is part number
0 there. -/
def lotAt (Z : ProofFile.Pub) (G : ProofFile.Ground) (o : Addr) : Option (K1.Par × (Nat → Option Ride)) :=
  if o.part == 0 then (lotPars Z G).find? fun x => x.1.place == o.place else none

/-- Accepts if the address is the sender of a job of the two lists. -/
def lotsMine (Z : ProofFile.Pub) (G : ProofFile.Ground) (o : Addr) : Bool := (lotAt Z G o).isSome

/-- The guard of the sender at o, on runs of the extension field. At an address that is no sender of
ours it returns the runs unchanged. -/
def lotsGuardE (Z : ProofFile.Pub) (G : ProofFile.Ground) (o : Addr) (e : List (Nat × Nat)) :
    List (Nat × Nat) :=
  match lotAt Z G o with
  | some x => sendGuardE x.1 x.2 e
  | none => e

/-- The further test at the sender at o: no two jobs are at one place, and ownerFitsB accepts at
that sender's numbers. It rejects at an address that is no sender of ours. The order of places is
not read. -/
def lotsOwnerFitsB (Z : ProofFile.Pub) (G : ProofFile.Ground) (Bk : ProverCoinCounts) (_ord : List Place) (o : Addr) :
    Bool :=
  lotPlacesApartB Z G &&
    match lotAt Z G o with
    | some x => ownerFitsB x.1 x.2 Bk o
    | none => false

/-- The three parts together at one owner: the further test, and at every address that spends
something of the owner's coins, nothing that it spends and nothing in the guard of it is known. The
clause on the base field appears in both halves, because the guard is the identity on base-field
runs. -/
def lotsOkB (Z : ProofFile.Pub) (G : ProofFile.Ground) (Bk : ProverCoinCounts) (ord : List Place) (o : Addr) : Bool :=
  lotsOwnerFitsB Z G Bk ord o && (Bk.ahead.map (·.spender)).all fun p =>
    (Bk.spentBy o p).isEmpty || (spentApartB Bk ord o p &&
      (apartRunsB (runsF (Bk.spentBy o p)) (runsF (Bk.knownBy ord o p)) &&
        apartRunsB (lotsGuardE Z G o (runsE (Bk.spentBy o p))) (runsE (Bk.knownBy ord o p))))

end OnBytes.SendSim.Seat
