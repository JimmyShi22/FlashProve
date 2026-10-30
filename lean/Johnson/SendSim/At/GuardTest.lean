-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/GuardTest.lean: the condition on the book at a sender, split in two executable
parts: a further test (fits), which bounds every entry on the sender's coins by the sender's number
of coins and checks what each address spends, and the guard, which names the coins that must not be
known to a part that spends given runs. The file holds definitions only.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. "Spent" against
"carried": the field once of the structure Ahead (Johnson/Desc/ProofFile/Honest/Frame.lean). A run
is a pair (start, length): the coins of one field with the numbers start, ..., start + length - 1.
The owner o is the address of the sending part whose coins the book hands out; p is any address that
the book gives a run. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. P holds the public numbers of a place (K1.Par), and ride says which messages are
tables sent along (Ride, Johnson/Desc/ProofFile/Honest/K1/Coins.lean).
  runsE, runsF       the runs that a list of entries cuts off, in the extension field and in the
                     base field.
  coinGuard P ride c   the runs that are tied to the coin number c of the extension field by what
                     the sender discloses. If c is a free mask entry of a sampled message that is
                     not a table sent along: the pads of that message's sample, the tail of the mask
                     row that holds c, and the tail of the last mask row (the row that holds the
                     pads). If c is one of the coefficient coins of a table sent along: the tails of
                     all rows of that table.
  sendGuardE P ride e   the guard: the runs e themselves, and coinGuard of every coin in them.
  apartRunsB a b     accepts if no coin is in a run of a and in a run of b.
  spentApartB        at o and p: accepts if the runs that p spends are apart from the known ones, in
                     both fields.
  guardApartB        at o and p: spentApartB, and the guard of what p spends is apart from the known
                     runs. The guard leaves the base-field runs as they are and is sendGuardE on the
                     extension-field runs.
  spenderFitsB       at o and p: accepts if p spends nothing of o's coins; or spends no coin of the
                     base field, only free mask entries, and no coin twice; or has one spending
                     entry, which is exactly the coefficient coins of one table sent along (its
                     first Ride.count mask coins, not its tails).
  ownerFitsB         accepts if all entries on o's coins are within the sender's number of coins
                     (withinB) and spenderFitsB accepts at every address that the book gives a run.
  ownerOkB           ownerFitsB, and guardApartB at every such address that spends something of
                     o's coins.

How it fits. The condition on the book (BookClearAny, Johnson/SendSim/At/BookWide.lean) has clauses
on what is spent and clauses on what is known. Here the two are apart. spenderFitsB reads no known
entry. Besides the bound in withinB, which covers every entry on the owner's coins, known entries
enter only as runs that must be apart from the spent runs and from the guard. ownerOkB accepts
exactly where BookClearAny holds (ownerOkB_iff, Johnson/SendSim/At/GuardTestTie.lean). The tests
serve lemmas that are meant as steps toward index privacy (Johnson/WholeKey/Statement.lean); nothing
in this folder derives index privacy from them. None is one of the release's goal statements.

Limits. No test is evaluated here. ownerOkB accepts at a book without entries, and at an owner on
whose coins the book has no entry; BookClearAny holds there too. The guard is the spent runs as
given, followed by the runs that coinGuard ties to them, the added runs each once. To make it, the
code goes through every spent coin. The bound on queried positions (budAt,
Johnson/SendSim/At/Sim.lean) and the test that a job fits its place (sendFits) are no part of these
tests: they do not read the book.
-/
import Johnson.SendSim.At.WideTest

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

/-- The runs of coins of the extension field that a list of entries cuts off. -/
def runsE (l : List Ahead) : List (Nat × Nat) := l.map fun a => (a.start.e, a.count.e)

/-- The runs of coins of the base field that a list of entries cuts off. -/
def runsF (l : List Ahead) : List (Nat × Nat) := l.map fun a => (a.start.f, a.count.f)

/-- No coin is in a run of a and in a run of b. -/
def apartRunsB (a b : List (Nat × Nat)) : Bool :=
  !(a.any fun x => b.any fun y => meets x.1 x.2 y.1 y.2)

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- The pads of message number k's sample, each as a run of one coin. -/
def padRuns (k : Nat) : List (Nat × Nat) :=
  (List.range (shapeAt P k).answers).map fun i => (padNo P ride k i, 1)

/-- The tail of mask row r of message number k, as a run. -/
def tailRun (k r : Nat) : Nat × Nat := (maskTailNo P ride k r 0, (maskCodeAt P k).r)

/-- The runs that what the sender discloses ties to the coin number c of the extension field. -/
def coinGuard (c : Nat) : List (Nat × Nat) :=
  (List.range P.sent.size).flatMap fun k =>
    match ride k with
    | none =>
      if (shapeAt P k).answers != 0 && decide (maskStart P ride k ≤ c) &&
          decide (c < maskStart P ride k + OnBytes.Send.freeMaskEntries (shapeAt P k).maskRows
            (maskCodeAt P k).ell (shapeAt P k).answers) then
        padRuns P ride k ++ [tailRun P ride k ((c - maskStart P ride k) % (shapeAt P k).maskRows),
          tailRun P ride k ((shapeAt P k).maskRows - 1)]
      else []
    | some R =>
      if decide (maskStart P ride k ≤ c) && decide (c < maskStart P ride k + R.count) then
        (List.range (shapeAt P k).maskRows).map fun r => tailRun P ride k r
      else []

/-- **The guard**: the runs themselves, and the runs that are tied to a coin in them. -/
def sendGuardE (e : List (Nat × Nat)) : List (Nat × Nat) :=
  e ++ (e.flatMap fun x => (List.range x.2).flatMap fun t => coinGuard P ride (x.1 + t)).dedup

/-- At an owner and an address: nothing that the address spends is known there. -/
def spentApartB (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Bool :=
  apartRunsB (runsF (Bk.spentBy o p)) (runsF (Bk.knownBy ord o p)) &&
    apartRunsB (runsE (Bk.spentBy o p)) (runsE (Bk.knownBy ord o p))

/-- At an owner and an address: nothing that the address spends is known there, and nothing in the
guard of what it spends. The clause on the base field appears in both halves, because the guard is
the identity on base-field runs. -/
def guardApartB (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Bool :=
  spentApartB Bk ord o p &&
    (apartRunsB (runsF (Bk.spentBy o p)) (runsF (Bk.knownBy ord o p)) &&
      apartRunsB (sendGuardE P ride (runsE (Bk.spentBy o p))) (runsE (Bk.knownBy ord o p)))

/-- Accepts if the list is one entry, which is exactly the coefficient coins of one table sent
along. -/
def foldShapeB (sp : List Ahead) : Bool :=
  match sp with
  | [e] => (List.range P.sent.size).any fun k =>
    match ride k with
    | some R => (e.count == ⟨0, R.count⟩) && (e.start.e == maskStart P ride k)
    | none => false
  | _ => false

/-- What the sender asks of the entries by which one address spends. It reads no known entry. -/
def spenderFitsB (Bk : ProverCoinCounts) (o p : Addr) : Bool :=
  (Bk.spentBy o p).isEmpty ||
    (noFB (Bk.spentBy o p) && allE (Bk.spentBy o p) (isFreeB P ride) && apartB (Bk.spentBy o p)) ||
    foldShapeB P ride (Bk.spentBy o p)

/-- Accepts if all entries on the owner's coins are within the sender's number of coins and
spenderFitsB accepts at every address that the book gives a run. -/
def ownerFitsB (Bk : ProverCoinCounts) (o : Addr) : Bool :=
  withinB P ride Bk o && (Bk.ahead.map (·.spender)).all fun p => spenderFitsB P ride Bk o p

/-- **The condition on the book at a sender, in two parts.** Accepts if ownerFitsB accepts, and
guardApartB accepts at every address that spends something of the owner's coins. -/
def ownerOkB (Bk : ProverCoinCounts) (ord : List Place) (o : Addr) : Bool :=
  ownerFitsB P ride Bk o && (Bk.ahead.map (·.spender)).all fun p =>
    (Bk.spentBy o p).isEmpty || guardApartB P ride Bk ord o p

end OnBytes.SendSim.At
