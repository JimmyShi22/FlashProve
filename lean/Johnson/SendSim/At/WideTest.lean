-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/WideTest.lean: the executable tests for the wider condition on the book, which
allows a table of any number of rows that is sent along. Definitions only.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file has. Three executable tests (Bool-valued definitions); no statement and no proof. The
file has few imports, so that the tests can be run without the files that the statements on them
need.
  foldAnyB           The test for FoldSpenderAny: p spends, by one entry, the coefficients of a
                     table of any number of rows that is sent along; no coin of the tail of any of
                     its rows is known; and none of the spent coins is known.
  spenderClearAnyB   p spends nothing of the owner's coins, or passes maskB, or passes foldAnyB.
  bookClearAnyB      Every entry of the owner is within the sender's number of coins (withinB), and
                     every address that some entry names as its spender passes spenderClearAnyB.

Limits. The tests read a book's entries and a place's public parameters: no input, no value of a
coin and no execution. No distribution is named.

How it fits. FoldSpenderAny is in Johnson/SendSim/At/FoldAny.lean, maskB and withinB in
Johnson/SendSim/At/BookTest.lean. Each test accepts exactly if its condition holds: foldAnyB_iff and
spenderClearAnyB_iff (Johnson/SendSim/At/FreshWide.lean), bookClearAnyB_iff
(Johnson/SendSim/At/BookWide.lean). The condition BookClearAny is the premise on the book of
sendFreshAtWide (Johnson/SendSim/Seat/HandedWideProofs.lean).
-/
import Johnson.SendSim.At.BookTest

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- Test for FoldSpenderAny: p spends, by one entry, the coefficients of a table of any number of
rows that is sent along; no coin of the tail of any of its rows is known; none of the spent coins is
known. -/
def foldAnyB (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Bool :=
  (match Bk.spentBy o p with
    | [e] => (List.range P.sent.size).any fun k =>
      match ride k with
      | some R => (e.count == ⟨0, R.count⟩) && (e.start.e == maskStart P ride k) &&
          (List.range (shapeAt P k).maskRows).all fun r =>
            (List.range (maskCodeAt P k).r).all fun q =>
              !inE (Bk.knownBy ord o p) (maskTailNo P ride k r q)
      | none => false
    | _ => false) &&
    allE (Bk.spentBy o p) (fun n => !inE (Bk.knownBy ord o p) n)

/-- The test for the wider condition at one address p: it spends nothing of the owner's coins, or
passes maskB, or passes foldAnyB. -/
def spenderClearAnyB (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Bool :=
  (Bk.spentBy o p).isEmpty || maskB P ride Bk ord o p || foldAnyB P ride Bk ord o p

/-- The test for the wider condition at all addresses: withinB, and spenderClearAnyB at each address
that some entry names as its spender. -/
def bookClearAnyB (Bk : ProverCoinCounts) (ord : List Place) (o : Addr) : Bool :=
  withinB P ride Bk o &&
    (Bk.ahead.map (·.spender)).all fun p => spenderClearAnyB P ride Bk ord o p

end OnBytes.SendSim.At
