-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshOwner.lean: kind K14: THE TEST ON THE BOOK OF COINS FOR THE
PART AT "send o_omega", WHICH OWNS THE COIN THAT "SPLIT" SPENDS, in the frame's one form (OwnerTest,
Honest/BookGuard.lean). Definitions with code; no statement. It stands over
Honest/K14/FreshDefs.lean, Honest/BookGuard.lean, Honest/K14/SendingsShapes.lean (the test
sendingsFit) and the library's Johnson/Desc/K14/Honest/FreshAtShapes.lean (the test freshPublicB).

  spRun           all of o_sp's coins among the part's own, as one run: its n + 1 entries and its
                  tail's r entries, from spFirstCoin on
  spGuard         **the guard**: whatever is spent: that run. The part shows symbols and an
                  out-of-domain (OOD) answer that tie all of o_sp's coins to each other
  withinCount, spFits   what else is asked: of the book: oneSpender: at most one entry spends of the
                  part's coins, and it spends one entry of o_sp that is no pad · OF THE PLAN, WITH
                  CODE, THE THREE PREMISES OF THE LAW ON THE SHAPES: sendingsFit · the shape
                  splits · the library's freshPublicB (SpShape's six clauses: o_sp has no main row,
                  one mask row, one answer; its mask code has n + 1 message entries, a power of two,
                  and at most 2 ^ 32 positions; a seventh clause, on the tail's length, is true here
                  by unfolding). So the test REJECTS EVERY BOOK at a plan at which the law's
                  premises fail · OF THE OWNER: THAT IT IS THE PART's ONE ADDRESS: so, were mine
                  wider than that address, the test would reject at every other address that it
                  named, and the laws would keep their proofs · OF THE BOOK AGAIN: withinCount:
                  EVERY ENTRY OF THAT OWNER, SPENT OR CARRIED, LIES WITHIN THE PART's OWN COUNT
                  (takesOf at the sending's job: the field takes of sendingPart): the book's own
                  test (ProverCoinCounts.clauses' fourth) holds an entry against THE BOOK's ROW for its owner,
                  which may state too many. (Kin: withinB, in the files on the simulator of a
                  sending: the same spelling at another sender's count; here the count is an
                  argument)
  spOwnerTest     **the test**: mine: the one address of the part · guard: spGuard · fits: spFits
  spEntries, spOwner   the number n read off the mask code's message length, with code; the test at
                  that number

The law at this test: sp_owner_law, Honest/K14/FreshOwnerLaw.lean.
What is not claimed. That any book passes the test. Nothing on what is or is not hidden; no
property.
-/
import Johnson.Desc.ProofFile.Honest.K14.FreshDefs
import Johnson.Desc.ProofFile.Honest.BookGuard
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes
import Johnson.Desc.K14.Honest.FreshAtShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14

/-- All of o_sp's coins among the part's own, as one run: its first number and its length. -/
def spRun (A : SendPub) (n : Nat) : Nat × Nat := (spFirstCoin A, n + 1 + (spMaskCode A).r)

/-- **The guard**: whatever is spent, all of o_sp's coins; no coin of the base field. -/
def spGuard (A : SendPub) (n : Nat) : Guard := fun _ => { f := [], e := [spRun A n] }

/-- **Every entry of the book with this owner, spent or carried, lies within the count d.** -/
def withinCount (d : Due) (B : ProverCoinCounts) (o : Addr) : Bool :=
  B.ahead.all fun e => !(e.owner == o) ||
    (decide (e.start.f + e.count.f ≤ d.f) && decide (e.start.e + e.count.e ≤ d.e))

/-- **What else the owner asks**: of the book; of the plan, with code, the law's three premises on
the shapes; of the owner that it is the part's one address; and of the book that every entry of that
owner lies within THE PART's OWN count. -/
def spFits (A : SendPub) (n : Nat) (B : ProverCoinCounts) (o : Addr) : Bool :=
  oneSpender B o (spFirstCoin A) n && sendingsFit A.P && A.P.S.sharedSplitNeeded &&
    Desc.K14.Honest.freshPublicB A.P.codes A.P.S n (spMaskCode A).r &&
    o == { place := sendPlace 5, part := 0 } &&
    withinCount (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort) B o

/-- **The test for the part at "send o_omega".** -/
def spOwnerTest (A : SendPub) (n : Nat) : OwnerTest :=
  { name := "K14: send o_omega"
    mine := fun o => o == { place := sendPlace 5, part := 0 }
    guard := fun _ => spGuard A n
    fits := fun B _ o => spFits A n B o }

/-- The number of o_sp's entries that are no pad, read off the mask code's message length. (At the
length 0 it is 0; the library's freshPublicB rejects there.) -/
def spEntries (A : SendPub) : Nat := (spMaskCode A).ell - 1

/-- The test at that number. -/
def spOwner (A : SendPub) : OwnerTest := spOwnerTest A (spEntries A)

end ProofFile.Honest.K14
