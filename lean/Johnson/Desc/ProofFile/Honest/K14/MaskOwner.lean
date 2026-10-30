-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/MaskOwner.lean: kind K14: THE TEST ON THE BOOK OF COINS FOR THE
PART AT "send o_u", WHICH OWNS THE COINS THAT THE FIRST FOLD OF THE PROXIMITY TEST ON G_u SPENDS, in
the frame's one form (OwnerTest, Honest/BookGuard.lean). The part (Honest/K14/Sendings.lean) sends
o_u and, where masks are sent ahead, the first mask of that test: a fold's fresh table, whose 2 k +
1 first coins are the coefficients of the fold's hiding polynomial. Definitions with code; no
statement.

  maskFirstCoin   the number, among the part's own coins, of the first of these coefficients
  maskRun         all of the first mask's coins among the part's own, as one run: the coefficients
                  and its rows' tails
  runIs           at most one entry spends of a part's coins, and it is one whole run
  maskGuard       **the guard**: whatever is spent: all of the first mask's coins. The part shows
                  symbols of the first mask's rows, which tie its coefficients to its rows' tails
  maskOwnerFits   what else the owner asks: runIs at the 2 k + 1 coefficients; WITH CODE the law's
                  three premises on the shapes; that the owner is the part's one address; that every
                  entry of that owner lies within the part's own count
  maskOwnerTest   **the test**: mine: the one address of the part · guard: maskGuard · fits:
                  maskOwnerFits
  maskRounds, maskOwner   the number k read off the first stage of the test on G_u in the shape,
                  with code; the test at that number

Limits. maskFirstCoin is the first coefficient's number, and maskRun the first mask's coins, only
where the sending has a second message and the shapes fit (sendingsFit,
Honest/K14/SendingsShapes.lean). runIs asks more than the owner's sentence needs: a shorter run
inside the coefficients would do for it; the whole run is asked so that what the spender is handed
is what the owner has laid. That any book passes the test is not claimed. Nothing on what is or is
not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.FreshDefs
import Johnson.Desc.ProofFile.Honest.K14.FreshOwner
import Johnson.Desc.ProofFile.Honest.BookGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14

/-- The number, among the part's own coins, of the first coin of message number 1 of "send o_u":
under the premises named in this file's Limits the first coefficient of the first mask's hiding
polynomial. -/
def maskFirstCoin (A : SendPub) : Nat :=
  offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort 1

/-- All coins of message number 1 of "send o_u" among the part's own, as one run: its first number
and its length. -/
def maskRun (A : SendPub) : Nat × Nat :=
  (maskFirstCoin A,
    dueOf (jobU A).Q.codes ((jobU A).Q.sent.getD 1 default).shape ((jobU A).sort 1))

/-- **At most one entry spends of the part at o, and it is the whole run**: len coins of the
extension field from number first on; none of the base field, from the base field's number 0. -/
def runIs (B : ProverCoinCounts) (o : Addr) (first len : Nat) : Bool :=
  match spendersOf B o with
  | [] => true
  | [e] => e.start == ⟨0, first⟩ && e.count == ⟨0, len⟩
  | _ => false

/-- **The guard**: whatever is spent, all of the first mask's coins; no coin of the base field. -/
def maskGuard (A : SendPub) : Guard := fun _ => { f := [], e := [maskRun A] }

/-- **What else the owner asks.** k: the fold's number of variables. Of the book: runIs at the 2 k +
1 coefficients. Of the plan, WITH CODE, the law's three premises on the shapes: the test on both
sendings' shapes accepts; masks are sent ahead; the test on G_u has a first stage, of k variables:
so the test's yes stands at no shape at which the law does not. Of the owner: that it is the part's
one address: so a test whose mine were widened would reject at every other address. Of the book
again: that every entry of that owner, spent or carried, lies within THE PART's OWN count
(withinCount, Honest/K14/FreshOwner.lean): the book's own tests hold an entry against the book's row
alone. -/
def maskOwnerFits (A : SendPub) (k : Nat) (B : ProverCoinCounts) (o : Addr) : Bool :=
  runIs B o (maskFirstCoin A) (2 * k + 1) && sendingsFit A.P && A.P.S.masksAhead &&
    A.P.S.testU.head?.map (·.k) == some k &&
    o == { place := sendPlace 2, part := 0 } &&
    withinCount (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort) B o

/-- **The test for the part at "send o_u".** k: the fold's number of variables. -/
def maskOwnerTest (A : SendPub) (k : Nat) : OwnerTest :=
  { name := "K14: send o_u"
    mine := fun o => o == { place := sendPlace 2, part := 0 }
    guard := fun _ => maskGuard A
    fits := fun B _ o => maskOwnerFits A k B o }

/-- The fold's number of variables, read off the first stage of the test on G_u in the shape. -/
def maskRounds (A : SendPub) : Nat := (A.P.S.testU.head?.map (·.k)).getD 0

/-- The test at that number. -/
def maskOwner (A : SendPub) : OwnerTest := maskOwnerTest A (maskRounds A)

end ProofFile.Honest.K14
