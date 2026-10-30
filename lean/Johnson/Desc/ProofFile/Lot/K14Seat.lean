-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K14Seat.lean: the whole shared chain of a proof file's description, as
one value of the record that the description's maker takes for it
(Johnson/Desc/ProofFile/LotCore.lean: SharedSeat).

This file holds definitions only; no theorem is stated.

sharedSeatOf c beforePoint tests standIns last fileOk:
  c            the planner's chains;
  beforePoint  the first chain's messages that must be fixed before the shared point is drawn:
               (1, the message's number in the first chain's order of sending);
  tests        the proximity tests' blocks, at this chain's state, for the places 9 and 10;
  standIns     which of these are stand-ins, by name;
  last         the chain's closing block, for the place 11, as a function of the blocks that are
               laid in front of it;
  fileOk       the file's own share of the tests on the plan, as whoever assembles the file has
               reckoned it: what ties this chain's plan to the other two chains' reads the public
               part too, which this function is not handed.

The fields. The state is St (Johnson/Desc/K14/Text.lean): the statement, the book of trees, the
roots received and the kind's nine named values, the key among them: the key is the instance's, is
laid by start, and is no block's parameter. chain: chainOf (Johnson/Desc/K14/Blocks.lean): a front
block; "LIN point", "(rec_gamma)", "LOC", "joins", "LIN zeta", "SPLIT" and the two sendings; the
tests and the closing block, which come in as arguments. ended: the record of a shared chain's end,
field for field out of the state; nothing unless `tested` holds. okInst: the key's words are below
the prime, and it names the item that the chain's reads name. fileOk: testsFit, and the argument.
testsFit: as many proximity tests are handed in as the shape asks: two where it splits, else one.

Main names: testsFit, sharedSeatOf.

What is not claimed. That the tests and the closing block that are handed in are the right ones.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Blocks
import Johnson.Desc.ProofFile.LotCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)

/-- As many proximity tests are handed in as the shape asks: two where o_u and o_omega differ in
code (then "SPLIT" has its round, and G_omega wants a test of its own), else one. -/
def testsFit (P : P14) (tests : List (Block St Unit)) : Bool :=
  tests.length == if P.S.sharedSplitNeeded then 2 else 1

/-- The shared chain, as the record that the description's maker takes. -/
def sharedSeatOf (c : Verify.Chains) (beforePoint : List (Nat × Nat))
    (tests : P14 → List (Block St Unit)) (standIns : List String)
    (last : List (Block St Unit) → Block St Unit) (fileOk : Bool) : ProofFile.SharedSeat :=
  let P := p14Of c beforePoint
  { lot := "the shared chain"
    σ := St
    start := fun x => first P.codes x.key
    chain := chainOf c P (tests P) last
    ended := ended
    okInst := fun x => okKey P x.key
    fileOk := testsFit P (tests P) && fileOk
    standIns := standIns }

end Desc.K14
