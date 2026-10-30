-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Pend/Row.lean: the pending row: the one equation on the committed matrix W that a
link with claims on the weights hands on. It stands at the end of the closing of a link, between the
merge of the weights' claims, whose leavings it reads, and the members' batching, which tests it.

What it means. In the merge the prover has shown a value fv' and says that it is fv + beta c, where
    fv = < Gamma (x) eq(rm, .), W >.
Gamma: the weights on the rows of W that the link's claims add up to. rm: the merge's point on the
columns. c: an entry of the index-mask message that no other equation uses. Nothing in the link
tests this. So the link hands on the equation
    < Gamma (x) eq(rm, .), W > + beta c = fv'.

ROUNDS. None: nothing is sent and nothing is drawn. It comes behind a link's last round, at the
links whose record says that they leave a row: the layers' and the head's.

READS. No oracle message at any position.

DECIDES. From the plan: the layout of W, the link's number of claims, the number of rows of the
table that the test on W has (its row bits follow from that number). From what the merge left: for
each claim its unit, a scalar and its factors on the rows (recs); rm; beta; fv' (fvp). From the
statement: the ledger of the message number indexMasks. It says no if these do not fit each other or
no mask entry is free. Else it hands on: the row, which the caller puts at the END of the list of
pending rows; and that one ledger with the entry taken.

SENDS. Nothing: an honest prover has nothing to do here.

Calls. wsGamma: one claim's weights on the rows of its unit (the merge's). Own.weightsOnRows
(Johnson/Desc/Own/Stretch.lean): weights on a stretch of rows as a sum of vectors of product form;
it returns what `verify-on-bytes`'s memberWeightsOnRows returns (StretchAgree.lean, beside it).

Main names: nextEntry, takeEntry (the ledger); span, addClaim (Gamma); pendingRowO (the row).
A mark [n] behind a line is the number of the test in the list of this file's tests.

Definitions with code; no theorem. Not claimed: anything on soundness, on an honest prover or on
hiding.

Written after pendingRowH of the program `verify-on-bytes`
(OnBytes/Model/StagesLinks.lean:522-528), wsPending and wsSpan (OnBytes/Model/Pending.lean:55-82),
wsGammaAdd (OnBytes/Model/Weights.lean:434-444), Blk.takeMask and nextRealRow
(OnBytes/Iop/Ground.lean:1304-1315), memberPendingRow (OnBytes/Iop/Lin.lean:423). Of the two
functions under "Calls", wsGamma is that program's pure routine, called by name (Weights.lean:426);
Own.weightsOnRows is that program's memberWeightsOnRows (Lin.lean:415), taken over as a named part
of the description.
THE TESTS: number · what is asked · file:line in `verify-on-bytes` · the mark in this file.
   4 the layout has as many rows as the table · Pending.lean:71 · [4]
   5 there is a claim · :72 · [5]        6 as many claims as the plan says · :72 · [6]
   7 the point has the layout's column bits · :72 · [7]
   8 every claim's unit is in the layout (span) · :59 · [8]
   9 the span is not empty · :75 · [9]   10 it ends inside the layout · :75 · [10]
  11 at most 62 row bits · :75 · [11]
  12 the cube holds the layout · :75 · [12]: not reachable behind 4: the row bits are ceilLog2 of
     the table's rows (Lin.lean:55)
  13 every claim's unit is in the layout (weights) · Weights.lean:437 · [13]: not reachable behind 8
  14 as many weights as the unit has rows · :440 · [14]
  15 as many factors as the unit has groups · :440 · [15]
  16 the unit's rows lie inside Gamma · :440 · [16]: not reachable: Gamma has the span's end
  17 the stretch ends inside the table · Lin.lean:417 · [17-19]: Own/Stretch.lean's [1]
  18 fewer than 63 row bits, and the stretch lies in the cube · Lin.lean:405 · [17-19]: its [2]
  19 the blocks cover the stretch · Lin.lean:407 · [17-19]: its [3]
     (17 to 19: not reachable behind 4 and 9 to 12: `verify-on-bytes`'s own comment,
     Pending.lean:79-80)
  20 the message number indexMasks is there · Ground.lean:1310 · [20-21]
  21 it has a ledger · :1311 · [20-21]
  22 the ledger is open and an entry is left · :1312 · [22]
  23 the message's number is in range at the laying back (onOracle) · :1258-1260 · [20-21]: the same
     test; Array.modify is silent out of range; not reachable: 20 refuses first
NOT THIS FILE's (numbers 1 to 3, the caller's): the sub-proof closed its link · its plan is the
record's · it returned the merge's leavings (StagesLinks.lean:574, :575, :578).
ORDER: that of `verify-on-bytes`.

-/
import OnBytes.Model.Merge
import OnBytes.Iop.Lin
import Johnson.Desc.Own.Stretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Pend
open OnBytes OnBytes.Params OnBytes.Model

/-- The two names under which a row cannot be made. -/
def badRows : String := "internal-gamma-rows"
def badCount : String := "link-claim-count"

/-! ### the mask entry -/

/-- The next number, from n on, whose low logRows bits name a real mask row. fuel bounds the steps.
-/
def nextEntry (rows logRows : Nat) : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if n % 2 ^ logRows < rows then n else nextEntry rows logRows fuel (n + 1)

/-- The next free entry of a ledger is taken: its number, and the ledger behind. -/
def takeEntry (l : Ledger) : Option (Nat × Ledger) :=
  if !l.closed && 0 < l.left then                                                          -- [22]
    let n := nextEntry l.rows l.logRows (2 ^ l.logRows) l.next
    some (n, { l with next := n + 1, left := l.left - 1 })
  else none

/-! ### Gamma -/

/-- The rows of W that the claims' units span: the first, and the one behind the last. -/
def span (lay : WsLay) (recs : List WsRecClaim) : Except String (Nat × Nat) :=
  recs.foldlM
    (fun r c => do
      let some u := lay.U[c.ui]? | throw badRows                                           -- [8]
      pure (min r.1 u.off, max r.2 (u.off + u.rows)))
    (2 ^ 64 - 1, 0)

/-- Gamma, from row 0 on, with one claim's weights added at the rows of its unit. -/
def addClaim (lay : WsLay) (Gamma : Array E) (c : WsRecClaim) : Except String (Array E) := do
  let some u := lay.U[c.ui]? | throw badRows                                               -- [13]
  let v := wsGamma u c oneE
  unless v.size == u.rows do throw badRows                                                 -- [14]
  unless c.f.length == u.g.length do throw badRows                                         -- [15]
  unless u.off + u.rows ≤ Gamma.size do throw badRows                                      -- [16]
  pure (v.foldl (fun s x => (s.1.modify s.2 fun y => addE y x, s.2 + 1)) (Gamma, u.off)).1

/-! ### the row -/

/-- **The pending row**, and the statement's oracle messages with one entry of the message number
indexMasks taken. -/
def pendingRowO (lay : WsLay) (indexMasks : Nat) (o : WsForkOut) (claims : Nat) (S : LinShape)
    (oracles : Array Oracle) : Except String (TensorRow × Array Oracle) := do
  unless lay.m0 == S.matrixRows do throw badRows                                           -- [4]
  unless !o.recs.isEmpty do throw badCount                                                 -- [5]
  unless o.recs.length == claims do throw badCount                                         -- [6]
  unless o.rm.size == lay.lk do throw badCount                                             -- [7]
  let (first, last) ← span lay o.recs
  unless first < last do throw badRows                                                     -- [9]
  unless last ≤ lay.m0 do throw badRows                                                    -- [10]
  unless S.kRow ≤ 62 do throw badRows                                                      -- [11]
  unless lay.m0 ≤ 2 ^ S.kRow do throw badRows                                              -- [12]
  let Gamma ← o.recs.foldlM (addClaim lay) (Array.replicate last zeroE)
  let some g := Own.weightsOnRows S first (Gamma.extract first last) | throw badRows     -- [17-19]
  let some l := (oracles[indexMasks]?).bind (·.ledger) | throw unnamed                   -- [20-21]
  let some (c, l') := takeEntry l | throw unnamed
  let row : TensorRow :=
    { g := g, psi := o.rm.toList.reverse, masks := [(⟨indexMasks, c⟩, o.beta)], target := o.fvp }
  pure (row, oracles.modify indexMasks fun x => { x with ledger := some l' })

end VerifiableInference.Desc.First.Pend
