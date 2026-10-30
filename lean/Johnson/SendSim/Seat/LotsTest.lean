-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/LotsTest.lean: executable tests over all jobs of the kind K1 on the first chain
at once, for the public premises of hand_of_lots and budAtLots
(Johnson/SendSim/Seat/AtDescLots.lean) and for whether the statements there have content. The file
holds definitions only.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". In short: a job (SendJob) is what
the honest sender is given at one place: the place's public numbers P, the number of its first new
message, the data, and ride: which of its messages is the fresh mask table of a later folding step,
sent along ahead of that step. The two lists of jobs are lotJobs (Johnson/SendSim/Seat/Lot.lean: the
first segment's opening, each segment's reads and digits) and wJobs (Johnson/SendSim/Seat/LotW.lean:
the request's own table). A book (ProverCoinCounts, Johnson/Desc/ProofFile/Honest/Frame.lean) says which runs of
a part's coins a later part is given, to spend or to carry. Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. Z is the public part. G is the ground: the segments' data computed from Z.
  lotPars Z G        the public numbers P and the tables sent along (ride) of the jobs of the two
                     lists, in the lists' order. Its code copies that of lotJobs ++ wJobs and keeps
                     two of a job's four fields, so it needs neither the numbering of new messages
                     nor the data. lotPars_eq (LotsTestTie.lean) proves that the two agree.
  laterPars Z G      the public numbers at each segment's reads and digits alone.
  lotsClearB         accepts if the book passes bookClearAnyB (Johnson/SendSim/At/WideTest.lean) at
                     every job's sender.
  lotsFitB           accepts if every job fits its place (sendFits). That is no premise of the
                     statements. Where a job does not fit, what it discloses is the error value on
                     both sides of both equations: exact then says nothing, and fresh speaks of the
                     sender's coins alone (AtDescLots.lean, Limits). The test shows where the
                     statements have their full content.
  placesApartB F     accepts if no two members of the first chain's list of sub-protocols of the
                     description F are at one place.
  lotsReadsB F       accepts if the test on the description's queries (readsWithinB,
                     Johnson/SendSim/Seat/ReadsTest.lean) accepts at every job, at the number of
                     trees that the description states before the first member at the job's place
                     (where there is no such member, at the number of all the chain's trees).
  noMaskB P          accepts if no message of P has a mask row.
  laterNoMaskB       accepts if noMaskB accepts at each segment's reads and digits.
  shapeLaterNoMaskB  a test on the request's shape alone that implies laterNoMaskB
                     (laterNoMask_of_shape, LotsTestTie.lean). It accepts if no message of any
                     segment that is sent after the segment's first prover message has a mask row.
  armOf, lotsArms    for a printout: at each job, whether the sender's entries are within its number
                     of coins, and for each address that the book gives a run, how that address
                     meets or fails the condition on a spender.

How it fits. The tests serve the public premises of hand_of_lots and budAtLots, lemmas that are
meant as steps toward index privacy (Johnson/WholeKey/Statement.lean); nothing in this folder
derives index privacy from them. None is one of the release's goal statements. What an accepting
test gives is proved in Johnson/SendSim/Seat/LotsTestTie.lean. Of this folder the file loads only
the test files WideTest.lean and ReadsTest.lean and the files beneath them (BookTest.lean,
Fresh.lean, Sim.lean), which hold definitions, statements and small lemmas. It loads none of the
proofs of exact or fresh, so that a program can evaluate the tests without these. It does load
Johnson/Desc/ProofFile/Honest/K1/PlaceW.lean and, through it, much of the library.

Limits.
No test is evaluated here.
At which values the tests must be evaluated. For the premise of hand_of_lots: at the public part Z
and the ground Bs.G₀ of IM.Open (the value of ProofFile.blankBy ProofFile.pureRoad.links Z: IM.Open.blank,
Johnson/IMR/SeatOpen.lean), at the book that the rule's caller picks and at the order orderOf F. For
the premise of budAtLots: at the description F of the same IM.Open. At another ground the tests
speak of other jobs: at a ground without segments they see the opening and the request's own table
alone. In the scope of the release's goals, at the hash function OnBytes.secondHashFunction, lotPars Z Bs.G₀ has
52 entries (jobs_52_in_scope, LotCount.lean, with lotPars_eq).
A book without entries passes lotsClearB. Whether the book that the rule's caller picks is the right
one for an honest run is not tested here.
Where a test rejects, nothing follows, except for lotsClearB and lotsFitB, whose ties
(LotsTestTie.lean) are equivalences.
lotsReadsB counts as readsWithinB does: a position counts once for each opening and each round. So
the test can reject where the bound on queried positions holds. placesApartB asks more than is
needed: it looks at all places of the chain, not at the jobs' places alone.
The tests cover the places of the kind K1 on the first chain alone. That chain has other sendings of
new tables, of the kinds K2 and K12; they are not covered (AtDescLots.lean, Limits).
-/
import Johnson.SendSim.At.WideTest
import Johnson.SendSim.Seat.ReadsTest
import Johnson.Desc.ProofFile.Honest.K1.PlaceW

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)

variable {Xi : Type}

/-- The public numbers at each segment's reads (moment 1) and digits (moment 2), in the order of
lotJobs. -/
def laterPars (Z : ProofFile.Pub) (G : ProofFile.Ground) : List K1.Par :=
  G.built.toList.zipIdx.flatMap fun (Y, l) =>
    match K1.linkNumbers G Y with
    | none => []
    | some (pr, pd, _, _) =>
      [K1.parLater G.first (K1.gpOf Z) l pr 1, K1.parLater G.first (K1.gpOf Z) l pd 2]

/-- The public numbers and the tables sent along of the jobs of the two lists, in the lists'
order. -/
def lotPars (Z : ProofFile.Pub) (G : ProofFile.Ground) : List (K1.Par × (Nat → Option Ride)) :=
  ((K1.firstPar G.first (K1.gpOf Z), rideOf (firstFold G.first)) ::
      (laterPars Z G).map fun P => (P, rideOf none)) ++
    ((linMessageW Z.first.lin).map fun msg =>
      (K1.parW Z.first (wGp Z) 4 msg, rideOf (wFold Z.first.lin))).toList

/-- The book passes the executable condition bookClearAnyB at every job's sender. -/
def lotsClearB (Z : ProofFile.Pub) (G : ProofFile.Ground) (Bk : ProverCoinCounts) (ord : List Place) : Bool :=
  (lotPars Z G).all fun x => bookClearAnyB x.1 x.2 Bk ord ⟨x.1.place, 0⟩

/-- Every job fits its place. -/
def lotsFitB (Z : ProofFile.Pub) (G : ProofFile.Ground) : Bool :=
  (lotPars Z G).all fun x => sendFits x.1 x.2

/-- No two members of the first chain's list of sub-protocols are at one place. -/
def placesApartB (F : FileDescription Xi) : Bool := decide (F.first.blocksInOrder.map (·.place)).Nodup

/-- The test on the description's queries accepts at every job, at the number of trees before the
first member at the job's place. -/
def lotsReadsB (F : FileDescription Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground) : Bool :=
  (lotPars Z G).all fun x =>
    readsWithinB F x.1 (treesOf F.first.blocksInOrder (F.first.blocksInOrder.takeWhile (·.place != x.1.place)))

/-- No message of the place has a mask row. -/
def noMaskB (P : K1.Par) : Bool :=
  (List.range P.sent.size).all fun k => (shapeAt P k).maskRows == 0

/-- No message at a segment's reads or digits has a mask row. -/
def laterNoMaskB (Z : ProofFile.Pub) (G : ProofFile.Ground) : Bool := (laterPars Z G).all noMaskB

/-- In the request's shape, no message that is sent after its segment's first prover message has a
mask row. -/
def shapeLaterNoMaskB (sh : ReqShape) : Bool :=
  sh.link.all fun L => L.messages.all fun m => m.moment == 0 || m.shape.maskRows == 0

/-- The first clause of the condition on a spender (SpenderClearAny,
Johnson/SendSim/At/FreshWide.lean) that accepts at the address p for the coins of o, in the order of
spenderClearAnyB. Spending entries that cover no coin are named apart from the clause on mask
entries, which they also meet. -/
def armOf (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) :
    String :=
  if (Bk.spentBy o p).isEmpty then "spends none of this sender's coins"
  else if (Bk.spentBy o p).all fun e => e.count.e == 0 && e.count.f == 0 then
    "spends no coin: its spending entries have length 0 (allowed)"
  else if maskB P ride Bk ord o p then "spends only free mask entries of this sender (allowed)"
  else if foldAnyB P ride Bk ord o p then
    "spends the coefficients of a table sent along with this sending (allowed)"
  else "spends this sender's coins in a way that no clause allows (the test on the book rejects)"

/-- For a printout. For each job: its place; whether the sender's entries are within its number of
coins (withinB); and, for each address that some entry of the book gives a run (the addresses that
bookClearAnyB ranges over), what armOf says of it for this job's sender's coins. -/
def lotsArms (Z : ProofFile.Pub) (G : ProofFile.Ground) (Bk : ProverCoinCounts) (ord : List Place) :
    List (Place × String × List (Addr × String)) :=
  (lotPars Z G).map fun x =>
    (x.1.place,
      if withinB x.1 x.2 Bk ⟨x.1.place, 0⟩ then
        "the sender's entries are within its number of coins"
      else "an entry of the sender exceeds its number of coins (the test on the book rejects)",
      (Bk.ahead.map (·.spender)).eraseDups.map fun p =>
        (p, armOf x.1 x.2 Bk ord ⟨x.1.place, 0⟩ p))

end OnBytes.SendSim.Seat
