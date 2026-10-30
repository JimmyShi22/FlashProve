-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Fill/D1At.lean: the public data that the layer `fillP1` takes
(`FillP1.PubData`, Johnson/Top/H0/Fill/PubP1.lean), as a closed term of the proof file's public
part; and four further terms off the planner's output, for facts on the verifier's state that are no
items of the table. Definitions only; nothing is proved here.


  `d1At Z`   the three fields, each read off `Z : ProofFile.Pub`:
    `lay`   the layout of the committed table: `Z.p.X.layers.wsLay`
    `lin`   the shape of a row on that table: `Z.first.lin`
    `ncl m` the number of claims on that table that the planner's link number `m` states (its field
            `NCL`); 0 where there is no such link
  `tlAt Z m`  the planner's data of the closing part of link `m`'s sub-proof (the structure
    `HTailF2`), off which the approximate range proof (this library: the smallness test) reads its
    numbers; read off the links that the IOP's own sub-protocols are made at
    (`ProofFile.blankBy ProofFile.pureRoad.links Z`); none where these are not made or have no such link
  `fvsAt Z`   for each link in order: does its sub-proof leave a row on the committed table
  `free0Of cs M ix`   how many entries the fresh ledger of the message number `ix` has: the verifier
    program's own count of free mask entries (`OnBytes.Send.freeMaskEntries`) at the shape number
    `ix` of `M` and the code table `cs`; 0 where `M` has no such shape
  `startB Z M ix`   a test that can fail: `M` has a shape number `ix`, and the planner's request
    announces just one message at the chain's start, of that shape

Why these. They are what the IOP's own sub-protocols hand the frame
(Johnson/Desc/ProofFile/Lot/Frames.lean: `framesOf Z.p.built.links Z.first Z.p.X`;
Johnson/Top/H0/Walk/FrameLot.lean: `rowOf`, `fvsOf`), and the data off which the sub-protocol of the
approximate range proof reads its numbers (Johnson/Desc/ProofFile/Lot/K8.lean: `k8Par`). That they
are the right ones is shown nowhere here. Meant at `free0Of`: `cs` := `Z.first.codes`, `M` the
planner's list of the first chain's messages' shapes (Johnson/Desc/K12/Door/MsgShapes.lean), `ix`
the table's number `Numbers.indexNo`.

Limits. `tlAt Z m` is the planner's structure: its list of tables is not closed there. No law on
these values is imported or stated. `free0Of` and `startB` have been evaluated nowhere.

-/
import Johnson.Top.H0.Fill.PubP1
import Johnson.Top.H0.Walk.FrameLot
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.ProofFile.OnlineDescriptionPublicPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.FillP1

/-- How many entries the fresh ledger of the message number ix has: the verifier program's own
count, at that message's shape in the list M and the code table cs. 0 where the list has no such
shape. -/
def free0Of (cs : OnBytes.Codes) (M : List OnBytes.OracleShape) (ix : Nat) : Nat :=
  match M[ix]? with
  | some sh =>
    OnBytes.Send.freeMaskEntries sh.maskRows (cs.mask.getD sh.maskCode default).ell sh.answers
  | none => 0

/-- A test that can fail: the plan's request announces just one message at the chain's start, and
its shape is the shape number ix of M. -/
def startB (Z : ProofFile.Pub) (M : List OnBytes.OracleShape) (ix : Nat) : Bool :=
  match M[ix]? with
  | some sh => Z.first.shape.atStart.map (·.shape) == [sh]
  | none => false

/-- The planner's data of the closing part of link m's sub-proof. -/
def tlAt (Z : ProofFile.Pub) (m : Nat) : Option OnBytes.Model.HTailF2 :=
  ((ProofFile.blankBy ProofFile.pureRoad.links Z).bind fun G => G.built[m]?).map (·.tl)

/-- For each link in order: does its sub-proof leave a row on the committed table? -/
def fvsAt (Z : ProofFile.Pub) : List Bool := Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links

/-- **The public data of `fillP1`, of the proof file's public part alone.** -/
def d1At (Z : ProofFile.Pub) : PubData where
  lay := Z.p.X.layers.wsLay
  lin := Z.first.lin
  ncl := fun m => ((Z.p.built.links[m]?).map (·.NCL)).getD 0

end VerifiableInference.Desc.First.FillP1
