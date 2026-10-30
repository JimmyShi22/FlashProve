-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/ReadsK.lean: what the law of the proximity test asks of the reading of a view:
one proposition, `ReadsK`.

Definitions alone. The proximity test (the kind K12) is a block: `Block.step` hands its decision the
test's rounds as a view shows them, without the sealed digest (rs), and the columns that its rounds
open, laid into groups, one group for each tree that a declared round opens, in the declared order
(gs). The library's proved chain of fold, code switch and base case (`OnBytes.Slice.Chain`) speaks
of written rounds: typed transcripts `b : c.Bl`, whose messages hold written oracles. The law says:
a yes of the block gives the chain's yes in the field, `c.Acc`, if the view is the written
transcript's. `ReadsK` is that "if", and nothing else.
Main names:
  `ReadsK`, with five fields:
  `rounds`: behind the test's first round ("BAT", which sends nothing and draws one element) the
    rounds shown are the chain's written rounds, block by block (`Chain.rvs`), each without the
    sealed digest.
  `shown`: every column in a group that belongs to a later stage is the column, at its position, of
    the tree that the code switch into that stage has written (`ShownLater`).
  `members`, `mask`: g names, for each place t of the book of trees and each position x, a column:
    at the place of member j's tree it is the written oracle `o j`'s, at the place of the first
    fold's mask's tree it is `oF`'s.
  `groups`: the groups of the first switch are, tree by tree in the book's order (`P.ts`), at the
    tree's own list of positions under what the written round "CS" drew, columns that g names
    (`GroupsAre`, Johnson/Desc/K12/Law/FirstRead.lean).
  `laidOf`, `laidS`, `grpsS`, `firstDraws`: the declared rounds with their oracle messages, those
    behind "BAT", the groups behind the batching's, and what the first switch's written round "CS"
    drew.
Limits: The written oracles `o j` and `oF` are letters that stand in front of b in the law's
statement. They are not for whoever proves `ReadsK` to choose: they are the oracles that these
rounds wrote. At the unopened positions nothing here ties them to the view, and the words that the
law reads off them mean something only then. Where the first fold's own first message brings the
mask, `oF` is that message's oracle (Johnson/Desc/K12/Law/OwnMask.lean and K12Lemma.lean take that
form). That these rounds were sent before the test's first draw is said by no clause here
(Johnson/Desc/K12/FixedBefore.lean and Johnson/Desc/K12/Law/FirstSrc.lean speak of that). No clause
here asks a key or a width: at one of the proximity tests of the smaller stored example proof all
three keys are 0. Nothing here is about hiding.
-/
import Johnson.Desc.K12.Law.FirstRead

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw (GroupsAre)

/-- The place's declared rounds, each with its oracle messages, as Frame.lean's proximityTestKind lays them. -/
def laidOf (p : P12) : Laid := ((H2U.roundsOfNums p.nums).getD []).zip p.oracles

/-- Those behind "BAT": what the frame deals to the stages. -/
def laidS (p : P12) : Laid := (laidOf p).drop 1

/-- The groups behind the batching's: what the frame deals to the stages. -/
def grpsS (p : P12) (gs : Gs) : Gs := gs.drop (nOpen (((laidOf p).take 1).map (·.1)))

/-- What the written round "CS" of the chain's first code switch drew: the positions. -/
def firstDraws : {s : Sg} → (c : Chain s) → c.Bl → List Nat
  | _, .last _ _ _ _ _ _ _ => fun _ => []
  | _, .step _ _ _ _ _ _ _ _ dC _ _ _ _ _ _ => fun b => (rvOf dC b.2.1.2.2.1 b.2.1.2.2.2.1).poss

/-- What the law of the proximity test asks of the reading of a view. p: the place. c, b: the chain
and its written transcripts. G, P: the group under test and what is public of it on the record's
side (the library's plain Gp | GpData). o, oF: the written oracles behind the members' trees and the
first mask's. g: the written columns by the book's places. rs, gs: what Block.step hands the block's
decision. -/
structure ReadsK (p : P12) {s : Sg} (c : Chain s) (b : c.Bl) {G : Gp s} (P : GpData G)
    (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc) (g : ℕ → ℕ → Option (List UInt64))
    (rs : List Fmt.RoundView) (gs : Gs) : Prop where
  rounds : rs.drop 1 = (c.rvs b).map noDigest
  shown : ShownLater c b (laidS p) (grpsS p gs)
  members : ∀ j x, g (P.tp j) x = some (colW (P.d j) (o j) x)
  mask : ∀ x, g P.ft x = some (colW P.dF oF x)
  groups : GroupsAre (Positions.ofDraws s.C.a (firstDraws c b)) P.log g P.ts
    (grpS (laidS p) (s.h + s.g) (grpsS p gs))

end H2K.JointK
