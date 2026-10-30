-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Frames1.lean: the first chain from a list of blocks, and the record
`FileDescription` from three chains. General in the first chain's state, so that the proof file's
description (OnlineDescriptionFromBlockTables.lean) and test harnesses use one text.
  `guardMark`    a block, with a refusal where its decision leaves a mark of failure in the state
  `sameReply`    the test that the guard on the reply asks
  `shapeOf`      the name and place of every block of the first chain, from the plan alone
  `FrameRole`, `roleOf`   what a block of the kind `frame` is for, by its place
  `faultsOf`     what is wrong with a collection of blocks, in words
  `chainBy`      the first chain
  `fileDescBy`   the record `FileDescription Inst`
Blocks of the kind `frame`. Besides the blocks of the numbered kinds, a module may supply blocks
without a round, of the kind `frame`, for these places: the chain's first block (no segment, piece
0); where segment l starts (piece 0) and ends (its last piece); the chain's last block, which does
have a round; and any place of a kind (segment l, that place's piece), in which case its decision is
joined after the decision of the block that stands there (`Block.andThen`).
`isLeaveStep` and `filledLinks` are bookkeeping: they say which named steps of `verify-on-bytes`
such blocks replace, and no decision depends on them. `isFrameStep` and `stepName` are also
read by two tests of OnlineDescriptionFromBlockTables.lean: `lackingAt` uses the first to decide whether a block is asked for
after a segment's first place, and `partsAt` uses the second to match a lot's `still`.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.ProofFile.FillCore
import Johnson.Desc.ProofFile.Places
import Johnson.Desc.MadeOk
import Johnson.Desc.Ok.FormRules

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription KindName Place roundlessBlock)
open VerifiableInference.Desc.First

variable {σ : Type}

/-! ### A block as it is put into a chain -/

/-- The block `b`, with a refusal where its decision leaves a mark of failure in the state. Several
functions of State.lean mark the state and go on, and `Block.step` does not look at the mark.
Without this the mark would be noticed only at the end of the chain. -/
def guardMark (b : Block S Cl) : Block S Cl :=
  { b with decide := fun s rs gs =>
      (b.decide s rs gs).bind fun t =>
        match t.failed with
        | none => .ok t
        | some m => .error ("marked: " ++ m) }

/-- The two states hold the same reply. This is the test that the driver's guard asks
(FillCore.lean: `Gather.same`): no step may write the reply, except the decision at the one place
that hears it. -/
def sameReply (t s : S) : Bool := t.out.reply == s.out.reply

/-! ### The shape -/

/-- The kinds of the segments, in order, for the driver. -/
def subsOf (Z : Pub) : List ModelPart := Z.p.built.links.toList.map fun X => subOf X.kind

/-- The name and place of every block of the first chain, in the order of the flat list. It is
computed from the plan alone: the driver's chain over blocks that do nothing. -/
def shapeOf (Z : Pub) : Except String (List (String × Place)) := do
  let spots ← orSay "the table of steps names a kind that is not known" (spotsOf Z.cuts)
  let idle : List (Block Unit Unit) := spots.map fun p =>
    { (roundlessBlock p.name 1 none 0 .ok : Block Unit Unit) with place := p.place }
  let c ← chainC idle (subsOf Z) Frames.unguarded
  pure (c.blocksInOrder.map fun b => (b.name, b.place))

/-- The name of a step of `verify-on-bytes` as printouts spell it. -/
def stepName (look : String) : String := if look == "seal.behind" then "seal" else look

/-! ### Blocks of the kind `frame` -/

/-- What a block of the kind `frame` is for. -/
inductive FrameRole where
  | front
  | lay (l : Nat)
  | clear (l : Nat)
  /-- its decision is joined after that of the block of this name -/
  | behind (l : Nat) (place : String)
  /-- a place of the list of places (the chain's last block): treated like a place of a kind -/
  | common
  | stray
  deriving BEq

/-- The role of a block of the kind `frame` at the place `p`: by chain, segment and piece, looked up
in the shape. The start and the end of a segment are told by the names that `Link.blocksInOrder` (Block.lean)
gives its own two blocks there, over the name that the driver's `linkAt` gives the segment. -/
def roleOf (shape : List (String × Place)) (p : Place) : FrameRole :=
  match shape.find? fun b => b.2.chain == p.chain && b.2.link == p.link &&
      b.2.piece == p.piece, p.link with
  | none, _ => .stray
  | some b, none =>
    if b.2.kind != KindName.frame then .stray
    else if b.1 == frontName then .front else .common
  | some b, some l =>
    if b.2.kind != KindName.frame then .behind l b.1
    else if b.1 == s!"link {l}" ++ ": laid" then .lay l
    else if b.1 == s!"link {l}" ++ ": cleared" then .clear l
    else .stray

/-- The step of `verify-on-bytes` that enters a segment: the silent step after the segment's first
call. -/
def isFrameStep (p : Spot) (look : String) : Bool :=
  p.place.link.isSome &&
    (p.place.kind == KindName.K2 || (p.place.kind == KindName.K1 && p.place.piece == 1)) &&
    look.endsWith ".quiet"

/-- The step of `verify-on-bytes` that leaves a segment: the silent step after the closing's call.
-/
def isLeaveStep (p : Spot) (look : String) : Bool :=
  p.place.link.isSome && p.place.kind == KindName.K10 && look.endsWith ".quiet"

/-- The segments whose entering step, and those whose leaving step, blocks of these roles replace.
-/
def filledLinks (Z : Pub) (roles : List FrameRole) : List Nat × List Nat :=
  let spots := (spotsOf Z.cuts).getD []
  let holds := fun (name : String) =>
    spots.any fun p => p.name == name && p.cuts.any fun c => isFrameStep p c.look
  let enters : FrameRole → Option Nat
    | .lay l => some l
    | .behind l n => if holds n then some l else none
    | _ => none
  let leaves : FrameRole → Option Nat
    | .clear l => some l
    | _ => none
  (roles.filterMap enters, roles.filterMap leaves)

/-- What is wrong with a collection of blocks, in words; empty if nothing is. `own`: all the blocks.
Faults: a block at no place of the shape; a block of the kind `frame` where none can be supplied (at
no place, or at the driver's own block after the batching); a block of that kind, other than the
chain's last, that has a round, states claims or acts after the batching; a block for the start or
the end of a segment whose test on the plan says no (only its decision is passed on, so that test
would be asked nowhere); two blocks with one role; two blocks at one place. -/
def faultsOf (shape : List (String × Place)) (own : List (Block S Cl)) : List String :=
  let fr := (own.filter fun o => o.place.kind == KindName.frame).map fun o =>
    (roleOf shape o.place, o)
  ((own.filter fun o =>
      o.place.kind != KindName.frame && !(shape.any fun b => b.2 == o.place)).map fun o =>
    "the block " ++ o.name ++ " stands at no place of the chain") ++
  (fr.filterMap fun x =>
    let o := x.2
    if x.1 == .stray then some ("the block " ++ o.name ++ " stands where no frame can be supplied")
    else if x.1 != .common && !(o.rounds.isEmpty && o.hasNoClaimsAndNothingAfter) then
      some ("the block " ++ o.name ++ " is of the kind frame and has a round " ++
        "or states claims, or acts after the batching")
    else if !o.planOk && (match x.1 with | .lay _ => true | .clear _ => true | _ => false) then
      some ("the block " ++ o.name ++
        " starts or ends a link, and its test on the plan says no: only " ++
        "its decision is passed on, so that test would be asked nowhere")
    else if 1 < (fr.filter fun y => y.1 == x.1).length && x.1 != .common then
      some ("the role of the block " ++ o.name ++ " is taken by more than one block")
    else none) ++
  (shape.filter fun b => 1 < (own.filter fun o => o.place == b.2).length).map fun b =>
    "the place " ++ b.1 ++ " is taken by more than one block"

/-- The first chain. `base`: the blocks at the places of a kind and the last block, in order. `fr`:
the blocks of the kind `frame`, each with its role. `road`: FillCore.lean's `Gather`. -/
def chainBy (Z : Pub) (base : List (Block σ Cl)) (fr : List (FrameRole × Block σ Cl))
    (road : Gather σ Cl) : Except String (Chain σ Cl) :=
  let at_ := fun (r : FrameRole) => (fr.find? fun x => x.1 == r).map fun x => x.2
  -- By the segment and the name: the name alone would not say whose segment's block is joined.
  let behind : Block σ Cl → FrameRole → Bool
    | b, .behind l m => b.name == m && b.place.link == some l
    | _, _ => false
  let joined := base.map fun b =>
    match fr.find? fun x => behind b x.1 with
    -- What is joined after a block is guarded here, at every place. The driver's guard leaves the
    -- decision at the place that hears the reply free, and something could be joined there.
    | some x => b.andThen b.name (x.2.guarded road.same fun _ => false)
    | none => b
  let front : Block σ Cl :=
    -- No lot of OnlineDescriptionBlocks.lean supplies a first block. A block that tests nothing is intended here.
    match at_ .front with
    | some o => { o with name := frontName }
    | none => idleFront
  let frames : Frames σ Cl :=
    -- Where no block is supplied for the start or the end of a segment, the state is passed on and
    -- nothing is tested. Test harnesses need that. The proof file's description does not reach
    -- these two cases: `lackingAt` (OnlineDescriptionFromBlockTables.lean) refuses if such a block is missing.
    { toGather := road, first := front
      lay := fun l t =>
        match at_ (.lay l) with
        | some o => o.decide t [] []
        | none => .ok t
      clear := fun l t =>
        match at_ (.clear l) with
        | some o => o.decide t [] []
        | none => .ok t }
  chainC joined (subsOf Z) frames

/-! ### The description -/

/-- The record `FileDescription Inst`. `c`: the first chain, at a state from which `get` reads the carried
record `S`; `start`: its first state; `A`, `B`: the two later chains; `mk`: what computes the
segments' records for the tests on the instance; `o`: stands for the second hash function
(Pub.lean: `SecondHashFunctionArgument`). -/
def fileDescBy (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub) (A : SharedSeat) (B : SecondSeat)
    (get : σ → S) (start : InstPub → σ) (c : Chain σ Cl) : FileDescription Inst :=
  { S₁ := σ, S₂ := A.σ, S₃ := B.σ, Cl := Cl, plans := Z.D
    tableDepth := Z.depth
    -- Limit: both tables are empty. `wantedOk` and `owedOk` are not part of `planOk`, and `run`
    -- does not ask them. So no table made apart from the blocks is held against the blocks'
    -- places and rounds, or against the messages that a block names before its first draw.
    wanted := [], owed := []
    -- The two later chains' own tests on the plan; the test on the prices of the three chains'
    -- rounds (Johnson/Desc/MadeOk.lean); and the test that no entry of the planner's seven plans is
    -- without a test on its count (Johnson/Desc/Ok/FormRules.lean). That file says what a yes of
    -- the last one gives, and that it is meant for a record that the planner has made, as here.
    fileOk := A.fileOk && B.fileOk && VerifiableInference.Desc.proofOk Z.p.chains.made &&
      Johnson.Desc.Ok.everyOk Z.p.chains.made
    okStart := fun x => okBy o mk Z x && A.okInst x.pub, XiPub := InstPub
    pub := fun x => x.pub, start₁ := start, start₂ := A.start
    start₃ := fun p s₁ s₂ =>
      if !(get s₁).fin then .error "the first chain does not stand at its end"
      else
        match A.ended s₂ with
        | none => .error "the shared chain has not ended"
        | some e => B.start p (get s₁) e
    -- The later chains state no claims. `Chain.retype` changes the type of claims, and tests on the
    -- plan that they have no segment and state none.
    first := c, shared := A.chain.retype, second := B.chain.retype
    -- The reply that was heard is the reply that is asked about; the request's words in the state
    -- are still the instance's (a block could have written them); `A.ended` and `B.done` say yes.
    fin := fun x s₁ s₂ s₃ =>
      (get s₁).finAsked x.asked && (get s₁).req == Verify.words32 x.pub.request &&
        (A.ended s₂).isSome && B.done s₃ }

end ProofFile
