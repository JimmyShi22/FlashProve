-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TableOfSteps.lean: THE TABLE OF STEPS OF THE PROOF FILE's FIRST CHAIN: for
each of the 358 numbers in the chain's flat list ONE step on the whole shape and ONE test on
values, as terms with code in the public part Z and the maker's ground G: the very terms to which
the seats' frames pin the letters g and vals (FrameForm.lean: firstZA g vals). Definitions alone;
nothing is evaluated; the laws for 258 of the numbers are in TableFrames.lean, TableFramesV.lean,
TableSites.lean and TableSwitch.lean.

  `StepA` := ShA → Except String ShA, `ValsA`, `Cell` := StepA × ValsA; `noStep`, `noVals`,
    `noCell`: the step that refuses with a given word; no test (true); the two as a cell: what a
    cell answers where something that it looks up is missing.
  `Tab.laid`, `opening`, `switch`, `switchHead`, `finish`, `siteAt`, `lookCalls`, `lookDigits`,
    `lookHead`, `k4`, `k5`, `reads`, `readsHead`, `draw`, `digits`, `batch`, `behind`, `equation`,
    `close`, `shut`, `cleared`, `sendW`: one cell a sort of member; where a record of the plan is
    looked up and lacks, the cell refuses.
  `Tab.linkRow`, `headRow`, `backRow`; **`Tab.cells Z G`** : Nat → Cell (Table.lean's table);
    **`Tab.g`**, **`Tab.vals`**: its two halves.

Limits. THE CELLS batch, behind, equation AND close (100 OF THE 358 NUMBERS) ARE TIED TO A FRAME BY
NONE OF THE FOUR FILES NAMED ABOVE. At the 25 batching members the seats' laws give only a weaker
form of "carries" (CarriesV, BatchFrames.lean). THE FULL SIZE ALONE: the links are told apart by l %
2, l == 24 and l / 2, not by the plan's own readers: at another public part the table lays cells of
the wrong sort without a word. FROM 358 ON THE TABLE ANSWERS WITH THE SEAL's CELL (Table.lean), in
silence; at 0 the cell is the identity. The reader's structure (Verify.Public) is spelled in three
ways: Z.p.X, G.W and P5J.At.X Z. At the code switch's 25 places and at the proximity test the step
has a guard on the shape in front: where it refuses, the step refuses. The lookups' cells find their
site by a search. Several steps are as dear as the member's own text (they run it at blanks), and so
are several tests on values (the batching's; those behind it; the reads' midV; the proximity
test's). Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Table
import Johnson.AtFull.Shape.Numbers
import Johnson.AtFull.Shape.OpeningFrame
import Johnson.AtFull.Shape.ValueFrames
import Johnson.AtFull.Shape.CloseInOrder
import Johnson.AtFull.Shape.SwitchEndsBoth
import Johnson.AtFull.Shape.TestReturnsFrame
import Johnson.AtFull.Shape.LookFrames
import Johnson.AtFull.Shape.HeadDigitsFrame
import Johnson.AtFull.Shape.K4Fit
import Johnson.AtFull.Shape.ReadsFrames
import Johnson.AtFull.Shape.BattK6Frames
import Johnson.AtFull.Shape.ReplyFrame
import Johnson.AtFull.Shape.SendWFrame
import Johnson.AtFull.Shape.TestFrame
import Johnson.AtFull.Shape.BatchCellsAtt
import Johnson.Desc.ProofFile.Honest.K5.Law.ShapeFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law.Tests
open VerifiableInference.Desc.K9 (testsWhere)
open VerifiableInference.Desc.K9.Shape
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape
open Johnson.Desc.First.Walk.Seat (fvsOf pubOf)
open ProofFile.Honest.K3 (Site lookSites)
open ProofFile.Honest.K3.Law.AtThr (callsG digitsG headDigitsG headVals)
open ProofFile.Honest.K10.YesFree
open H2K5.Honest (valsTS)
open IM (subAt k2P k2PlaceF)

/-- A step on the whole shape. -/
abbrev StepA : Type := ShA → Except String ShA

/-- A member's named tests on values: of the state, its rounds and the columns that it is shown. -/
abbrev ValsA : Type := S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool

/-- No step is laid here. -/
def noStep (why : String) : StepA := fun _ => .error why

/-- No test on values. -/
def noVals : ValsA := fun _ _ _ => true

/-- A step and its tests. -/
abbrev Cell : Type := StepA × ValsA

def noCell (why : String) : Cell := (noStep why, noVals)

namespace Tab
variable (Z : ProofFile.Pub) (G : ProofFile.Ground)

/-- K1's numbers at a later moment of link l. -/
def k1P (l pc m : Nat) : VerifiableInference.Desc.K1.Par :=
  VerifiableInference.Desc.K1.parLater G.first (VerifiableInference.Desc.K1.gpOf Z) l pc m

def nums (l : Nat) : Option (Nat × Nat × Option (List Nat) × Option (List Nat)) :=
  (G.built[l]?).bind (VerifiableInference.Desc.K1.linkNumbers G)

def laid (l : Nat) : Cell := (liftQ (laidGS l), noVals)

def opening : Cell :=
  match Z.p.built.links[0]? with
  | some X =>
    match Z.p.X.G[X.g]? with
    | some hp =>
      (openingA
          (VerifiableInference.Desc.K1.firstPar G.first (VerifiableInference.Desc.K1.gpOf Z))
          (openZeroG ⟨pubOf X, 0, Z.p.X.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩
            (fvsOf Z.p.built.links) Z.first.lin.kCol), noVals)
    | none => noCell "the opening: no plan"
  | none => noCell "the opening: no link"

/-- The code switch at a link's first place, with the frame's "opened" behind it (l from 1 to 23):
the guard linkGd in front of the step; the test on values is switchW. -/
def switch (l : Nat) : Cell :=
  match (P1K2.prepOf Z G).bind fun P => P1K2.numsAt P (some l), P1K2.pureLetters G l,
      Z.p.built.links[l]? with
  | some n, some HP, some Y =>
    if l % 2 == 1 then
      match Z.p.X.A[Y.g]? with
      | some p => (optE fun y =>
          if linkGd (k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n) y
          then (switchU Z { chain := 1, link := some l, piece := 1, kind := .K2 } n HP y).bind
              (quietE (openAttG (attPar Y p l)))
          else none,
        fun s _ _ => switchW s)
      | none => noCell "the switch: no plan"
    else
      match Z.p.X.G[Y.g]? with
      | some hp => (optE fun y =>
          if linkGd (k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n) y
          then (switchU Z { chain := 1, link := some l, piece := 1, kind := .K2 } n HP y).bind
              (quietE (openLayG (layPar Z.p.X Y hp l)))
          else none,
        fun s _ _ => switchW s)
      | none => noCell "the switch: no plan"
  | _, _, _ => noCell "the switch: no numbers"

def switchHead : Cell :=
  match (P1K2.prepOf Z G).bind fun P => P1K2.numsAt P (some 24), P1K2.pureLetters G 24 with
  | some n, some HP =>
    (optE fun y =>
        if headGd (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } "" .head n) HP y
        then switchU Z { chain := 1, link := some 24, piece := 2, kind := .K2 } n HP y
        else none,
      fun s _ _ => headW HP s)
  | _, _ => noCell "the switch at the head: no numbers"

def finish : Cell :=
  match (P1K2.prepOf Z G).bind fun P => P1K2.numsAt P none with
  | some n => (optE fun y =>
      if finGd (k2P Z k2PlaceF "" .finish n) y
      then ((finFrontU y).bind (finU (k2P Z k2PlaceF "" .finish n))).bind finBehindU
      else none,
    fun s _ _ => switchW s)
  | none => noCell "the finish: no numbers"

def siteAt (l : Nat) (d : Bool) : Option Site :=
  (lookSites Z).find? fun s => s.link == l && s.digits == d

def lookCalls (l : Nat) : Cell :=
  match siteAt Z l false with
  | some s => (liftQ (callsG s.shape s.p.first), noVals)
  | none => noCell "the lookup: no site"

def lookDigits (l : Nat) : Cell :=
  match siteAt Z l true, lookUC Z.p.X l with
  | some s, some (u, c) => (liftQ (digitsG s.shape s.p.first u c), noVals)
  | _, _ => noCell "the lookup on the digits: no site"

/-- The lookup on the head's own digits. -/
def lookHead : Cell :=
  match siteAt Z 24 true with
  | some s => (liftQ (headDigitsG s.shape s.p.first Z.p.X), fun st _ _ => headVals Z.p.X st)
  | none => noCell "the lookup on the head's own digits: no site"

def k4 (g : Nat) : Cell :=
  match G.W.G[g]? with
  | some hp =>
    let p : OnBytes.Desc.First.K4.Par :=
      { name := "", link := 0, piece := 3, before := [], k3Runs := true, P := G.W.layers, hp := hp
        g := g }
    (liftO (k4StepW p), fun s rs _ => k4ValsV p s rs)
  | none => noCell "K4: no plan"

/-- The attention's own rounds, by group (another house's step; its test on values, k5V, is true at
every state: no test). -/
def k5 (g : Nat) : Cell :=
  match (P5J.At.X Z).A[g]? with
  | some a => (liftQ (ProofFile.Honest.K5.k5Q (ProofFile.Honest.K5.parAt Z g a).own), ProofFile.Honest.K5.k5V)
  | none => noCell "K5: no plan"

def reads (l : Nat) : Cell :=
  match nums G l with
  | some (_, _, rd, _) =>
    if l % 2 == 0 then
      match G.W.G[l / 2]? with
      | some hp => (readsA (readsGS (k1P Z G l 4 1) l rd (tailSh hp.tl)) (k1P Z G l 4 1), noVals)
      | none => noCell "the reads: no plan"
    else
      match G.W.A[l / 2]? with
      | some A => (readsA (readsAttGS (k1P Z G l 4 1) l rd A) (k1P Z G l 4 1),
          fun s rs gs => midV (k1P Z G l 4 1) l rd (valsTS A) s rs gs)
      | none => noCell "the reads: no plan"
  | none => noCell "the reads: no numbers"

def readsHead : Cell :=
  match nums G 24 with
  | some (_, _, rd, _) =>
    (readsA (readsHeadGS (k1P Z G 24 5 1) rd ⟨⟨1, some 24, 5, .K1⟩, G.W.hS, G.W.HLy, G.W.H⟩)
        (k1P Z G 24 5 1),
      fun s rs gs => midV (k1P Z G 24 5 1) 24 rd
        (fun m => (m.covered G.W.hS.T G.W.hS.V).toOption.isSome) s rs gs)
  | none => noCell "the head's reads: no numbers"

def draw (l : Nat) : Cell :=
  match G.built[l]? with
  | some Xl => (liftQ (drawStep (ProofFile.k8Par Z G Xl l)), noVals)
  | none => noCell "the draw: no link"

def digits (l : Nat) : Cell :=
  match nums G l with
  | some (_, _, _, dg) =>
    (digitsA (k1P Z G l (IM.k1Ix l true + 1) 2) l dg, noVals)
  | none => noCell "the digits: no numbers"

def behind (l : Nat) : Cell :=
  match G.built[l]?, testsWhere Z.p.X l 0 with
  | some Xl, some w =>
    if l % 2 == 0 && l != 24 then
      match G.W.G[l / 2]? with
      | some hp => (liftQ (behindG₃ (gTw w) freeG (ProofFile.k8ParW Z G Xl l).nU),
          fun s _ _ => behindV₃ w hp (ProofFile.k8ParW Z G Xl l).nU s)
      | none => noCell "behind the batching: no plan"
    else (liftQ (behindG (gTw w) (ProofFile.k8ParW Z G Xl l).nU),
      fun s _ _ => behindV w (ProofFile.k8ParW Z G Xl l).nU s)
  | _, _ => noCell "behind the batching: no link"

/-- The batching: the member's step and its one Bool out of the link's list of rows (a run of
claims, the run on shapes, its premise as a Bool), along the link's own order. -/
def batch (l : Nat) : Cell :=
  match IM.k9At Z l, testsWhere Z.p.X l 0 with
  | some p, some w =>
    if l == 24 then
      match G.W.H.tl.ix.U.getD 2 none, VerifiableInference.Desc.First.Look.placeAt G.W 24 false with
      | some iU3, some q =>
        (cellG p w.1 (rowsHead G.W iU3 q.lm) (VerifiableInference.Desc.First.orderOf (subAt 24)),
          cellV p (rowsHead G.W iU3 q.lm) (VerifiableInference.Desc.First.orderOf (subAt 24)))
      | _, _ => noCell "the batching at the head: no place"
    else if l % 2 == 0 then
      (cellG p w.1 (rowsLay G.W (l / 2)) (VerifiableInference.Desc.First.orderOf (subAt l)),
        cellV p (rowsLay G.W (l / 2)) (VerifiableInference.Desc.First.orderOf (subAt l)))
    else
      match G.W.A[l / 2]?, VerifiableInference.Desc.First.Look.placeAt G.W l false with
      | some A, some q =>
        (cellG p w.1 (rowsAtt A q.lm) (VerifiableInference.Desc.First.orderOf (subAt l)),
          cellV p (rowsAtt A q.lm) (VerifiableInference.Desc.First.orderOf (subAt l)))
      | _, _ => noCell "the batching: no plan"
  | _, _ => noCell "the batching: no numbers"

def equation : Cell := (oneA, fun s _ _ => oneV s)

def close (l : Nat) : Cell :=
  match (IM.k9At Z l).bind fun p => ProofFile.k10Par Z (ProofFile.k9Stretches Z) p with
  | some Q => (optE (closeGF Q), fun s _ _ => closeInOrdB s)
  | none => noCell "the closing: no numbers"

def shut : Cell := (liftQ shutGS, noVals)

def cleared (l : Nat) : Cell :=
  match Z.p.built.links[l]? with
  | some Y =>
    if l == 24 then (liftQ (clearHeadG (pubOf Y) Z.p.X.layers.wsLay Z.first.lin), noVals)
    else if l % 2 == 1 then
      match Z.p.X.A[Y.g]? with
      | some p => (liftQ (clearAttG (pubOf Y) p.nLin), noVals)
      | none => noCell "cleared: no plan"
    else
      match Z.p.X.G[Y.g]? with
      | some hp => (liftQ (clearLayG (pubOf Y) Z.p.X.layers.wsLay Z.first.lin hp.tl.NM), noVals)
      | none => noCell "cleared: no plan"
  | none => noCell "cleared: no link"

def sendW : Cell :=
  match linMessageW Z.first.lin with
  | some msg => (sendWA (wPar Z msg) (VerifiableInference.Desc.K13.whereOf Z), noVals)
  | none => noCell "W's sending: no message"

def linkRow (l : Nat) : LinkRow Cell where
  laid := laid l
  first := if l == 0 then opening Z G else switch Z G l
  lookCalls := lookCalls Z l
  own := if l % 2 == 0 then k4 G (l / 2) else k5 Z (l / 2)
  reads := reads Z G l
  draw := draw Z G l
  digits := digits Z G l
  lookDigits := lookDigits Z l
  batch := batch Z G l
  behind := behind Z G l
  equation := equation
  close := close Z l
  shut := shut
  cleared := cleared Z l

def headRow : HeadRow Cell where
  laid := laid 24
  reply := (replyA (tailSh G.W.H.tl), fun _ rs _ => replyV G.W.hS.V rs)
  switch := switchHead Z G
  lookCalls := lookCalls Z 24
  own := (liftO (k6GR (P5J.At.X Z).hS), fun s _ _ => k6V (P5J.At.X Z) s)
  reads := readsHead Z G
  draw := draw Z G 24
  digits := digits Z G 24
  lookDigits := lookHead Z
  merge := (liftO (mergeG (K11.parOf Z G)), noVals)
  batch := batch Z G 24
  behind := behind Z G 24
  equation := equation
  close := close Z 24
  shut := shut
  cleared := cleared Z 24

def backRow : BackRow Cell where
  finish := finish Z G
  test := (optE fun y =>
      if testGuardB (H2U.p12OfMade Z.made) y.1 then testA (H2U.p12OfMade Z.made) y else none,
    testV (H2U.p12OfMade Z.made))
  batching := (liftO (battGS (VerifiableInference.Desc.K13.whereOf Z)), noVals)
  sendW := sendW Z
  sealing := (liftQ sealGS, noVals)

/-- **The table of the first chain's 358 members.** -/
def cells : Nat → Cell :=
  table (liftQ .ok, noVals) (linkRow Z G) (headRow Z G) (backRow Z G)

/-- The steps. -/
def g (b : Nat) : StepA := (cells Z G b).1

/-- The tests on values. -/
def vals (b : Nat) : ValsA := (cells Z G b).2

end Tab

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.StepA
#print axioms Johnson.AtFull.Shape.ValsA
#print axioms Johnson.AtFull.Shape.noStep
#print axioms Johnson.AtFull.Shape.noVals
#print axioms Johnson.AtFull.Shape.Cell
#print axioms Johnson.AtFull.Shape.noCell
#print axioms Johnson.AtFull.Shape.Tab.k1P
#print axioms Johnson.AtFull.Shape.Tab.nums
#print axioms Johnson.AtFull.Shape.Tab.laid
#print axioms Johnson.AtFull.Shape.Tab.opening
#print axioms Johnson.AtFull.Shape.Tab.switch
#print axioms Johnson.AtFull.Shape.Tab.switchHead
#print axioms Johnson.AtFull.Shape.Tab.finish
#print axioms Johnson.AtFull.Shape.Tab.siteAt
#print axioms Johnson.AtFull.Shape.Tab.lookCalls
#print axioms Johnson.AtFull.Shape.Tab.lookDigits
#print axioms Johnson.AtFull.Shape.Tab.lookHead
#print axioms Johnson.AtFull.Shape.Tab.k4
#print axioms Johnson.AtFull.Shape.Tab.k5
#print axioms Johnson.AtFull.Shape.Tab.reads
#print axioms Johnson.AtFull.Shape.Tab.readsHead
#print axioms Johnson.AtFull.Shape.Tab.draw
#print axioms Johnson.AtFull.Shape.Tab.digits
#print axioms Johnson.AtFull.Shape.Tab.behind
#print axioms Johnson.AtFull.Shape.Tab.batch
#print axioms Johnson.AtFull.Shape.Tab.equation
#print axioms Johnson.AtFull.Shape.Tab.close
#print axioms Johnson.AtFull.Shape.Tab.shut
#print axioms Johnson.AtFull.Shape.Tab.cleared
#print axioms Johnson.AtFull.Shape.Tab.sendW
#print axioms Johnson.AtFull.Shape.Tab.linkRow
#print axioms Johnson.AtFull.Shape.Tab.headRow
#print axioms Johnson.AtFull.Shape.Tab.backRow
#print axioms Johnson.AtFull.Shape.Tab.cells
#print axioms Johnson.AtFull.Shape.Tab.g
#print axioms Johnson.AtFull.Shape.Tab.vals
