-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TabLetters.lean: WHAT THE TABLE OF THE FIRST CHAIN's 358 MEMBERS (`Tab.cells`,
TableOfSteps.lean) READS OF THE PUBLIC PART Z AND OF THE GROUND G: A RECORD OF 20 LETTERS; THE
TABLE's TEXT ONCE MORE OVER THAT RECORD; THE TIE BETWEEN THE TWO TEXTS; A CONGRUENCE; SIX CONTROLS.
Definitions with code, statements and proofs; general in Z and G; no head; nothing is evaluated.

What it is for. The rule's public premise "the run on shapes returns" speaks of Tab.g Zp Bs.G₀ at
the public part and ground that the makers return. To show it at given public files by Lean's
kernel, the steps must stand at closed terms. With the tie and the congruence it is enough to show,
letter by letter, that the letters at Zp and Bs.G₀ are closed terms: then the table's cells are the
second text's at these.

A SECOND TEXT. `TabL.*` is `Tab.*`'s text, arm for arm, the arms that refuse too, with a field of
the record where the first text has a reader of Z or G. It was made from TableOfSteps.lean's own
lines by a program of counted replacements. Three definitions of the first text are fields here
(k1P, nums, siteAt). Two short texts more: `k2PL`, `switchUL`: IM.k2P's and switchU's with the one
number that they read of Z as a letter. Two more at the layers' own rounds (the kind K4): `k4GL`,
`k4StepL`: k4G's and k4StepW's texts with two things as letters: the Bool of the step's two guards
that read no shape (`k4PubB`), and the hearing on shapes (ownOf); `k4G_eq`, `k4StepW_eq` tie them,
by rfl. AT EIGHT CELLS' TEXTS THE SECOND TEXT PARTS FROM "A FIELD FOR A READER". (1) The three
lookups' cells spend of the site that the first text finds its shape and its first slot alone
(s.shape, s.p.first): the letter look is that pair, and the second text says s.1, s.2;
`lookCalls_letters`, `lookDigits_letters`, `lookHead_letters` hold it, by cases on the search. (2)
ONE READER IS NOT A LETTER: at the attention's own rounds the first text has (K5.parAt Z g a).own,
which is a.own by the library's text (parO: "own := pA.own",
Johnson/Desc/First/Att/K05KeepsSeats.lean:159-161): the second text says a.own, and `k5_letters`
holds by rfl. (3) At the layers' own rounds the first text has k4StepW p; the second has k4StepL
(L.k4pub g) (L.k4own g) p; `k4_letters` holds it, by cases on the plan. (4) At "cleared", at a
layers' link and at the head's, the first text has clearLayG and clearHeadG; the second has
`clearLayGL` and `clearHeadGL` (ClearLight.lean), which are equal to them at all arguments and build
no vector and no array to measure it; no letter is in play; `cleared_letters` holds it, by these two
equations. (5) At the draw and behind the batching the first text matches on the link as built
(G.built[l]?) and reads the smallness test's numbers off it (ProofFile.k8Par; ProofFile.k8ParW); the second
matches on the letter k8 and says p8.toPar and p8.nU; `draw_letters`, `behind_letters` hold it, by
cases on the link (and, behind the batching, on the tests' place). Also: the first text's third
spelling of the reader's structure, P5J.At.X Z, is L.XZ here. THE TWO TEXTS CANNOT DRIFT APART
UNSEEN: `tab_letters` ties them: if either turns, Lean breaks the tie.

Main names.
* `TabLetters`: the plans' half: XZ (Z.p.X), XG (G.W), links (Z.p.built.links), each whole. Where a
  reader takes G or Z whole, what it returns: nums, hpL, k8, k2n, k11; and look: of the site found,
  the shape and the first slot. At K4's cell: k4pub (`k4pubX G.W`: the two guards' Bool at the
  group's plan; true where no plan stands) and k4own (`k4ownX G.W`: the hearing on shapes at that
  plan, a function of the lookup's record's shape and the ledger's). The half that hangs on Z's own
  written fields, as the cells spend it: ft, k1, k1First, lin, k9, close, wP, where13, p12.
  `lettersOf Z G`.
* `TabL.cells L`: the second text. **`tab_letters`**: Tab.cells Z G = TabL.cells (lettersOf Z G);
  beneath it one equation a definition (`opening_letters` … `backRow_letters`): of the 22 with
  tab_letters, 11 by rfl.
* `LettersAlike L L'`: the two records agree wherever a cell reads them: the functions of a link at
  l < 25 alone, hpL and k2n at 0 < l; k4pub and k4own at every group, k4own as an equation of
  functions. **`cells_alike`**: then TabL.cells L n = TabL.cells L' n at every n.
  **`tab_of_alike`**: LettersAlike (lettersOf Z G) L gives Tab.cells Z G n = TabL.cells L n.
* Controls: `close_is_read`, `k2n_is_read`, `hpL_is_read`, `look_is_read`: at every record, two
  turns of it that part in that one letter have cells (12, 353, 339, 3) whose steps part at every
  shape. `k4pub_is_read`, `k4own_is_read`: where k4pub says no, or k4own gives nothing, k4StepL
  refuses at every shape.

Limits. EQUATIONS OF TERMS. Nothing says that a letter is a closed term at any Z and G; nothing on
whether a step returns or a test accepts. What the readers behind nums, hpL, k8, k2n, look and k11
read of Z and G is not said: these letters are what the readers return. Controls at six of the 20
letters alone: at close, k2n, hpL and look each shows a refusal's word against another word or a
return; at k4pub and k4own each shows a refusal of the step's text, not of the cell. NO CONTROL
STANDS at the three other letters that are Options (nums, k8, k9), nor at the eleven that are none:
that the cells read these fourteen is seen in the text, not shown. 77 cells read no letter. THE
TABLE HAS NO END (Table.lean): at every number from 357 on the cell is the seal's, whose step
returns the shape that it is given where it accepts: so a run that overshoots 358 is not caught.
TabL.g and TabL.vals have no caller (LettersRun.lean's shapeL spells the two anew); TabL.k4 repeats
k4Par's text. The ending L has three senses in these files: over letters (TabL, k2PL, switchUL,
k4GL, k4StepL, shapeL), in numerals (numsL, k11L, k2nL, k9L, closeL), light (clearLayGL,
clearHeadGL). noneWaitsSh has two definitions of one text: K4Fit.lean's, in this file's own
namespace, and TailClaims/FreeSlotChain.lean's, in a namespace that this file opens. Whichever Lean
takes at k4StepL: k4StepW_eq holds, by rfl. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TableOfSteps
import Johnson.AtFull.Shape.ClearLight

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

/-- K4's record at a group's plan, as the table's cell lays it. -/
def k4Par (X : Verify.Public) (hp : Layer.HPlan2) (g : Nat) : OnBytes.Desc.First.K4.Par :=
  { name := "", link := 0, piece := 3, before := [], k3Runs := true, P := X.layers, hp := hp
    g := g }

/-- The two guards of K4's step that read no shape: the test on the plan alone, and "the host's
count of the padding keys is the layout's own" (k4Step,
Johnson/Desc/First/K4/Returns/AtStep.lean). -/
def k4PubB (p : OnBytes.Desc.First.K4.Par) : Bool :=
  OnBytes.Desc.First.K4.Rt.k4PlanB p &&
    (VerifiableInference.Desc.First.Look.laidLayers p.P == some p.P.y.fo.pub)

/-- The letter k4pub off the reader's structure: true where no plan stands. -/
def k4pubX (X : Verify.Public) (g : Nat) : Bool := (X.G[g]?).all fun hp => k4PubB (k4Par X hp g)

/-- The letter k4own off the reader's structure: K4's hearing on shapes at the group's plan; nothing
where no plan stands. -/
def k4ownX (X : Verify.Public) (g : Nat) :
    HeardAll → LedSh → Option (OwnSh × List FunSh × LedSh) :=
  match X.G[g]? with
  | some hp => OnBytes.Desc.First.K4.Rt.ownOf (k4Par X hp g)
  | none => fun _ _ => none

/-- k4G's text (Johnson/Desc/First/K4/Returns/AtShape.lean) with the hearing on shapes as a
letter. -/
def k4GL (own : HeardAll → LedSh → Option (OwnSh × List FunSh × LedSh)) (a : ChainSh) :
    Option ChainSh :=
  if a.here != 1 then none else
  match a.look, a.led with
  | some h, some L =>
    (own h L).map fun z =>
      (((a.setLed z.2.2).layOwn (some z.1)).layTables (some z.2.1)).setRowsOwed none
  | _, _ => none

theorem k4G_eq (p : OnBytes.Desc.First.K4.Par) :
    OnBytes.Desc.First.K4.Rt.k4G p = k4GL (OnBytes.Desc.First.K4.Rt.ownOf p) := rfl

/-- k4StepW's text (K4Fit.lean, through k4StepS and k4Step) with the two guards that read no shape
and the hearing on shapes as letters. -/
def k4StepL (ok : Bool) (own : HeardAll → LedSh → Option (OwnSh × List FunSh × LedSh))
    (p : OnBytes.Desc.First.K4.Par) (a : ChainSh) : Option ChainSh :=
  if noneWaitsSh a then
    if a.marked then none
    else if (ok && OnBytes.Desc.First.K4.Rt.k4FrontB p 0 a) = true then k4GL own a
    else none
  else none

theorem k4StepW_eq (p : OnBytes.Desc.First.K4.Par) :
    k4StepW p = k4StepL (k4PubB p) (OnBytes.Desc.First.K4.Rt.ownOf p) p := rfl

/-- **What the table's 358 cells read of the public part Z and of the ground G.** The plans' half:
the reader's structure whole, at its two spellings, and the built links. "As spent": where a reader
takes G or Z whole, what it returns. The written half: as the cells spend it. -/
structure TabLetters where
  /-- Z.p.X -/
  XZ : Verify.Public
  /-- G.W -/
  XG : Verify.Public
  /-- Z.p.built.links -/
  links : Array Stages.LinkH
  /-- (G.built[l]?).bind (K1.linkNumbers G) -/
  nums : Nat → Option (Nat × Nat × Option (List Nat) × Option (List Nat))
  /-- P1K2.pureLetters G l -/
  hpL : Nat → Option VerifiableInference.Desc.First.K2.HeadPar
  /-- (G.built[l]?).map fun Xl => ProofFile.k8ParW Z G Xl l -/
  k8 : Nat → Option VerifiableInference.Desc.First.K8.ParW
  /-- (P1K2.prepOf Z G).bind fun P => P1K2.numsAt P a -/
  k2n : Option Nat → Option P1K2.Nums
  /-- of the site s that (lookSites Z).find? fun s => s.link == l && s.digits == d finds:
  (s.shape, s.p.first) -/
  look : Nat → Bool → Option (Forest.Shape × Nat)
  /-- k4pubX G.W g -/
  k4pub : Nat → Bool
  /-- k4ownX G.W g -/
  k4own : Nat → HeardAll → LedSh → Option (OwnSh × List FunSh × LedSh)
  /-- K11.parOf Z G -/
  k11 : Johnson.Desc.First.ForkMerge.HeadMergeP
  /-- Z.P.firstTree -/
  ft : Nat
  /-- K1.parLater G.first (K1.gpOf Z) l pc m -/
  k1 : Nat → Nat → Nat → VerifiableInference.Desc.K1.Par
  /-- K1.firstPar G.first (K1.gpOf Z) -/
  k1First : VerifiableInference.Desc.K1.Par
  /-- Z.first.lin -/
  lin : OnBytes.Params.LinShape
  /-- IM.k9At Z l -/
  k9 : Nat → Option VerifiableInference.Desc.K9.Where
  /-- (IM.k9At Z l).bind fun p => ProofFile.k10Par Z (ProofFile.k9Stretches Z) p -/
  close : Nat → Option VerifiableInference.Desc.First.Close.Par
  /-- wPar Z msg -/
  wP : Array OracleNotice → VerifiableInference.Desc.K1.Par
  /-- K13.whereOf Z -/
  where13 : VerifiableInference.Desc.K13.Where
  /-- H2U.p12OfMade Z.made -/
  p12 : VerifiableInference.Desc.K12.P12

/-- The letters at a public part and a ground. -/
def lettersOf (Z : ProofFile.Pub) (G : ProofFile.Ground) : TabLetters where
  XZ := Z.p.X
  XG := G.W
  links := Z.p.built.links
  nums := fun l => (G.built[l]?).bind (VerifiableInference.Desc.K1.linkNumbers G)
  hpL := P1K2.pureLetters G
  k8 := fun l => (G.built[l]?).map fun Xl => ProofFile.k8ParW Z G Xl l
  k2n := fun a => (P1K2.prepOf Z G).bind fun P => P1K2.numsAt P a
  look := fun l d =>
    ((lookSites Z).find? fun s => s.link == l && s.digits == d).map fun s => (s.shape, s.p.first)
  k4pub := k4pubX G.W
  k4own := k4ownX G.W
  k11 := K11.parOf Z G
  ft := Z.P.firstTree
  k1 := fun l pc m =>
    VerifiableInference.Desc.K1.parLater G.first (VerifiableInference.Desc.K1.gpOf Z) l pc m
  k1First := VerifiableInference.Desc.K1.firstPar G.first (VerifiableInference.Desc.K1.gpOf Z)
  lin := Z.first.lin
  k9 := IM.k9At Z
  close := fun l => (IM.k9At Z l).bind fun p => ProofFile.k10Par Z (ProofFile.k9Stretches Z) p
  wP := wPar Z
  where13 := VerifiableInference.Desc.K13.whereOf Z
  p12 := H2U.p12OfMade Z.made

/-- IM.k2P's text (Johnson/IMR/K2Seat.lean) with the one number that it reads of Z as a letter. -/
def k2PL (ft : Nat) (a : Place) (nm : String) (st : VerifiableInference.Desc.First.K2.At)
    (n : P1K2.Nums) : VerifiableInference.Desc.First.K2.P2 :=
  { name := nm, place := a, stands := st, grp := n.grp, firstTree := ft, samples := n.samples,
    work₁ := n.work₁, roots := n.roots, seeds := n.seeds, nonZero := n.nonZero,
    work₂ := n.work₂, answers := n.answers, positions := n.positions, logN := n.logN,
    sent := P1K2.oraclesAt n.grp n.codes n.sent, read := n.read }

theorem k2PL_eq (Z : ProofFile.Pub) : k2P Z = k2PL Z.P.firstTree := rfl

/-- switchU's text (SwitchAtHead.lean) over k2PL. -/
def switchUL (ft : Nat) (a : Place) (n : P1K2.Nums)
    (HP : VerifiableInference.Desc.First.K2.HeadPar) (x : ChainF) : Option ChainF :=
  match x.1.here with
  | 0 => linkU (k2PL ft a "" .link n) x
  | 4 => (headU (k2PL ft a "" .head n) x).bind (headOpenU HP)
  | _ => none

theorem switchUL_eq (Z : ProofFile.Pub) : switchU Z = switchUL Z.P.firstTree := rfl

/-! ## The table's text once more, a field for each reader -/

namespace TabL
variable (L : TabLetters)

def laid (l : Nat) : Cell := (liftQ (laidGS l), noVals)

def opening : Cell :=
  match L.links[0]? with
  | some X =>
    match L.XZ.G[X.g]? with
    | some hp =>
      (openingA L.k1First
          (openZeroG ⟨pubOf X, 0, L.XZ.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩
            (fvsOf L.links) L.lin.kCol), noVals)
    | none => noCell "the opening: no plan"
  | none => noCell "the opening: no link"

/-- The code switch at a link's first place, with the frame's "opened" behind it (l from 1 to 23):
the guard linkGd in front of the step; the test on values is switchW. -/
def switch (l : Nat) : Cell :=
  match L.k2n (some l), L.hpL l, L.links[l]? with
  | some n, some HP, some Y =>
    if l % 2 == 1 then
      match L.XZ.A[Y.g]? with
      | some p => (optE fun y =>
          if linkGd (k2PL L.ft { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n) y
          then (switchUL L.ft { chain := 1, link := some l, piece := 1, kind := .K2 } n HP y).bind
              (quietE (openAttG (attPar Y p l)))
          else none,
        fun s _ _ => switchW s)
      | none => noCell "the switch: no plan"
    else
      match L.XZ.G[Y.g]? with
      | some hp => (optE fun y =>
          if linkGd (k2PL L.ft { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n) y
          then (switchUL L.ft { chain := 1, link := some l, piece := 1, kind := .K2 } n HP y).bind
              (quietE (openLayG (layPar L.XZ Y hp l)))
          else none,
        fun s _ _ => switchW s)
      | none => noCell "the switch: no plan"
  | _, _, _ => noCell "the switch: no numbers"

def switchHead : Cell :=
  match L.k2n (some 24), L.hpL 24 with
  | some n, some HP =>
    (optE fun y =>
        if headGd (k2PL L.ft { chain := 1, link := some 24, piece := 2, kind := .K2 } "" .head n)
            HP y
        then switchUL L.ft { chain := 1, link := some 24, piece := 2, kind := .K2 } n HP y
        else none,
      fun s _ _ => headW HP s)
  | _, _ => noCell "the switch at the head: no numbers"

def finish : Cell :=
  match L.k2n none with
  | some n => (optE fun y =>
      if finGd (k2PL L.ft k2PlaceF "" .finish n) y
      then ((finFrontU y).bind (finU (k2PL L.ft k2PlaceF "" .finish n))).bind finBehindU
      else none,
    fun s _ _ => switchW s)
  | none => noCell "the finish: no numbers"

def lookCalls (l : Nat) : Cell :=
  match L.look l false with
  | some s => (liftQ (callsG s.1 s.2), noVals)
  | none => noCell "the lookup: no site"

def lookDigits (l : Nat) : Cell :=
  match L.look l true, lookUC L.XZ l with
  | some s, some (u, c) => (liftQ (digitsG s.1 s.2 u c), noVals)
  | _, _ => noCell "the lookup on the digits: no site"

/-- The lookup on the head's own digits. -/
def lookHead : Cell :=
  match L.look 24 true with
  | some s => (liftQ (headDigitsG s.1 s.2 L.XZ), fun st _ _ => headVals L.XZ st)
  | none => noCell "the lookup on the head's own digits: no site"

def k4 (g : Nat) : Cell :=
  match L.XG.G[g]? with
  | some hp =>
    let p : OnBytes.Desc.First.K4.Par :=
      { name := "", link := 0, piece := 3, before := [], k3Runs := true, P := L.XG.layers, hp := hp
        g := g }
    (liftO (k4StepL (L.k4pub g) (L.k4own g) p), fun s rs _ => k4ValsV p s rs)
  | none => noCell "K4: no plan"

/-- The attention's own rounds, by group (another house's step; its test on values, k5V, is true at
every state: no test). -/
def k5 (g : Nat) : Cell :=
  match L.XZ.A[g]? with
  | some a => (liftQ (ProofFile.Honest.K5.k5Q a.own), ProofFile.Honest.K5.k5V)
  | none => noCell "K5: no plan"

def reads (l : Nat) : Cell :=
  match L.nums l with
  | some (_, _, rd, _) =>
    if l % 2 == 0 then
      match L.XG.G[l / 2]? with
      | some hp => (readsA (readsGS (L.k1 l 4 1) l rd (tailSh hp.tl)) (L.k1 l 4 1), noVals)
      | none => noCell "the reads: no plan"
    else
      match L.XG.A[l / 2]? with
      | some A => (readsA (readsAttGS (L.k1 l 4 1) l rd A) (L.k1 l 4 1),
          fun s rs gs => midV (L.k1 l 4 1) l rd (valsTS A) s rs gs)
      | none => noCell "the reads: no plan"
  | none => noCell "the reads: no numbers"

def readsHead : Cell :=
  match L.nums 24 with
  | some (_, _, rd, _) =>
    (readsA (readsHeadGS (L.k1 24 5 1) rd ⟨⟨1, some 24, 5, .K1⟩, L.XG.hS, L.XG.HLy, L.XG.H⟩)
        (L.k1 24 5 1),
      fun s rs gs => midV (L.k1 24 5 1) 24 rd
        (fun m => (m.covered L.XG.hS.T L.XG.hS.V).toOption.isSome) s rs gs)
  | none => noCell "the head's reads: no numbers"

def draw (l : Nat) : Cell :=
  match L.k8 l with
  | some p8 => (liftQ (drawStep p8.toPar), noVals)
  | none => noCell "the draw: no link"

def digits (l : Nat) : Cell :=
  match L.nums l with
  | some (_, _, _, dg) =>
    (digitsA (L.k1 l (IM.k1Ix l true + 1) 2) l dg, noVals)
  | none => noCell "the digits: no numbers"

def behind (l : Nat) : Cell :=
  match L.k8 l, testsWhere L.XZ l 0 with
  | some p8, some w =>
    if l % 2 == 0 && l != 24 then
      match L.XG.G[l / 2]? with
      | some hp => (liftQ (behindG₃ (gTw w) freeG p8.nU),
          fun s _ _ => behindV₃ w hp p8.nU s)
      | none => noCell "behind the batching: no plan"
    else (liftQ (behindG (gTw w) p8.nU),
      fun s _ _ => behindV w p8.nU s)
  | _, _ => noCell "behind the batching: no link"

/-- The batching: the member's step and its one Bool out of the link's list of rows (a run of
claims, the run on shapes, its premise as a Bool), along the link's own order. -/
def batch (l : Nat) : Cell :=
  match L.k9 l, testsWhere L.XZ l 0 with
  | some p, some w =>
    if l == 24 then
      match L.XG.H.tl.ix.U.getD 2 none,
          VerifiableInference.Desc.First.Look.placeAt L.XG 24 false with
      | some iU3, some q =>
        (cellG p w.1 (rowsHead L.XG iU3 q.lm) (VerifiableInference.Desc.First.orderOf (subAt 24)),
          cellV p (rowsHead L.XG iU3 q.lm) (VerifiableInference.Desc.First.orderOf (subAt 24)))
      | _, _ => noCell "the batching at the head: no place"
    else if l % 2 == 0 then
      (cellG p w.1 (rowsLay L.XG (l / 2)) (VerifiableInference.Desc.First.orderOf (subAt l)),
        cellV p (rowsLay L.XG (l / 2)) (VerifiableInference.Desc.First.orderOf (subAt l)))
    else
      match L.XG.A[l / 2]?, VerifiableInference.Desc.First.Look.placeAt L.XG l false with
      | some A, some q =>
        (cellG p w.1 (rowsAtt A q.lm) (VerifiableInference.Desc.First.orderOf (subAt l)),
          cellV p (rowsAtt A q.lm) (VerifiableInference.Desc.First.orderOf (subAt l)))
      | _, _ => noCell "the batching: no plan"
  | _, _ => noCell "the batching: no numbers"

def equation : Cell := (oneA, fun s _ _ => oneV s)

def close (l : Nat) : Cell :=
  match L.close l with
  | some Q => (optE (closeGF Q), fun s _ _ => closeInOrdB s)
  | none => noCell "the closing: no numbers"

def shut : Cell := (liftQ shutGS, noVals)

def cleared (l : Nat) : Cell :=
  match L.links[l]? with
  | some Y =>
    if l == 24 then (liftQ (clearHeadGL (pubOf Y) L.XZ.layers.wsLay L.lin), noVals)
    else if l % 2 == 1 then
      match L.XZ.A[Y.g]? with
      | some p => (liftQ (clearAttG (pubOf Y) p.nLin), noVals)
      | none => noCell "cleared: no plan"
    else
      match L.XZ.G[Y.g]? with
      | some hp => (liftQ (clearLayGL (pubOf Y) L.XZ.layers.wsLay L.lin hp.tl.NM), noVals)
      | none => noCell "cleared: no plan"
  | none => noCell "cleared: no link"

def sendW : Cell :=
  match linMessageW L.lin with
  | some msg => (sendWA (L.wP msg) L.where13, noVals)
  | none => noCell "W's sending: no message"

def linkRow (l : Nat) : LinkRow Cell where
  laid := laid l
  first := if l == 0 then opening L else switch L l
  lookCalls := lookCalls L l
  own := if l % 2 == 0 then k4 L (l / 2) else k5 L (l / 2)
  reads := reads L l
  draw := draw L l
  digits := digits L l
  lookDigits := lookDigits L l
  batch := batch L l
  behind := behind L l
  equation := equation
  close := close L l
  shut := shut
  cleared := cleared L l

def headRow : HeadRow Cell where
  laid := laid 24
  reply := (replyA (tailSh L.XG.H.tl), fun _ rs _ => replyV L.XG.hS.V rs)
  switch := switchHead L
  lookCalls := lookCalls L 24
  own := (liftO (k6GR L.XZ.hS), fun s _ _ => k6V L.XZ s)
  reads := readsHead L
  draw := draw L 24
  digits := digits L 24
  lookDigits := lookHead L
  merge := (liftO (mergeG L.k11), noVals)
  batch := batch L 24
  behind := behind L 24
  equation := equation
  close := close L 24
  shut := shut
  cleared := cleared L 24

def backRow : BackRow Cell where
  finish := finish L
  test := (optE fun y =>
      if testGuardB L.p12 y.1 then testA L.p12 y else none,
    testV L.p12)
  batching := (liftO (battGS L.where13), noVals)
  sendW := sendW L
  sealing := (liftQ sealGS, noVals)

/-- **The table of the first chain's 358 members.** -/
def cells : Nat → Cell :=
  table (liftQ .ok, noVals) (linkRow L) (headRow L) (backRow L)

/-- The steps. -/
def g (b : Nat) : StepA := (cells L b).1

/-- The tests on values. -/
def vals (b : Nat) : ValsA := (cells L b).2

end TabL

/-! ## The tie, a class at a time -/

theorem opening_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    Tab.opening Z G = TabL.opening (lettersOf Z G) := rfl

theorem switch_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    Tab.switch Z G l = TabL.switch (lettersOf Z G) l := rfl

theorem switchHead_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    Tab.switchHead Z G = TabL.switchHead (lettersOf Z G) := rfl

theorem finish_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    Tab.finish Z G = TabL.finish (lettersOf Z G) := rfl

theorem lookCalls_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    Tab.lookCalls Z l = TabL.lookCalls (lettersOf Z G) l := by
  unfold Tab.lookCalls Tab.siteAt TabL.lookCalls lettersOf
  dsimp only
  cases (lookSites Z).find? fun s => s.link == l && s.digits == false <;> rfl

theorem lookDigits_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    Tab.lookDigits Z l = TabL.lookDigits (lettersOf Z G) l := by
  unfold Tab.lookDigits Tab.siteAt TabL.lookDigits lettersOf
  dsimp only
  cases (lookSites Z).find? fun s => s.link == l && s.digits == true <;>
    cases lookUC Z.p.X l <;> rfl

theorem lookHead_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    Tab.lookHead Z = TabL.lookHead (lettersOf Z G) := by
  unfold Tab.lookHead Tab.siteAt TabL.lookHead lettersOf
  dsimp only
  cases (lookSites Z).find? fun s => s.link == 24 && s.digits == true <;> rfl

theorem k4_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (g : Nat) :
    Tab.k4 G g = TabL.k4 (lettersOf Z G) g := by
  unfold Tab.k4 TabL.k4 lettersOf k4pubX k4ownX
  dsimp only
  cases G.W.G[g]? with
  | none => rfl
  | some hp =>
    dsimp only
    rw [k4StepW_eq]
    rfl

theorem k5_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (g : Nat) :
    Tab.k5 Z g = TabL.k5 (lettersOf Z G) g := rfl

theorem reads_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    Tab.reads Z G l = TabL.reads (lettersOf Z G) l := rfl

theorem readsHead_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    Tab.readsHead Z G = TabL.readsHead (lettersOf Z G) := rfl

theorem draw_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    Tab.draw Z G l = TabL.draw (lettersOf Z G) l := by
  unfold Tab.draw TabL.draw lettersOf
  dsimp only
  cases G.built[l]? <;> rfl

theorem digits_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    Tab.digits Z G l = TabL.digits (lettersOf Z G) l := rfl

theorem behind_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    Tab.behind Z G l = TabL.behind (lettersOf Z G) l := by
  unfold Tab.behind TabL.behind lettersOf
  dsimp only
  cases G.built[l]? <;> cases testsWhere Z.p.X l 0 <;> rfl

theorem batch_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    Tab.batch Z G l = TabL.batch (lettersOf Z G) l := rfl

theorem close_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    Tab.close Z l = TabL.close (lettersOf Z G) l := rfl

theorem cleared_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    Tab.cleared Z l = TabL.cleared (lettersOf Z G) l := by
  unfold Tab.cleared TabL.cleared
  simp only [clearHeadG_eq, clearLayG_eq]
  rfl

theorem sendW_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    Tab.sendW Z = TabL.sendW (lettersOf Z G) := rfl

theorem linkRow_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) :
    Tab.linkRow Z G l = TabL.linkRow (lettersOf Z G) l := by
  unfold Tab.linkRow TabL.linkRow
  rw [opening_letters Z G, switch_letters Z G, lookCalls_letters Z G, k4_letters Z G,
    k5_letters Z G, reads_letters Z G, draw_letters Z G, digits_letters Z G,
    lookDigits_letters Z G, batch_letters Z G, behind_letters Z G, close_letters Z G,
    cleared_letters Z G]
  rfl

theorem headRow_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    Tab.headRow Z G = TabL.headRow (lettersOf Z G) := by
  unfold Tab.headRow TabL.headRow
  rw [switchHead_letters Z G, lookCalls_letters Z G, readsHead_letters Z G, draw_letters Z G,
    digits_letters Z G, lookHead_letters Z G, batch_letters Z G, behind_letters Z G,
    close_letters Z G, cleared_letters Z G]
  rfl

theorem backRow_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    Tab.backRow Z G = TabL.backRow (lettersOf Z G) := by
  unfold Tab.backRow TabL.backRow
  rw [finish_letters Z G, sendW_letters Z G]
  rfl

/-- **THE TABLE READS OF Z AND G THESE LETTERS ALONE.** -/
theorem tab_letters (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    Tab.cells Z G = TabL.cells (lettersOf Z G) := by
  unfold Tab.cells TabL.cells
  rw [headRow_letters, backRow_letters, funext (linkRow_letters Z G)]

/-! ## The congruence -/

/-- Two records of letters that are alike wherever a cell reads them: the functions of a link at
l < 25 alone; hpL and k2n at 0 < l, since link 0 has the opening in the switch's place. (k1 is asked
at every piece and moment: more than the cells read; so are nums, as a whole tuple, of which the
cells read the third and fourth parts; k4pub and k4own at every group, of which twelve are read; wP
at every message, of which one is read; hpL's value at the links 1 to 23, where switchUL's text
reads it in the arm "4" alone (at 24 the guard and the test on values read it too).) -/
structure LettersAlike (L L' : TabLetters) : Prop where
  XZ : L.XZ = L'.XZ
  XG : L.XG = L'.XG
  links : L.links = L'.links
  nums : ∀ l, l < 25 → L.nums l = L'.nums l
  hpL : ∀ l, 0 < l → l < 25 → L.hpL l = L'.hpL l
  k8 : ∀ l, l < 25 → L.k8 l = L'.k8 l
  k2nL : ∀ l, 0 < l → l < 25 → L.k2n (some l) = L'.k2n (some l)
  k2nF : L.k2n none = L'.k2n none
  look : ∀ l, l < 25 → ∀ d, L.look l d = L'.look l d
  k4pub : ∀ g, L.k4pub g = L'.k4pub g
  k4own : ∀ g, L.k4own g = L'.k4own g
  k11 : L.k11 = L'.k11
  ft : L.ft = L'.ft
  k1 : ∀ l, l < 25 → ∀ pc m, L.k1 l pc m = L'.k1 l pc m
  k1First : L.k1First = L'.k1First
  lin : L.lin = L'.lin
  k9 : ∀ l, l < 25 → L.k9 l = L'.k9 l
  close : ∀ l, l < 25 → L.close l = L'.close l
  wP : ∀ msg, L.wP msg = L'.wP msg
  where13 : L.where13 = L'.where13
  p12 : L.p12 = L'.p12

section
variable {L L' : TabLetters} (h : LettersAlike L L')
include h

theorem opening_alike : TabL.opening L = TabL.opening L' := by
  unfold TabL.opening
  rw [h.links, h.XZ, h.k1First, h.lin]

theorem switch_alike (l : Nat) (h0 : 0 < l) (hl : l < 25) :
    TabL.switch L l = TabL.switch L' l := by
  unfold TabL.switch
  rw [h.k2nL l h0 hl, h.hpL l h0 hl, h.links, h.XZ, h.ft]

theorem switchHead_alike : TabL.switchHead L = TabL.switchHead L' := by
  unfold TabL.switchHead
  rw [h.k2nL 24 (by omega) (by omega), h.hpL 24 (by omega) (by omega), h.ft]

theorem finish_alike : TabL.finish L = TabL.finish L' := by
  unfold TabL.finish
  rw [h.k2nF, h.ft]

theorem lookCalls_alike (l : Nat) (hl : l < 25) : TabL.lookCalls L l = TabL.lookCalls L' l := by
  unfold TabL.lookCalls
  rw [h.look l hl false]

theorem lookDigits_alike (l : Nat) (hl : l < 25) :
    TabL.lookDigits L l = TabL.lookDigits L' l := by
  unfold TabL.lookDigits
  rw [h.look l hl true, h.XZ]

theorem lookHead_alike : TabL.lookHead L = TabL.lookHead L' := by
  unfold TabL.lookHead
  rw [h.look 24 (by omega) true, h.XZ]

theorem k4_alike (g : Nat) : TabL.k4 L g = TabL.k4 L' g := by
  unfold TabL.k4
  rw [h.XG, h.k4pub g, h.k4own g]

theorem k5_alike (g : Nat) : TabL.k5 L g = TabL.k5 L' g := by
  unfold TabL.k5
  rw [h.XZ]

theorem reads_alike (l : Nat) (hl : l < 25) : TabL.reads L l = TabL.reads L' l := by
  unfold TabL.reads
  rw [h.nums l hl, h.XG, h.k1 l hl 4 1]

theorem readsHead_alike : TabL.readsHead L = TabL.readsHead L' := by
  unfold TabL.readsHead
  rw [h.nums 24 (by omega), h.XG, h.k1 24 (by omega) 5 1]

theorem draw_alike (l : Nat) (hl : l < 25) : TabL.draw L l = TabL.draw L' l := by
  unfold TabL.draw
  rw [h.k8 l hl]

theorem digits_alike (l : Nat) (hl : l < 25) : TabL.digits L l = TabL.digits L' l := by
  unfold TabL.digits
  rw [h.nums l hl, h.k1 l hl (IM.k1Ix l true + 1) 2]

theorem behind_alike (l : Nat) (hl : l < 25) : TabL.behind L l = TabL.behind L' l := by
  unfold TabL.behind
  rw [h.k8 l hl, h.XZ, h.XG]

theorem batch_alike (l : Nat) (hl : l < 25) : TabL.batch L l = TabL.batch L' l := by
  unfold TabL.batch
  rw [h.k9 l hl, h.XZ, h.XG]

theorem close_alike (l : Nat) (hl : l < 25) : TabL.close L l = TabL.close L' l := by
  unfold TabL.close
  rw [h.close l hl]

theorem cleared_alike (l : Nat) : TabL.cleared L l = TabL.cleared L' l := by
  unfold TabL.cleared
  rw [h.links, h.XZ, h.lin]

theorem sendW_alike : TabL.sendW L = TabL.sendW L' := by
  have e : L.wP = L'.wP := funext h.wP
  unfold TabL.sendW
  rw [h.lin, h.where13, e]

theorem linkRow_alike (l : Nat) (hl : l < 25) : TabL.linkRow L l = TabL.linkRow L' l := by
  have e : (if l == 0 then TabL.opening L else TabL.switch L l) =
      if l == 0 then TabL.opening L' else TabL.switch L' l := by
    by_cases h0 : l = 0
    · subst h0
      exact opening_alike h
    · rw [if_neg (by simpa using h0), if_neg (by simpa using h0)]
      exact switch_alike h l (by omega) hl
  unfold TabL.linkRow
  rw [e, lookCalls_alike h l hl, k4_alike h, k5_alike h,
    reads_alike h l hl, draw_alike h l hl, digits_alike h l hl, lookDigits_alike h l hl,
    batch_alike h l hl, behind_alike h l hl, close_alike h l hl, cleared_alike h]

theorem headRow_alike : TabL.headRow L = TabL.headRow L' := by
  unfold TabL.headRow
  rw [switchHead_alike h, lookCalls_alike h 24 (by omega), readsHead_alike h,
    draw_alike h 24 (by omega), digits_alike h 24 (by omega), lookHead_alike h,
    batch_alike h 24 (by omega), behind_alike h 24 (by omega), close_alike h 24 (by omega),
    cleared_alike h, h.XG, h.XZ, h.k11]

theorem backRow_alike : TabL.backRow L = TabL.backRow L' := by
  unfold TabL.backRow
  rw [finish_alike h, sendW_alike h, h.p12, h.where13]

/-- **LETTERS ALIKE, CELLS ALIKE**: at every number. -/
theorem cells_alike (n : Nat) : TabL.cells L n = TabL.cells L' n := by
  unfold TabL.cells table
  rw [headRow_alike h, backRow_alike h]
  by_cases h0 : n = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : n < 337
    · rw [if_pos h1, if_pos h1, linkRow_alike h _ (by omega)]
    · rw [if_neg h1, if_neg h1]

end

/-- **WHERE THE LETTERS AT Z AND G ARE ALIKE TO L, THE TABLE's CELLS ARE THE SECOND TEXT's
(TabL.cells) AT L.** -/
theorem tab_of_alike {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : TabLetters}
    (h : LettersAlike (lettersOf Z G) L) (n : Nat) : Tab.cells Z G n = TabL.cells L n := by
  rw [tab_letters]
  exact cells_alike h n

/-! ## Controls: the twin table reads its letters -/

/-- Two records that part in the letter close alone: the cell at 12 parts, at every shape. -/
theorem close_is_read (L : TabLetters) (Q : VerifiableInference.Desc.First.Close.Par) (a : ShA) :
    (TabL.cells { L with close := fun _ => none } 12).1 a ≠
      (TabL.cells { L with close := fun _ => some Q } 12).1 a := by
  show noStep "the closing: no numbers" a ≠ optE (closeGF Q) a
  unfold noStep optE
  cases closeGF Q a <;> simp

/-- The like at the letter k2n and the cell at 353. -/
theorem k2n_is_read (L : TabLetters) (n : P1K2.Nums) (a : ShA) :
    (TabL.cells { L with k2n := fun _ => none } 353).1 a ≠
      (TabL.cells { L with k2n := fun _ => some n } 353).1 a := by
  show noStep "the finish: no numbers" a ≠ optE (fun y =>
      if finGd (k2PL L.ft k2PlaceF "" .finish n) y
      then ((finFrontU y).bind (finU (k2PL L.ft k2PlaceF "" .finish n))).bind finBehindU
      else none) a
  unfold noStep optE
  split <;> simp

/-- The like at the letter hpL and the cell at 339. -/
theorem hpL_is_read (L : TabLetters) (n : P1K2.Nums)
    (HP : VerifiableInference.Desc.First.K2.HeadPar) (a : ShA) :
    (TabL.cells { L with k2n := fun _ => some n, hpL := fun _ => none } 339).1 a ≠
      (TabL.cells { L with k2n := fun _ => some n, hpL := fun _ => some HP } 339).1 a := by
  show noStep "the switch at the head: no numbers" a ≠ optE (fun y =>
      if headGd (k2PL L.ft { chain := 1, link := some 24, piece := 2, kind := .K2 } "" .head n) HP y
      then switchUL L.ft { chain := 1, link := some 24, piece := 2, kind := .K2 } n HP y
      else none) a
  unfold noStep optE
  split <;> simp

/-- The like at the letter look and the cell at 3. -/
theorem look_is_read (L : TabLetters) (hf : Forest.Shape × Nat) (a : ShA) :
    (TabL.cells { L with look := fun _ _ => none } 3).1 a ≠
      (TabL.cells { L with look := fun _ _ => some hf } 3).1 a := by
  show noStep "the lookup: no site" a ≠ liftQ (callsG hf.1 hf.2) a
  unfold noStep liftQ callsG
  split <;> simp [Except.map]

/-- At the letter k4pub: where it says no, K4's step refuses at every shape. -/
theorem k4pub_is_read (own : HeardAll → LedSh → Option (OwnSh × List FunSh × LedSh))
    (p : OnBytes.Desc.First.K4.Par) (a : ChainSh) : k4StepL false own p a = none := by
  unfold k4StepL
  split
  · split <;> rfl
  · rfl

/-- At the letter k4own: where it gives nothing, K4's step refuses at every shape. -/
theorem k4own_is_read (ok : Bool) (p : OnBytes.Desc.First.K4.Par) (a : ChainSh) :
    k4StepL ok (fun _ _ => none) p a = none := by
  have e : k4GL (fun _ _ => none) a = none := by
    unfold k4GL
    split
    · rfl
    · split <;> rfl
  unfold k4StepL
  rw [e]
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.k4G_eq
#print axioms Johnson.AtFull.Shape.k4StepW_eq
#print axioms Johnson.AtFull.Shape.k2PL_eq
#print axioms Johnson.AtFull.Shape.switchUL_eq
#print axioms Johnson.AtFull.Shape.opening_letters
#print axioms Johnson.AtFull.Shape.switch_letters
#print axioms Johnson.AtFull.Shape.switchHead_letters
#print axioms Johnson.AtFull.Shape.finish_letters
#print axioms Johnson.AtFull.Shape.lookCalls_letters
#print axioms Johnson.AtFull.Shape.lookDigits_letters
#print axioms Johnson.AtFull.Shape.lookHead_letters
#print axioms Johnson.AtFull.Shape.k4_letters
#print axioms Johnson.AtFull.Shape.k5_letters
#print axioms Johnson.AtFull.Shape.reads_letters
#print axioms Johnson.AtFull.Shape.readsHead_letters
#print axioms Johnson.AtFull.Shape.draw_letters
#print axioms Johnson.AtFull.Shape.digits_letters
#print axioms Johnson.AtFull.Shape.behind_letters
#print axioms Johnson.AtFull.Shape.batch_letters
#print axioms Johnson.AtFull.Shape.close_letters
#print axioms Johnson.AtFull.Shape.cleared_letters
#print axioms Johnson.AtFull.Shape.sendW_letters
#print axioms Johnson.AtFull.Shape.linkRow_letters
#print axioms Johnson.AtFull.Shape.headRow_letters
#print axioms Johnson.AtFull.Shape.backRow_letters
#print axioms Johnson.AtFull.Shape.tab_letters
#print axioms Johnson.AtFull.Shape.opening_alike
#print axioms Johnson.AtFull.Shape.switch_alike
#print axioms Johnson.AtFull.Shape.switchHead_alike
#print axioms Johnson.AtFull.Shape.finish_alike
#print axioms Johnson.AtFull.Shape.lookCalls_alike
#print axioms Johnson.AtFull.Shape.lookDigits_alike
#print axioms Johnson.AtFull.Shape.lookHead_alike
#print axioms Johnson.AtFull.Shape.k4_alike
#print axioms Johnson.AtFull.Shape.k5_alike
#print axioms Johnson.AtFull.Shape.reads_alike
#print axioms Johnson.AtFull.Shape.readsHead_alike
#print axioms Johnson.AtFull.Shape.draw_alike
#print axioms Johnson.AtFull.Shape.digits_alike
#print axioms Johnson.AtFull.Shape.behind_alike
#print axioms Johnson.AtFull.Shape.batch_alike
#print axioms Johnson.AtFull.Shape.close_alike
#print axioms Johnson.AtFull.Shape.cleared_alike
#print axioms Johnson.AtFull.Shape.sendW_alike
#print axioms Johnson.AtFull.Shape.linkRow_alike
#print axioms Johnson.AtFull.Shape.headRow_alike
#print axioms Johnson.AtFull.Shape.backRow_alike
#print axioms Johnson.AtFull.Shape.cells_alike
#print axioms Johnson.AtFull.Shape.tab_of_alike
#print axioms Johnson.AtFull.Shape.close_is_read
#print axioms Johnson.AtFull.Shape.k2n_is_read
#print axioms Johnson.AtFull.Shape.hpL_is_read
#print axioms Johnson.AtFull.Shape.look_is_read
#print axioms Johnson.AtFull.Shape.k4pub_is_read
#print axioms Johnson.AtFull.Shape.k4own_is_read
#print axioms Johnson.AtFull.Shape.k4Par
#print axioms Johnson.AtFull.Shape.k4PubB
#print axioms Johnson.AtFull.Shape.k4pubX
#print axioms Johnson.AtFull.Shape.k4ownX
#print axioms Johnson.AtFull.Shape.k4GL
#print axioms Johnson.AtFull.Shape.k4StepL
#print axioms Johnson.AtFull.Shape.TabLetters
#print axioms Johnson.AtFull.Shape.lettersOf
#print axioms Johnson.AtFull.Shape.k2PL
#print axioms Johnson.AtFull.Shape.switchUL
#print axioms Johnson.AtFull.Shape.TabL.laid
#print axioms Johnson.AtFull.Shape.TabL.opening
#print axioms Johnson.AtFull.Shape.TabL.switch
#print axioms Johnson.AtFull.Shape.TabL.switchHead
#print axioms Johnson.AtFull.Shape.TabL.finish
#print axioms Johnson.AtFull.Shape.TabL.lookCalls
#print axioms Johnson.AtFull.Shape.TabL.lookDigits
#print axioms Johnson.AtFull.Shape.TabL.lookHead
#print axioms Johnson.AtFull.Shape.TabL.k4
#print axioms Johnson.AtFull.Shape.TabL.k5
#print axioms Johnson.AtFull.Shape.TabL.reads
#print axioms Johnson.AtFull.Shape.TabL.readsHead
#print axioms Johnson.AtFull.Shape.TabL.draw
#print axioms Johnson.AtFull.Shape.TabL.digits
#print axioms Johnson.AtFull.Shape.TabL.behind
#print axioms Johnson.AtFull.Shape.TabL.batch
#print axioms Johnson.AtFull.Shape.TabL.equation
#print axioms Johnson.AtFull.Shape.TabL.close
#print axioms Johnson.AtFull.Shape.TabL.shut
#print axioms Johnson.AtFull.Shape.TabL.cleared
#print axioms Johnson.AtFull.Shape.TabL.sendW
#print axioms Johnson.AtFull.Shape.TabL.linkRow
#print axioms Johnson.AtFull.Shape.TabL.headRow
#print axioms Johnson.AtFull.Shape.TabL.backRow
#print axioms Johnson.AtFull.Shape.TabL.cells
#print axioms Johnson.AtFull.Shape.TabL.g
#print axioms Johnson.AtFull.Shape.TabL.vals
#print axioms Johnson.AtFull.Shape.LettersAlike
