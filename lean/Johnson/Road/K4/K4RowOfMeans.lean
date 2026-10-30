-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4RowOfMeans.lean: K4's ROW AT THE TABLE OF JOINTS, WHOLE, ON THE SIDE OF THE
PROMISE AND OF WHAT RIDES: THE THREE STRUCTURES OF LINES THAT K4's LAW AT THE TABLE TAKES (`K4Front`
· `K4Riders` · `K4Keeps`) OUT OF: the structure of equations on the meaning (`K4Means`) · ONE LINE
ON THE NAMES AT THE DOOR THAT PASS K4's PLACE, GENERAL IN THEIR SORT rest (`K4Kept`, K4Reads.lean:
of other authors' names this file has one: "pile.room", which K4's row asks) · the lines on its
owners' letters (`K4Reads`) · ONE STRUCTURE OF TESTS AND EQUATIONS ON THE PUBLIC PARAMETERS
(`K4RowPlan`: each field a test with code, an equation, or a line that a lemma draws from such a
test: sort: `riders_are`; only: `only_of_fit`) · ONE FACT ON THE PIECE (hbase) · AND ONE STRUCTURE
ON THE SEATS (`K4Seats`). Definitions, one statement with its proof: calls.

  `K4RowPlan`: THE PUBLIC PARAMETERS' SIDE, GATHERED: which sorts ride (sort), and that the lookup's
    own claims are open there (objOpen) · the table's and K4's tests on the lists of places
    (k4NextFit · k4ToldFit · bookFit · fenceFit · pubFit · k4PubFit · k4TiedFit · only) · what the
    door's filling lays at K4's place (askRoom · askLeft · askBare) · where the two lookups stand
    (piece 2, piece 7) · the map of names at segment m (own · objects · planes · join) · the public
    parameters' numbers nextOf m, and nsOf m, WHICH IS hp.ns (the number at which the promise in
    front speaks of the segment's ledger), and that an entry of the index masks' ledger is left
    (room1) · the three tests in the totality laws' and lookIn's places (`frontB` · `rowB` ·
    `lookInPlanB`) · the pending row's layout and count, and the lookup's shape, are K4's · three
    tests under which the verifier's state reads as the public parameters say (openAll · maskP ·
    readsP: Rec/InTFour.lean) · four lines on the public parameters X.
  **`k4Row_of_means`**: the three structures of lines.

THE ONE STRUCTURE OF ANOTHER KIND: `K4Seats`: THE SEATS' TIES: segment m's readers are those of one
value l of the Lean type `Link`; l's sub-protocols number 1 and 2 state, under their names, runs
that do what the lookup's sub-protocol's ("objects", "guests") and K4's sub-protocol's ("front",
"back") do. PAYERS: InT/SeatTie.lean, Riders/SeatsTies.lean (at a sub-protocol behind the driver's
guard), Riders/SeatsAtDesc.lean (at the IOP as written in Lean, at its own value of that type). AND
R : `K4Reads`: lines on letters of which some have no term yet. AND hDoor: ONE NAMED PREMISE OVER
THE MEANING: "what the door's filling lets the row at
this place make holds after it accepts" (no tie asks that the door make nothing there): idle where
the door makes no name at K4's place (`door_none`).

Limits. EVERY PREMISE STANDS. The names that only
carry a fact on every reached state across many authors' sub-protocols ARE NOT IN the composed
meaning's door: THIRTEEN (the weights' one · the proximity test's door's four · the pile's three ·
"pile.room" · "frame.liveIs" · "K8.lay7" · "K8.onThird" · "K8.funsThird"), and four conjuncts of "in
order": a theorem here that spends, keeps or makes one of them stands at a WIDER meaning than the
composed one (a bridge's side), and is carried to it by a bridge under facts on reached states that
are owed. No field of `K4RowPlan` is evaluated here, and no file that evaluates one is imported. AT
THE COMPOSED MEANING WITH THE SMALL DOOR THE PREMISES HOLD TOGETHER NOWHERE: "pile.room" and three
of openAll's six names are struck from that door, so askRoom and openAll are false there (by
reading): THE THEOREM IS MEANT AT THE WIDER MEANING. Beside the road, over other grounds:
Riders/PlanFull.lean asks Lean's kernel ten of the fields, and Riders/Full.lean one (sort), at the
full size's written lists; seven of the ten read a door: whichever that file imports;
Riders/OnXOfPlan.lean has seven as theorems in the goals' scope. Of `K4Means`' equations those at
names that are not open at a door are spent by nothing at that door. No run is cited here. NO TERM
OF THE TYPE `K4RowPlan` STANDS ANYWHERE: its fields are shown together at no public parameters. THIS
IS THE PROMISE's SIDE: what the claims that K4 opens are WORTH is not touched. K04_law, the law of
K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K4OfMeans
import Johnson.Road.K4.K4FrontOfMeans
import Johnson.Road.K4.Riders.MakeOfMeans
import Johnson.Road.K4.Riders.OwnAtMeans
import Johnson.Road.K4.Riders.InRowAtMeans
import Johnson.Road.K4.Riders.ObjectsAtMeans
import Johnson.Road.K4.Riders.AsksAtMeans
import Johnson.Road.K4.Riders.MoreFront
import Johnson.Road.K4.Rec.InTFour
import Johnson.Road.K4.Riders.ObjAsksOfMeans
import Johnson.Road.K4.Riders.PlanTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Total (rowB frontB)
open OnBytes.Road.K4.InT (StatesAt)
open OnBytes.Road.K4.Rec (inT_four_of_front openAllB readsArrayP)
open VerifiableInference.Desc.First.RecordPlan (maskSeatP)
open VerifiableInference.Desc.First.FillBare (leftName bareName)
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open OnBytes.Road.K4.Riders (riderSort k4PubFit k4TiedFit lookInPlanB ObjAsks hobj_of_means
  hObj_of_means make_of_means hOwn_of_means hIn_of_means hRow_of_means asks_of_means left_of_means
  hroom_of_means objAsks_of_means placeAt_link roomName)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Claim Link K9.LinkHoles K9.statesOfLink K9.readersOfLink)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning start openSets pubSets pubFit bookFit
  fenceFit moreItem)
open VerifiableInference.Desc.First.FillK4 (isLay k4NextFit k4ToldFit)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.OnPublicFiles (LeftQ)
open VerifiableInference.Desc.Sound (Frame Piece insQ outsQ openAfter onQ MsgT)

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}

/-- **The public parameters' side of K4's row, gathered**: 36 fields, ALL PREMISES of
`k4Row_of_means`. par.g and m are tied by no field (the caller has par.g = m / 2). -/
structure K4RowPlan (D : K4Data Xi P Tok rows cols nR kC X) (rest : Option ℕ → String → Bool)
    (links : List ModelPart) (ps : List Place)
    (k m : ℕ) (pl : Place) (par : Par) (told : List (List VerifiableInference.Desc.Oracle))
    (pol KL : ByteArray) (layout : Option ByteArray) (hp : Layer.HPlan2) (n : ℕ) : Prop where
  linksIs : D.links = links
  sort : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
    ¬ insQ links ps k i → riderSort m i = true
  next : k4NextFit links ps = true
  toldFit : k4ToldFit links ps told = true
  book : bookFit D.N ps told = true
  fence : fenceFit D.N links ps = true
  fit : pubFit D.moreL links ps = true
  pub : k4PubFit rest D.moreL links ps = true
  tied : k4TiedFit links ps = true
  only : ∀ m', isLay links m' = true →
    Pub.callerIn m' ∈ (pubSets D.moreL links ps)[k]?.getD [] → m' = m
  askRoom : roomName m ∈ (D.moreL.rows links pl).asks
  askLeft : leftName m ∈ (D.moreL.rows links pl).asks
  askBare : bareName m ∈ (D.moreL.rows links pl).asks
  objOpen : Item.formsT m 2 "objects" ∈ (openSets links ps (start links))[k]?.getD []
  room1 : 1 ≤ D.free0 - rowsBefore D.fvs m
  front : frontB (!par.k3Runs) par.P par.hp par.g par.P.y.fo = true
  shape : X.y.fo = par.P.y.fo
  openAll : openAllB D.moreL links ps k m = true
  maskP : (maskSeatP D.D3.shape D.sd (D.N.sent m 0) D.d12.L.places (D.N.msgsAt ps[k]?) m).isSome =
    true
  readsP : readsArrayP par.hp D.D3.shape D.D3.layout (D.D3.arrayOf.getD m #[]) m (D.sd.trees m) =
    true
  pc2 : VerifiableInference.Desc.K3.pieceAt X m false = 2
  pc7 : VerifiableInference.Desc.K3.pieceAt X m true = 7
  runsOwn : D.runs m 3 "own" = [(2, "front"), (2, "back")]
  runsObj : D.runs m 2 "objects" = [(1, "objects"), (1, "guests")]
  runsPl : D.runs m 2 "planes" = []
  runsJo : D.runs m 2 "join" = []
  nextOf : D.nextOf m = some n
  nsOf : D.nsOf m = some hp.ns
  lookIn : lookInPlanB par X m n hp.ns = true
  lay : D.d1.lay = par.P.wsLay
  ncl : D.d1.ncl m = par.hp.NCL
  row : rowB par.P par.g par.hp.NCL D.d1.lin = true
  pubOf : Verify.publicOf pol KL layout = .ok X
  notHead : m ≠ (if X.p4 then 2 else 1) * X.NGr
  step : m % (if X.p4 then 2 else 1) = 0
  plan : X.G[m / (if X.p4 then 2 else 1)]? = some hp

/-- **The seats' ties, gathered**: segment m's readers are those of a segment l, whose sub-protocols
number 1
and 2
state, under their names, runs that do what the lookup's sub-protocol's and K4's sub-protocol's runs
do. -/
structure K4Seats (D : K4Data Xi P Tok rows cols nR kC X) (m : ℕ) (par : Par) (Hh : K9.LinkHoles)
    (l : Link S Claim) (nO nG : String) (runO runG : ℕ → S → Except String (List Claim × S)) :
    Prop where
  Rd : D.Rd m = K9.readersOfLink Hh l
  st : ∀ s : S, StatesAt (K9.statesOfLink l) 2 par "front" s ∧
    StatesAt (K9.statesOfLink l) 2 par "back" s
  fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO)
  oRun : ObjRun runO
  fG : (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some (nG, runG)
  gRun : GuestRun runG

variable {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X}
  {Z : P} {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}
  {told : List (List VerifiableInference.Desc.Oracle)} {pol KL : ByteArray}
  {layout : Option ByteArray} {hp : Layer.HPlan2} {n : ℕ}
  {Hh : K9.LinkHoles} {l : Link S Claim} {nO nG : String}
  {runO runG : ℕ → S → Except String (List Claim × S)}

/-- **UNDER E, Kp, R, H, Pl, hbase, Se, hDoor AND hDoorP (ALL PREMISES): K4's row's three structures
of
lines.** -/
theorem k4Row_of_means (E : K4Means Mg D) {rest : Option ℕ → String → Bool}
    (Kp : K4Kept Mg rest Z) (R : K4Reads D Z Fr q.base) (H : AtK4 links ps k m pl)
    (Pl : K4RowPlan D rest links ps k m pl par told pol KL layout hp n)
    (hbase : D.N.treesAt (some pl) = q.base)
    (Se : K4Seats D m par Hh l nO nG runO runG)
    (hDoor : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ nm ∈ (Mg.more.rows links pl).makes,
      Mg.pub (moreItem nm) (Z, (behindOf seatS q a τ o G').1) = true)
    (hDoorP : ∀ nm ∈ (Mg.more.rows links pl).makes, ∀ a, Mg.pubP (moreItem nm) a) :
    K4Front Mg Z links ps m X.y.fo X.y.h.lmb 0 (LeftQ hp.ns) ∧
      K4Riders D.N Mg Z links ps k m q par ∧ ∃ pl', K4Keeps D.N Mg Z links ps k m pl pl' q par := by
  have fit' : pubFit Mg.more links ps = true := E.more ▸ Pl.fit
  have A : ObjAsks Fr Mg D Z links ps k m Hh l nO nG runO runG :=
    objAsks_of_means E R H Pl.linksIs fit' (E.more ▸ Pl.askBare) Pl.objOpen Se.Rd Pl.runsObj Se.fO
      Se.oRun Se.fG Se.gRun
  have hLo : ((pubSets D.moreL links ps)[k]?.getD []).contains (.ledger m) = true := by
    have h1 := k4_open Mg H fit' (.ledger m) (by simp)
    rw [E.more] at h1
    simpa using h1
  have Kf := k4Front_of_means (Z := Z) E H Pl.linksIs Pl.pubOf Pl.notHead Pl.step Pl.plan Pl.fit
  refine ⟨Kf, k4Riders_of_means E R H Pl.sort (hobj_of_means E H Pl.linksIs fit' A), ?_⟩
  exact k4Keeps_of_means E R Kp H Kf Pl.next told Pl.toldFit Pl.book
    Pl.fence hbase
    (E.more ▸ Pl.only) Pl.linksIs Pl.pub Pl.tied Pl.pc2 (hObj_of_means E H Pl.linksIs fit' A)
    (make_of_means E H hDoor Pl.runsPl Pl.runsJo
      (hIn_of_means E H Pl.linksIs fit' Pl.pc7 Pl.nextOf Pl.nsOf Pl.lookIn
        fun _ hp => placeAt_link hp)
      (hOwn_of_means E A.Rd Pl.runsOwn
        (asks_of_means E H Kf Pl.shape Pl.nsOf Pl.front
          (left_of_means E H Pl.linksIs fit' (E.more ▸ Pl.askLeft))
          (fun a τ fo o G' ha hu y => inT_four_of_front E D.sd E.sentIs E.treesAre Z links ps k m
            par q Pl.openAll hLo Pl.maskP Pl.readsP a τ fo o G' ha hu y) Se.st))
      (hRow_of_means E Pl.lay Pl.ncl Pl.row
        (hroom_of_means E H fit' (E.more ▸ Pl.askRoom) Pl.room1)))
    hDoorP

/-- Where the door's filling makes no name at K4's place the premise hDoor is idle. -/
theorem door_none (h : (Mg.more.rows links pl).makes = []) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ nm ∈ (Mg.more.rows links pl).makes,
      Mg.pub (moreItem nm) (Z, (behindOf seatS q a τ o G').1) = true := by
  intro a τ fo o G' _ _ _ nm hnm
  rw [h] at hnm
  exact nomatch hnm

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.door_none
#print axioms OnBytes.Road.K4.k4Row_of_means
