-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/Whole.lean: THE STATEMENTS OF Johnson/Road/K4/Rec/Statement.lean IN ONE CALL:
one record of the plan's letters, one record of equations of the meaning's fields, ONE TEST WITH
CODE ON
THE PLAN ("the six public items are open at the border"), one record of what then holds of the open
segment's part. Definitions, one statement and its proof: calls of Rec/Proofs.lean. GLUE.

  `RecPlan`: the plan's letters: codes, the request's shape, the layout, link by link the list of
    arrays, the plan's list of (tree, part), its list of the messages' shapes, `SentData`.
  `RecMeans Mg R`: THE SEVEN EQUATIONS (eLive, eFresh, eSeats, eShapes, eCodes, eSent, eTrees).
  `recItems m`, `openAllB M links ps k m`: the six items; the test.
  `RecIs A R n m`: the link's layout, its frame's shape and link, its list of arrays, `whereIs`,
    `maskOracle`, `seatAt`, `rowBits`, `placeBits` and the look of the ledger's arrays are the
    plan's terms.
  **`recordIsPlan`**: UNDER `RecMeans` (A PREMISE) AND A YES OF `openAllB` AT THE MEANING's OWN
    FILLING OF THE DOOR: at an unmarked statement inside the promise at border k: `RecIs` at
    n := the plan's number of messages at that border.

  `RecIs.maskSeat`, `.arrayIn`, `.atMoment1`, `.ownRow`, `.hasEnt`: five more readers of the part,
    each its plan's term, out of `RecIs`.

OBJECT: none of its own. USER: Johnson/Road/K4/Rec/Pins.lean, Rec/InT.lean. LETTERS, filled by
nobody: all.

Limits. `RecMeans` IS A PREMISE, shown at no term; two of its items lie in no composed filling yet
and have run nowhere. `openAllB` has been evaluated nowhere. Where no unmarked record meets the
promise the theorem holds for nothing. K04_law, the law of K4's block itself, IS NOT PROVED BY THIS.
Nothing on soundness.
-/
import Johnson.Road.K4.Rec.Proofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Pub More Meaning Numbers pubSets)
open VerifiableInference.Desc.First.FillSent (SentData treeLook whereIsP maskP)
open VerifiableInference.Desc.First.RecordPlan (seatP rowBitsP placeBitsP maskSeatP arrayInP
  atMoment1P ownRowP hasEntP ownRow_is hasEnt_is)
open VerifiableInference.Desc.K9 (seatAt maskSeat maskAt arrayIn atMoment1 ownRow)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (Frame)

/-- **The plan's letters.** -/
structure RecPlan where
  cs : Codes
  shape : Params.ReqShape
  layout : Params.ReqLayout
  arrs : ℕ → Array (ℕ × String)
  L : LaidP
  M : List OracleShape
  d : SentData

/-- **The seven equations of the meaning's fields.** -/
structure RecMeans {P W : Type} (Mg : Meaning P W) (R : RecPlan) : Prop where
  live : ELive Mg R.shape R.layout
  fresh : EFresh Mg R.arrs
  seats : ESeats Mg R.L
  shapes : EShapes Mg R.M
  codes : ECodes Mg R.cs
  sent : ESent Mg R.d
  trees : ETrees Mg R.d

/-- The six public items of segment m that are spent. -/
def recItems (m : ℕ) : List Pub :=
  [.more (some m) "frame.liveIs", .linkFresh m, .more none "K12.seatsCarried",
   .more none "K12.msgShapes", .more (some m) "frame.sentIs", .more (some m) "ledger.treesAre"]

/-- A TEST ON THE PLAN: the six are open at border k. M: the filling of the door. -/
def openAllB (M : More) (links : List ModelPart) (ps : List Place) (k m : ℕ) : Bool :=
  (recItems m).all fun q => ((pubSets M links ps)[k]?.getD []).contains q

/-- **The open segment's part reads as the plan says.** n: the number of messages sent. -/
structure RecIs (A : Part9) (R : RecPlan) (n m : ℕ) : Prop where
  layout : A.L.check.rows.layout = R.layout
  shape : A.L.check.frame.shape = R.shape
  arrays : A.L.arrayOf = R.arrs m
  link : A.L.check.frame.link = m
  whereIs : ∀ born message : ℕ,
    A.L.check.frame.whereIs born message = whereIsP R.d m born message
  mask : maskOracle A.L.check.frame = maskP R.shape R.d m
  seat : ∀ (own : List (ℕ × ℕ)) (o : ℕ), seatAt own A.d.book o = seatP own R.L.places n o
  rowBits : ∀ (o : ℕ) (part : OnBytes.Part), A.d.st.rowBits o part = rowBitsP R.M n o part
  placeBits : ∀ (o : ℕ) (part : OnBytes.Part),
    A.d.st.placeBits o part = placeBitsP R.cs R.M n o part
  trees : A.F.trees.toList.map treeLook = R.d.trees m

section
variable {A : Part9} {R : RecPlan} {n m : ℕ}

theorem RecIs.maskSeat (h : RecIs A R n m) (own : List (ℕ × ℕ)) :
    maskSeat own A = maskSeatP R.shape R.d own R.L.places n m := by
  have e1 : maskAt A.L.check.frame = maskP R.shape R.d m := h.mask
  unfold VerifiableInference.Desc.K9.maskSeat maskSeatP
  rw [e1]
  congr 1
  funext o
  exact h.seat own o

theorem RecIs.arrayIn (h : RecIs A R n m) (own : List (ℕ × ℕ)) (t : ℕ) :
    arrayIn own A t = arrayInP R.layout (R.arrs m) R.d own R.L.places n m t := by
  unfold VerifiableInference.Desc.K9.arrayIn arrayInP
  simp only [h.arrays, h.layout, h.whereIs, h.seat]

theorem RecIs.atMoment1 (h : RecIs A R n m) (c : ℕ × String) (X : Params.ReqArray) :
    atMoment1 A c X = atMoment1P R.shape m c X := by
  unfold VerifiableInference.Desc.K9.atMoment1 atMoment1P
  rw [h.link, h.shape]
  try rfl

theorem RecIs.ownRow (h : RecIs A R n m) (x : Ent) : ownRow A.F x = ownRowP (R.d.trees m) x :=
  ownRow_is h.trees x

theorem RecIs.hasEnt (h : RecIs A R n m) (x : Ent) :
    Fork.hasEnt A.F.trees x = hasEntP (R.d.trees m) x := hasEnt_is h.trees x

end

/-- THE STATEMENT. -/
def RecordIsPlan : Prop :=
  ∀ (P W : Type) (Fr : Frame) (N : Numbers) (Mg : Meaning P W) (Z : P) (links : List ModelPart)
    (ps : List Place) (k m : ℕ) (b : S × Fr.E.Str) (A : Part9) (R : RecPlan),
    RecMeans Mg R → openAllB Mg.more links ps k m = true → AtBorder N Mg Z links ps k b A →
    RecIs A R (N.msgsAt ps[k]?) m

/-- A yes of the test: each of the six is open. -/
theorem open_of_all {P W : Type} {Mg : Meaning P W} {links : List ModelPart} {ps : List Place}
    {k m : ℕ} (h : openAllB Mg.more links ps k m = true) {q : Pub} (hq : q ∈ recItems m) :
    OpenAt Mg links ps k q := by
  have h1 := List.all_eq_true.mp h q hq
  unfold OpenAt
  simpa using h1

/-- **UNDER `RecMeans` (A PREMISE) and a yes of `openAllB`: the record's part is the plan's.** -/
theorem recordIsPlan : RecordIsPlan := by
  intro P W Fr N Mg Z links ps k m b A R E hO h
  have o1 : OpenAt Mg links ps k (.more (some m) "frame.liveIs") :=
    open_of_all hO (by simp [recItems])
  have o2 : OpenAt Mg links ps k (.linkFresh m) := open_of_all hO (by simp [recItems])
  have o3 : OpenAt Mg links ps k (.more none "K12.seatsCarried") :=
    open_of_all hO (by simp [recItems])
  have o4 : OpenAt Mg links ps k (.more none "K12.msgShapes") :=
    open_of_all hO (by simp [recItems])
  have o5 : OpenAt Mg links ps k (.more (some m) "frame.sentIs") :=
    open_of_all hO (by simp [recItems])
  have o6 : OpenAt Mg links ps k (.more (some m) "ledger.treesAre") :=
    open_of_all hO (by simp [recItems])
  have l := layoutIs P W Fr N Mg Z links ps k m b A R.shape R.layout E.live o1 h
  have w := whereIs P W Fr N Mg Z links ps k m b A R.d E.sent o5 h
  exact
    { layout := l.1
      shape := l.2
      arrays := arraysAre P W Fr N Mg Z links ps k m b A R.arrs E.fresh o2 h
      link := w.1
      whereIs := w.2
      mask := maskIs P W Fr N Mg Z links ps k m b A R.d R.shape R.layout E.sent E.live o5 o1 h
      seat := seatIs P W Fr N Mg Z links ps k b A R.L E.seats o3 h
      rowBits := rowBitsAre P W Fr N Mg Z links ps k b A R.M E.shapes o4 h
      placeBits := placeBitsAre P W Fr N Mg Z links ps k b A R.M R.cs E.shapes E.codes o4 h
      trees := treesAre P W Fr N Mg Z links ps k m b A R.d E.trees o6 h }

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.recordIsPlan
