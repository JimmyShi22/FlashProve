-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/Rel.lean: WHAT TWO PUBLIC RECORDS SHARE AT ALL FILES IN THE GOALS' SCOPE,
AND THE RELATION BETWEEN SHAPES UNDER WHICH THE RUNS ON SHAPES OF THE TWO RECORDS GO ALIKE.
Definitions and laws by unfolding; nothing is evaluated.

What moves. In scope (VerifierAndGoals.InScope) eight numbers of the parameter file are free, and the scale
file. flat lays these fields of the record that publicOfO returns to fixed values: the scan's values
and its record's eight numbers; eps1, eps2, epsF in the layers' shape; the scales; six numbers of
the head's shape; of each attention plan the shifts in its shape, each call's shift and table there,
and each call's table in its lookup's record. That nothing else moves is sameRead_in_scope's claim
(Johnson/AtFull/Shape/Scope/RelScope.lean), not this file's.

* stripCall, stripF, stripA, stripS, stripPlan: the fixed value for what moves in a plan.
* flatP, flatL, flatLay, flatH, flat: a record with every moving field laid to a fixed value.
* **SameRead X X₀**: flat X = flat X₀: an equation on fields of the record alone. Its readers:
  SameRead.G and the others below.
* stripH, **strip**: a shape on which the calls' tables in look and lookHeard are laid to a fixed
  value. The lookup's steps copy Forest.Shape into these two components (lookHeardSh). That no other
  component holds an attention plan's table is a reading (the notes on the sorts), no theorem here:
  the laws on the sorts show what they need of it.
* **RelX X X₀ a a'**: strip a = strip a'. Its readers: RelX.marked and the others below. relX_of: the
  builder from the components.
* oddAt, **RelAt X X₀ n a a'**: the relation at the border in front of member n: RelX in front of the
  members of an attention link, equality elsewhere.

Limits. Definitions. That the two records of a run meet SameRead: RelScope.lean. That the steps go
alike under RelX: the laws on the sorts of cells. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.FrameForm
import Johnson.HonestTrace.Run.SetUpTurnDefs
import Johnson.HonestTrace.Run.SetUpSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape (ChainSh HeardAll)
open HonestTraceRun.SetUp (scanTurn layTurn SamePlans)

/-! ## 1 What moves in an attention plan -/

/-- A call with no table. -/
def stripCall (c : Call) : Call := { c with tau := none }

/-- A lookup's record, its calls with no table. -/
def stripF (h : Forest.Shape) : Forest.Shape := { h with calls := h.calls.map stripCall }

/-- An attention call with no shift and no table. -/
def stripA (k : Attention.ACall) : Attention.ACall := { k with sh := 0, call := stripCall k.call }

/-- An attention shape with no shifts and no tables of calls. -/
def stripS (S : Attention.Shape) : Attention.Shape :=
  { S with cf := { S.cf with sh := #[] }, calls := S.calls.map stripA }

/-- A plan with no shifts and no tables of calls. -/
def stripPlan (a : Attention.Plan) : Attention.Plan :=
  { a with S := stripS a.S, fs := stripF a.fs }

/-! ## 2 The record -/

/-- The eight numbers at 0. -/
def zeroLines : VerifierAndGoals.FreeLines := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The scan with no list of values and the eight numbers at 0. -/
def flatP (P : PolScan) : PolScan := scanTurn P [] zeroLines

/-- The layers' layout with the three numbers at 0. -/
def flatL (y : Layer.Lay) : Layer.Lay := layTurn y zeroLines

/-- The layers' record with the three numbers at 0 and no scales. -/
def flatLay (L : Layer.Pub) : Layer.Pub := { L with y := flatL L.y, sc := ⟨#[], 0, 0⟩ }

/-- The head's shape with the six numbers at 0. -/
def flatH (h : Head.Shape) : Head.Shape :=
  { h with MF := 0, KF := 0, epsF := 0, clipC := 0, theta := 0, cap := 0 }

/-- The record with every field that moves laid to a fixed value, and no digests. -/
def flat (X : Verify.Public) : Verify.Public :=
  { P := flatP X.P, digests := ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty⟩,
    layers := flatLay X.layers, hS := flatH X.hS, HLy := X.HLy, G := X.G,
    A := X.A.map stripPlan, H := X.H, owner := X.owner }

/-- **What the first halves of the cells may read**: all but what moves. -/
def SameRead (X X₀ : Verify.Public) : Prop := flat X = flat X₀

namespace SameRead
variable {X X₀ : Verify.Public}

theorem eq (h : SameRead X X₀) : flat X = flat X₀ := h
theorem refl (X : Verify.Public) : SameRead X X := rfl
theorem symm (h : SameRead X X₀) : SameRead X₀ X := Eq.symm h.eq

theorem G (h : SameRead X X₀) : X.G = X₀.G := by
  have e := congrArg Verify.Public.G h.eq
  exact e
theorem H (h : SameRead X X₀) : X.H = X₀.H := by
  have e := congrArg Verify.Public.H h.eq
  exact e
theorem HLy (h : SameRead X X₀) : X.HLy = X₀.HLy := by
  have e := congrArg Verify.Public.HLy h.eq
  exact e
theorem owner (h : SameRead X X₀) : X.owner = X₀.owner := by
  have e := congrArg Verify.Public.owner h.eq
  exact e
theorem frame (h : SameRead X X₀) : X.P.frame = X₀.P.frame := by
  have e := congrArg (fun W : Verify.Public => W.P.frame) h.eq
  exact e
theorem polCalls (h : SameRead X X₀) : X.P.polCalls = X₀.P.polCalls := by
  have e := congrArg (fun W : Verify.Public => W.P.polCalls) h.eq
  exact e
/-- The scan, but for its list of values and the eight numbers. -/
theorem scan (h : SameRead X X₀) : flatP X.P = flatP X₀.P := by
  have e := congrArg Verify.Public.P h.eq
  exact e
/-- The layers' record, but for the three numbers and the scales. -/
theorem layers (h : SameRead X X₀) : flatLay X.layers = flatLay X₀.layers := by
  have e := congrArg Verify.Public.layers h.eq
  exact e
/-- The layers' layout, but for the three numbers. -/
theorem lay (h : SameRead X X₀) : flatL X.layers.y = flatL X₀.layers.y := by
  have e := congrArg (fun W : Verify.Public => W.layers.y) h.eq
  exact e
theorem rd (h : SameRead X X₀) : X.layers.rd = X₀.layers.rd := by
  have e := congrArg (fun W : Verify.Public => W.layers.rd) h.eq
  exact e
theorem rope (h : SameRead X X₀) : X.layers.rope = X₀.layers.rope := by
  have e := congrArg (fun W : Verify.Public => W.layers.rope) h.eq
  exact e
theorem wsLay (h : SameRead X X₀) : X.layers.wsLay = X₀.layers.wsLay := by
  have e := congrArg (fun W : Verify.Public => W.layers.wsLay) h.eq
  exact e
theorem V (h : SameRead X X₀) : X.layers.V = X₀.layers.V := by
  have e := congrArg (fun W : Verify.Public => W.layers.V) h.eq
  exact e
theorem tails (h : SameRead X X₀) : X.layers.tails = X₀.layers.tails := by
  have e := congrArg (fun W : Verify.Public => W.layers.tails) h.eq
  exact e
theorem set (h : SameRead X X₀) : X.layers.set = X₀.layers.set := by
  have e := congrArg (fun W : Verify.Public => W.layers.set) h.eq
  exact e
/-- The head's shape, but for the six numbers. -/
theorem hS (h : SameRead X X₀) : flatH X.hS = flatH X₀.hS := by
  have e := congrArg Verify.Public.hS h.eq
  exact e
/-- The head's shape whole, but for the six numbers. -/
theorem hSrest (h : SameRead X X₀) :
    X.hS = { X₀.hS with
      MF := X.hS.MF, KF := X.hS.KF, epsF := X.hS.epsF, clipC := X.hS.clipC, theta := X.hS.theta,
      cap := X.hS.cap } := by
  have e := h.hS
  calc X.hS = { flatH X.hS with
        MF := X.hS.MF, KF := X.hS.KF, epsF := X.hS.epsF, clipC := X.hS.clipC, theta := X.hS.theta,
        cap := X.hS.cap } := rfl
    _ = { flatH X₀.hS with
        MF := X.hS.MF, KF := X.hS.KF, epsF := X.hS.epsF, clipC := X.hS.clipC, theta := X.hS.theta,
        cap := X.hS.cap } := by rw [e]
    _ = _ := rfl
/-- The attention plans, but for what moves in them. -/
theorem plans (h : SameRead X X₀) : X.A.map stripPlan = X₀.A.map stripPlan := by
  have e := congrArg Verify.Public.A h.eq
  exact e
/-- The layers' record whole, but for the layout and the scales. -/
theorem layersRest (h : SameRead X X₀) :
    X.layers = { X₀.layers with y := X.layers.y, sc := X.layers.sc } := by
  have e := h.layers
  generalize X.layers = L at e ⊢
  generalize X₀.layers = L₀ at e ⊢
  cases L with
  | mk y rd sc rope wsLay V tokv tails set =>
    cases L₀ with
    | mk y' rd' sc' rope' wsLay' V' tokv' tails' set' =>
      injection e with _ e2 _ e4 e5 e6 e7 e8 e9
      subst e2 e4 e5 e6 e7 e8 e9
      rfl
theorem sizeA (h : SameRead X X₀) : X.A.size = X₀.A.size := by
  have e := congrArg Array.size h.plans
  rwa [Array.size_map, Array.size_map] at e
/-- Number by number. -/
theorem atA (h : SameRead X X₀) (g : Nat) : X.A[g]?.map stripPlan = X₀.A[g]?.map stripPlan := by
  have e := congrArg (fun W : Array Attention.Plan => W[g]?) h.plans
  simpa [Array.getElem?_map] using e
/-- At a number where both have a plan. -/
theorem plan (h : SameRead X X₀) {g : Nat} {a a₀ : Attention.Plan} (h1 : X.A[g]? = some a)
    (h2 : X₀.A[g]? = some a₀) : stripPlan a = stripPlan a₀ := by
  have e := h.atA g
  rw [h1, h2] at e
  exact Option.some.inj e

/-- The layers' layout whole, but for the three numbers. -/
theorem layRest (h : SameRead X X₀) :
    X.layers.y = { X₀.layers.y with
      h := { X₀.layers.y.h with
        eps1 := X.layers.y.h.eps1, eps2 := X.layers.y.h.eps2, epsF := X.layers.y.h.epsF } } := by
  have e := h.lay
  calc X.layers.y = { flatL X.layers.y with
        h := { (flatL X.layers.y).h with
          eps1 := X.layers.y.h.eps1, eps2 := X.layers.y.h.eps2, epsF := X.layers.y.h.epsF } } := rfl
    _ = { flatL X₀.layers.y with
        h := { (flatL X₀.layers.y).h with
          eps1 := X.layers.y.h.eps1, eps2 := X.layers.y.h.eps2, epsF := X.layers.y.h.epsF } } := by
      rw [e]
    _ = _ := rfl

/-- SameRead holds all of SamePlans: so the laws of Johnson/HonestTrace/Run/SetUpSame.lean apply. -/
theorem toSamePlans (h : SameRead X X₀) : SamePlans X X₀ where
  frame := h.frame
  lay := ⟨_, _, _, h.layRest⟩
  rd := h.rd
  wsLay := h.wsLay
  G := h.G
  H := h.H
  HLy := h.HLy
  head := by
    have e := h.hS
    have e1 := congrArg Head.Shape.lt e
    have e2 := congrArg Head.Shape.lPd e
    have e3 := congrArg Head.Shape.XL e
    exact ⟨e1, e2, e3⟩
  sizeA := h.sizeA
  A := fun g a a₀ h1 h2 => by
    have e := h.plan h1 h2
    have e1 := congrArg Attention.Plan.seam e
    have e2 := congrArg Attention.Plan.ns e
    have e3 := congrArg Attention.Plan.own e
    have e4 := congrArg (fun p : Attention.Plan => OnBytes.Model.forestSize p.fs) e
    exact ⟨e1, e2, e3, e4⟩

end SameRead

/-! ## 3 The shape -/

/-- What a lookup heard, its record's calls with no table. -/
def stripH (g : HeardAll) : HeardAll := { g with shape := stripF g.shape }

/-- **A shape with no table of a call in look and lookHeard.** -/
def strip (a : ShA) : ShA :=
  (ChainSh.mk a.1.marked a.1.here a.1.tl a.1.led a.1.tables a.1.rowsOwed a.1.core a.1.reply
    a.1.indexMasks a.1.pile a.1.atEnd a.1.check a.1.link (a.1.look.map stripH)
    (a.1.lookHeard.map stripH) a.1.own a.1.head a.1.att a.1.fin, a.2)

/-- **THE RELATION.** X and X₀ name the two records; nothing is read of them here. -/
def RelX (_X _X₀ : Verify.Public) (a a' : ShA) : Prop := strip a = strip a'

namespace RelX
variable {X X₀ : Verify.Public} {a a' b : ShA}

theorem eq (h : RelX X X₀ a a') : strip a = strip a' := h
theorem refl (a : ShA) : RelX X X₀ a a := rfl
theorem symm (h : RelX X X₀ a a') : RelX X₀ X a' a := Eq.symm h.eq
theorem trans {X₁ : Verify.Public} (h : RelX X X₀ a a') (h' : RelX X₀ X₁ a' b) : RelX X X₁ a b :=
  Eq.trans h.eq h'.eq

theorem marked (h : RelX X X₀ a a') : a.1.marked = a'.1.marked := by
  have e := congrArg (fun z : ShA => z.1.marked) h.eq
  exact e
theorem here (h : RelX X X₀ a a') : a.1.here = a'.1.here := by
  have e := congrArg (fun z : ShA => z.1.here) h.eq
  exact e
theorem tl (h : RelX X X₀ a a') : a.1.tl = a'.1.tl := by
  have e := congrArg (fun z : ShA => z.1.tl) h.eq
  exact e
theorem led (h : RelX X X₀ a a') : a.1.led = a'.1.led := by
  have e := congrArg (fun z : ShA => z.1.led) h.eq
  exact e
theorem tables (h : RelX X X₀ a a') : a.1.tables = a'.1.tables := by
  have e := congrArg (fun z : ShA => z.1.tables) h.eq
  exact e
theorem rowsOwed (h : RelX X X₀ a a') : a.1.rowsOwed = a'.1.rowsOwed := by
  have e := congrArg (fun z : ShA => z.1.rowsOwed) h.eq
  exact e
theorem core (h : RelX X X₀ a a') : a.1.core = a'.1.core := by
  have e := congrArg (fun z : ShA => z.1.core) h.eq
  exact e
theorem reply (h : RelX X X₀ a a') : a.1.reply = a'.1.reply := by
  have e := congrArg (fun z : ShA => z.1.reply) h.eq
  exact e
theorem indexMasks (h : RelX X X₀ a a') : a.1.indexMasks = a'.1.indexMasks := by
  have e := congrArg (fun z : ShA => z.1.indexMasks) h.eq
  exact e
theorem pile (h : RelX X X₀ a a') : a.1.pile = a'.1.pile := by
  have e := congrArg (fun z : ShA => z.1.pile) h.eq
  exact e
theorem atEnd (h : RelX X X₀ a a') : a.1.atEnd = a'.1.atEnd := by
  have e := congrArg (fun z : ShA => z.1.atEnd) h.eq
  exact e
theorem check (h : RelX X X₀ a a') : a.1.check = a'.1.check := by
  have e := congrArg (fun z : ShA => z.1.check) h.eq
  exact e
theorem link (h : RelX X X₀ a a') : a.1.link = a'.1.link := by
  have e := congrArg (fun z : ShA => z.1.link) h.eq
  exact e
theorem look (h : RelX X X₀ a a') : a.1.look.map stripH = a'.1.look.map stripH := by
  have e := congrArg (fun z : ShA => z.1.look) h.eq
  exact e
theorem lookHeard (h : RelX X X₀ a a') : a.1.lookHeard.map stripH = a'.1.lookHeard.map stripH := by
  have e := congrArg (fun z : ShA => z.1.lookHeard) h.eq
  exact e
theorem own (h : RelX X X₀ a a') : a.1.own = a'.1.own := by
  have e := congrArg (fun z : ShA => z.1.own) h.eq
  exact e
theorem head (h : RelX X X₀ a a') : a.1.head = a'.1.head := by
  have e := congrArg (fun z : ShA => z.1.head) h.eq
  exact e
theorem att (h : RelX X X₀ a a') : a.1.att = a'.1.att := by
  have e := congrArg (fun z : ShA => z.1.att) h.eq
  exact e
theorem fin (h : RelX X X₀ a a') : a.1.fin = a'.1.fin := by
  have e := congrArg (fun z : ShA => z.1.fin) h.eq
  exact e
theorem forms (h : RelX X X₀ a a') : a.2 = a'.2 := by
  have e := congrArg Prod.snd h.eq
  exact e

end RelX

theorem strip_congr {a a' : ShA} (h : a = a') (X X₀ : Verify.Public) : RelX X X₀ a a' :=
  congrArg strip h

/-- From the components: the builder of a relation. -/
theorem relX_of {X X₀ : Verify.Public} {a a' : ShA} (h1 : a.1.marked = a'.1.marked)
    (h2 : a.1.here = a'.1.here) (h3 : a.1.tl = a'.1.tl) (h4 : a.1.led = a'.1.led)
    (h5 : a.1.tables = a'.1.tables) (h6 : a.1.rowsOwed = a'.1.rowsOwed)
    (h7 : a.1.core = a'.1.core) (h8 : a.1.reply = a'.1.reply)
    (h9 : a.1.indexMasks = a'.1.indexMasks) (h10 : a.1.pile = a'.1.pile)
    (h11 : a.1.atEnd = a'.1.atEnd) (h12 : a.1.check = a'.1.check) (h13 : a.1.link = a'.1.link)
    (h14 : a.1.look.map stripH = a'.1.look.map stripH)
    (h15 : a.1.lookHeard.map stripH = a'.1.lookHeard.map stripH) (h16 : a.1.own = a'.1.own)
    (h17 : a.1.head = a'.1.head) (h18 : a.1.att = a'.1.att) (h19 : a.1.fin = a'.1.fin)
    (h20 : a.2 = a'.2) : RelX X X₀ a a' := by
  unfold RelX strip
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

/-- The border in front of member n lies in an attention link: the members 14 l + 1 to 14 l + 14 of
an odd link l < 24. -/
def oddAt (n : Nat) : Bool := decide (1 ≤ n) && decide (n < 337) && ((n - 1) / 14 % 2 == 1)

/-- **THE RELATION AT A BORDER.** -/
def RelAt (X X₀ : Verify.Public) (n : Nat) (a a' : ShA) : Prop :=
  if oddAt n = true then RelX X X₀ a a' else a = a'

theorem relAt_of_eq {X X₀ : Verify.Public} {n : Nat} {a a' : ShA} (h : a = a') :
    RelAt X X₀ n a a' := by
  unfold RelAt
  split
  · exact strip_congr h X X₀
  · exact h

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.SameRead.plan
#print axioms Johnson.AtFull.Shape.Scope.relX_of
