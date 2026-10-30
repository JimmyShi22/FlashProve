-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/AllFilledBy.lean: THE TESTS `allFilled` AND `worthFilled`
(Johnson/Desc/First/AllFilled.lean) AS FUNCTIONS OF THE FOUR THINGS THAT THEY READ OF THE HALVES'
LETTERS: so that they can be evaluated at a written list of segments without a whole structure of
letters. Definitions with code, and that each IS the elder. No Mathlib.

  `hdOf X`: the head's segment's number off the public parameters X (the lookups' `K3.isHead`'s own
    term).
  `pieceBy`, `k3SortBy hd`, `k3ItemBy hd`, `k5ItemBy links`: the lookups' and the attention caller's
    tests "is the item mine", at that number and at a list of segments' sorts.
  `whoFillsBy hd mH links links5`, `unfilledBy`, `allFilledBy`, `worthNamedBy hd`, `worthFilledBy`.
  `whoFills_by`, `unfilled_by`, `allFilled_by`, `worthFilled_by`: each elder at D (at X) is its twin
    at hdOf D.d3.X, D.mH, D.links, D.d5.links (at hdOf X).

Limits. FOUR LETTERS STAND WHERE ONE SEGMENTS' LIST IS MEANT: that hdOf D.d3.X = D.mH is the place
of the head in D.links, and that D.d5.links = D.links, is said by nothing here (the composed filling
lays mH, d3.X and d5.links off one X and one list by its make). Nothing on soundness.

-/
import Johnson.Desc.First.AllFilled

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K13 (k13ItemC)
open VerifiableInference.Desc.First.FillK4 (k4Item)
open VerifiableInference.Desc.Kinds.Head (k6k7Item)
open VerifiableInference.Desc.First.Look (K3Data k3Item k3SortAt)
open VerifiableInference.Desc.First.FillP1 (p1Item)
open H2K5.Door (K5Data k5Item)
open VerifiableInference.Desc.First.FillSent (sentItem sent1Item)
open VerifiableInference.Desc.First.FillBare (leftItem)

/-- The head's segment's number, off the public parameters. -/
def hdOf (X : OnBytes.Model.Verify.Public) : Nat := (if X.p4 then 2 else 1) * X.NGr

/-- The piece of segment m at which the lookup on the digits, or on the calls, stands. -/
def pieceBy (hd m : Nat) (digits : Bool) : Nat :=
  if m == hd then (if digits then 8 else 3) else (if digits then 7 else 2)

def k3SortBy (hd m pc : Nat) : Option Bool :=
  if pc == pieceBy hd m true then some true
  else if pc == pieceBy hd m false then some false
  else none

theorem k3SortAt_by (X : OnBytes.Model.Verify.Public) (m pc : Nat) :
    k3SortAt X m pc = k3SortBy (hdOf X) m pc := rfl

def k3ItemBy (hd : Nat) : Pub → Bool
  | .lookIn m pc => (k3SortBy hd m pc).isSome
  | .lookOut m pc => (k3SortBy hd m pc).isSome
  | .linkFresh _ => true
  | .left _ => true
  | .leftOn _ => true
  | _ => false

theorem k3Item_by (d : K3Data) (q : Pub) : k3Item d q = k3ItemBy (hdOf d.X) q := by
  cases q <;> rfl

def k5ItemBy (links : List ModelPart) : Pub → Bool
  | .callerIn m => links[m]? == some .attention
  | .look m => links[m]? == some .attention
  | .more (some m) n =>
    (links[m]? == some .attention) &&
      (n == "K5.readsThere" || n == "K5.okAt" || n == "K5.liveReq" || n == "K5.plain")
  | _ => false

theorem k5Item_by (d : K5Data) (q : Pub) : k5Item d q = k5ItemBy d.links q := by
  cases q with
  | more sg name => cases sg <;> rfl
  | _ => rfl

/-- Which layer answers at a public item. -/
def whoFillsBy (hd mH : Nat) (links links5 : List ModelPart) (q : Pub) : Option String :=
  if formsItem q then some "the runs' forms"
  else if k13ItemC q then some "the index's and the last blocks'"
  else if k3ItemBy hd q then some "the lookups'"
  else if k6k7Item mH q then some "the head's"
  else if k4Item links q then some "the feed-forward caller's"
  else if p1Item q then some "the row on the weights' and the smallness test's names'"
  else if k5ItemBy links5 q then some "the attention caller's"
  else if sentItem q then some "what stands sent"
  else if sent1Item q then some "what stands sent, later"
  else if leftItem links q then some "the feed-forward caller's two names"
  else if keeperItem q then some "the table's own"
  else none

theorem whoFills_by (D : PubData) (q : Pub) :
    whoFills D q = whoFillsBy (hdOf D.d3.X) D.mH D.links D.d5.links q := by
  unfold whoFills whoFillsBy
  rw [k3Item_by, k5Item_by]

def unfilledBy (hd mH : Nat) (linksD links5 : List ModelPart) (M : More) (links : List ModelPart)
    (ps : List Place) : List (Nat × Pub) :=
  (askedAt M links ps).zipIdx.flatMap fun x =>
    (x.1.filter fun q => (whoFillsBy hd mH linksD links5 q).isNone).map fun q => (x.2, q)

def allFilledBy (hd mH : Nat) (linksD links5 : List ModelPart) (M : More) (links : List ModelPart)
    (ps : List Place) : Bool :=
  (askedAt M links ps).all fun Q => Q.all fun q => (whoFillsBy hd mH linksD links5 q).isSome

theorem unfilled_by (D : PubData) (M : More) (links : List ModelPart) (ps : List Place) :
    unfilled D M links ps = unfilledBy (hdOf D.d3.X) D.mH D.links D.d5.links M links ps := by
  unfold unfilled unfilledBy
  simp only [whoFills_by]

theorem allFilled_by (D : PubData) (M : More) (links : List ModelPart) (ps : List Place) :
    allFilled D M links ps = allFilledBy (hdOf D.d3.X) D.mH D.links D.d5.links M links ps := by
  unfold allFilled allFilledBy
  simp only [whoFills_by]

def worthNamedBy (hd : Nat) : Item → Bool
  | .worth m k r =>
    match k3SortBy hd m k with
    | some true => r == "planes" || r == "keys"
    | some false => r == "planes" || r == "keys" || r == "rider"
    | none => false
  | _ => true

theorem worthNamed_by (X : OnBytes.Model.Verify.Public) (i : Item) :
    worthNamed X i = worthNamedBy (hdOf X) i := by
  cases i <;> rfl

def worthFilledBy (hd : Nat) (links : List ModelPart) (ps : List Place) : Bool :=
  (openSets links ps (start links)).all fun O => O.all (worthNamedBy hd)

theorem worthFilled_by (X : OnBytes.Model.Verify.Public) (links : List ModelPart) (ps : List Place) :
    worthFilled X links ps = worthFilledBy (hdOf X) links ps := by
  unfold worthFilled worthFilledBy
  rw [show worthNamed X = worthNamedBy (hdOf X) from funext (worthNamed_by X)]

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.k3SortAt_by
#print axioms VerifiableInference.Desc.First.k3Item_by
#print axioms VerifiableInference.Desc.First.k5Item_by
#print axioms VerifiableInference.Desc.First.whoFills_by
#print axioms VerifiableInference.Desc.First.unfilled_by
#print axioms VerifiableInference.Desc.First.allFilled_by
#print axioms VerifiableInference.Desc.First.worthNamed_by
#print axioms VerifiableInference.Desc.First.worthFilled_by
