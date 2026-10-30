-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Toy.lean: the lookup's honest row, played whole at a small size and
heard by `hearV`, the text that the seated hearing calls (Johnson/Desc/First/Look/Via/Rounds.lean);
the three claims on the planes are made by `planesV` of the same file, which no seated sub-protocol
calls. This file is the harness: definitions with code; a few tests by evaluation on its own
numbers; no theorem. The tests on rows and fillings stand in Honest/K3/ToyGuards.lean, the print in
Honest/K3/ToyPrint.lean [not in this library].

Terms. Honest/K3/GLOSSARY.md. In this file: the example is the small synthetic lookup of section 1;
the small chain is the synthetic chain of section 2.

What is defined.
  1 A small lookup: 8 places for keys, one of them padding; a table of 4 rows; counts of 3 bits in 4
    places for bits (one plane is not real). There is a shift: keys and rows have two columns, and
    the joint value is the first plus the shift times the second, so keys, rows, the padding's key
    and the public factor all depend on a challenge. Which rows the keys hold depends on a challenge
    that is sampled in front of the lookup. The face is given at any order of the key tree's rounds.
  2 A small chain of two sub-protocols: two rounds of another place in front, then the lookup's
    rounds, which are those of `entriesV`; the second sub-protocol decides by `hearV`.
  3 A book written in this file: one owner, the mask row, whose coin number j stands under the
    ledger's slot j; for each masked sumcheck of the row two entries, counted off the verifier's
    calls; the cut is that of Honest/BookOf.lean, from the rounds' names.
  4 The play: the frame's own `chainSteps` (which compares the row's cut and counts with the book)
    and `play` (Honest/Frame.lean).
  5 What is tested. The hearing tests no equation: it leaves claims. `residues` evaluates every one
    of them on the ledger that the text leaves and on the played coins (the value under a slot is
    what was shown less the factor times the mask entry): the rows that read hidden values alone;
    the three claims on the planes, with the planes read from the example's own bits; the key side's
    last form against alpha - key at the key side's last point. All are 0 at an honest run.

Imported. Files directly under Honest/.

Limits. The three claims on the planes are those of `planesV`. In the description they are made in
another way: of the verifier program's structure, by `planeClaimsOwn`
(Johnson/Desc/First/Look/LookPlanesOwn.lean). That the two ways make the same claims is shown by
no theorem here; Honest/K3/ToySeated.lean [not in this library; so here read: not tested in this
library] goes both at one run and finds the
same values. Shown in part: `seated_same_worth` (Honest/K3/Law/SeatedWorth.lean) shows that the
three claims of the two ways have the same worth in a world, at a face `faceOf h`, conditional on
three hypotheses: `toHeard` returns; the shape lists every tree's count of padding keys; and
`ReadersSay`, on the calling kind's readers in that world, of which no instance is exhibited there.
It is the same worth, not the same claims; and by that file's limits the claims on the planes at a
layers' link are not reached. One size. The small chain's second sub-protocol is this file's own
thin wrapper of `hearV` with the rounds of `entriesV`, not a member of the real description; no
planner is asked. The ledger in front is written by hand: four slots are counted as taken, none of
them is filled. The book is synthetic: it is not made by the real book's maker. Evaluations at fixed
coins and challenges.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.ToyOwn
import Johnson.Desc.ProofFile.Honest.BookOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Toy
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Aff Fork orderDefault)
open OnBytes.Slice (toE)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.K3 (hearV planesV entriesV HeardV PlaneClaim drawEntry)
open ProofFile.Honest.SumToy (e formAt)

/-! ## 1 A small lookup -/

/-- The table's two columns: four rows. -/
def tabA : List UInt64 := [3, 8, 21, 34]
def tabB : List UInt64 := [5, 1, 9, 2]

/-- The table's row u, of the shift. -/
def rowAt (theta : E) (u : Nat) : E := addE (e (tabA.getD u 0)) (mulE theta (e (tabB.getD u 0)))

/-- The public key at a place of padding, of the shift: the table's row 1. -/
def padKey (theta : E) : E := rowAt theta 1

/-- The table's row at a point: z1 belongs to the higher bit of the row's number. -/
def rowExt (theta z1 z0 : E) : E :=
  ext 2 (rowAt theta) fun b => if b == 1 then z1 else z0

/-- **The face.** orders: of the key tree's level with m variables: the bit that
each round fixes. -/
def face (orders : Nat → List Nat) : LFace :=
  { shifted := true, mu := 2, planes := 3, parts := [3], d := 2
    orders := fun _ => orders
    padding := [(1, padKey)]
    leaf := fun theta alpha zb0 =>
      subE (subE alpha oneE) (rowExt theta (zb0.getD 0 zeroE) (zb0.getD 1 zeroE)) }

/-- Two orders: the highest bit first; the lowest bit first. -/
def f₁ : LFace := face orderDefault
def f₂ : LFace := face List.range

/-- What the prover holds: for each place its key, of the shift; the counts' bits (row, plane). -/
structure Made where
  keys : List (E → E)
  bit : Nat → Nat → E

def Made.hidden (d : Made) : Hidden := ⟨fun th _ x => (d.keys.getD x fun _ => zeroE) th, d.bit⟩

/-- The bits of written counts. -/
def bitsOf (counts : List Nat) (u j : Nat) : E := if (counts.getD u 0).testBit j then oneE else
    zeroE

/-- **The honest data**, of a number c: seven keys, each a row of the table (the rows 2 0 0 3 2 0 .
2, each moved on by c, around the table), padding at place 6; so the rows c, c + 1, c + 2, c + 3 are
met 3, 0, 3 and 1 times. -/
def honest (c : Nat) : Made :=
  { keys := [2, 0, 0, 3, 2, 0].map (fun r => (rowAt · ((r + c) % 4))) ++
      [padKey, (rowAt · ((2 + c) % 4))]
    bit := bitsOf ((List.range 4).map fun u => [3, 0, 3, 1].getD ((u + 4 - c % 4) % 4) 0) }

/-- **What the row is seated at**: the data depend on a challenge in front of the lookup: c is the
first word of the first challenge heard. Here d is the data, as a function of c. -/
def askOf (d : Nat → Made) : Ask := fun heard =>
  (d (((heard.head?.bind (·.elems.head?)).map (·.1.toNat)).getD 0)).hidden

/-! ## 2 A small chain -/

/-- The owner's place, in front; the lookup's place. -/
def pM : Place := ⟨1, some 0, 0, .K1⟩
def pL : Place := ⟨1, some 0, 2, .K3⟩
def aM : Addr := ⟨pM, 0⟩

/-- How many slots of the ledger are counted as taken in front of the lookup. -/
def first : Nat := 4

/-- The ledger's room: the slots in front, the lookup's, three more. -/
def room (f : LFace) : Nat := first + f.slots + 3

/-- The ledger in front of the lookup, written by hand. -/
def ledger (f : LFace) : Fork := { (({} : Fork).slots (room f)) with next := first }

/-- What the small chain's structure holds: the ledger, and what was heard. -/
abbrev St : Type := Fork × Option HeardV

/-- Two rounds of another place, in which nothing is sent and one element is sampled. No half stands
there. -/
def frontBlock : Block St Unit :=
  { name := "front", place := pM, planOk := true
    rounds := [{ entry := drawEntry "BAT-sigma" 1 }, { entry := drawEntry "BAT-sigma" 1 }]
    oracles := [[], []], before := [], decide := fun s _ _ => .ok s, claims := [], after := [] }

/-- The lookup's rounds, by `entriesV`; the decision, by `hearV`. -/
def lookBlock (f : LFace) : Block St Unit :=
  { name := "lookup", place := pL, planOk := true
    rounds := (entriesV f).map fun x => { entry := x }
    oracles := (entriesV f).map fun _ => []
    before := []
    decide := fun s rs _ =>
      match hearV f s.1 rs with
      | some x => .ok (x.2, some x.1)
      | none => .error "the hearing"
    claims := [], after := [] }

def blocks (f : LFace) : List (Block St Unit) := [frontBlock, lookBlock f]

/-- How many rounds stand in front of the lookup: read off the chain. -/
def baseOf (f : LFace) : Nat := (roundsInFront (blocks f) pL).getD 0

def atOf (f : LFace) : At := ⟨pL, f, baseOf f⟩

/-! ## 3 The book -/

/-- The entries: stage by stage, in the ledger's order: the sumcheck's own slots (the hiding
polynomial's coefficients), then its end values'. off: the slot of the stage's first scalar. -/
def aheadFrom (f : LFace) : List (Stage × Nat) → Nat → List Ahead
  | [], _ => []
  | x :: l, off =>
    match x.1.call f with
    | none => aheadFrom f l off
    | some k =>
      let n := (k.ends.map (·.n)).getD 0
      [(⟨runName maskRowRun ⟨pL, x.2⟩ "sum", aM, ⟨0, off⟩, ⟨0, ownRun k⟩, ⟨pL, x.2⟩, true⟩ : Ahead)]
        ++
        (if n == 0 then [] else
          [⟨runName maskRowRun ⟨pL, x.2⟩ "ends", aM, ⟨0, off + ownRun k⟩, ⟨0, n⟩, ⟨pL, x.2⟩, true⟩])
            ++
        aheadFrom f l (off + ownRun k + n)

/-- **The book**: one owner, with a coin for each slot of the ledger. -/
abbrev bookOf (f : LFace) : ProverCoinCounts :=
  { first := [(aM, ⟨0, room f⟩)], shared := [], second := []
    ahead := aheadFrom f (stages f).zipIdx first
    cuts := cutsIn (blocks f) }

/-- Coins by a formula: the owner's coin number j, by its three coordinates. -/
def csOf (n : Nat) (g : Nat → UInt64 × UInt64 × UInt64) : Cs ⟨0, n⟩ :=
  ⟨fun i => i.elim0, fun i => toE (g i.val)⟩

def coinsOf (f : LFace) (g : Nat → UInt64 × UInt64 × UInt64) : Coins (bookOf f) :=
  ⟨(csOf (room f) g, ()), (), ()⟩

/-- The mask entry under a slot. -/
def maskOf (g : Nat → UInt64 × UInt64 × UInt64) (j : Nat) : E := E.ofTriple (g j)

/-! ## 4 The play -/

/-- **The chain played**: the row at the lookup's place; the rounds as a view shows them, the two in
front among them; or the rejection's words. No columns are handed: the play starts at
`opened := none`. -/
def playAll {W : Type} (f : LFace) (row : List (Part Unit W Unit)) (w : W)
    (g : Nat → UInt64 × UInt64 × UInt64) (ds : List Fmt.Drawn) : Except String (List Fmt.RoundView) :=
  (chainSteps (bookOf f) ((bookOf f).rowsOf 0) ((coinsOf f g).look 0) (some ()) (blocks f)
    [⟨pL, row⟩]).bind fun steps =>
  match play steps ds [] ⟨⟨w, [], ()⟩, [], [], none⟩ with
  | .ok y => .ok (roundsOf y.1)
  | .error x => .error x.print

/-- The lookup's own rounds of a played chain. -/
def own (f : LFace) (rs : List Fmt.RoundView) : List Fmt.RoundView := rs.drop (baseOf f)

/-! ## 5 What is tested -/

/-- The vector of product form with these pairs, the lowest variable first, at the number x. -/
def prodAt (pairs : List (E × E)) (x : Nat) : E :=
  pairs.zipIdx.foldl (fun w p => mulE w (if x.testBit p.2 then p.1.2 else p.1.1)) oneE

/-- A claim on the planes, evaluated: lead + scalar <v, the bits>. -/
def planeAt (f : LFace) (G : Fork) (m : Nat → E) (w : Hidden) (c : PlaneClaim) : E :=
  addE (formAt G m c.lead) (mulE c.scalar
    ((List.range (2 ^ (f.mu + f.d))).foldl
      (fun s x => addE s (mulE (prodAt c.pairs x) (bitTab f w x))) zeroE))

/-- What the verifier's text leaves, evaluated. -/
structure Left where
  heard : HeardV
  /-- the claims that read hidden values alone -/
  rows : List E
  /-- the three claims on the planes -/
  planes : List E
  /-- for each part of keys: the last form, less alpha - key at the last point -/
  keys : List E

def Left.all (x : Left) : List E := x.rows ++ x.planes ++ x.keys

/-- **The hearing and the claims' values.** Here rs is the lookup's own rounds, m the mask entries
by slot, and w the data on which the claims are read. Nothing where the verifier's text rejects. -/
def residues (f : LFace) (rs : List Fmt.RoundView) (m : Nat → E) (w : Hidden) : Option Left :=
  (hearV f (ledger f) rs).bind fun x =>
  (planesV f x.1 x.2).map fun y =>
    let p : Pts := { theta := x.1.theta, alpha := x.1.alpha, rhoT := #[], keyPt := fun _ _ => #[]
                     tabPt := fun _ => #[], zeroPt := #[], heard := [] }
    { heard := x.1
      rows := x.1.rows.toList.map (formAt y.2 m)
      planes := y.1.map (planeAt f y.2 m w)
      keys := x.1.keys.zipIdx.map fun k =>
        subE (formAt y.2 m k.1.2)
          (ext (f.parts.getD k.2 0) (keyLeaf w p k.2) (coord (f.parts.getD k.2 0) k.1.1)) }

/-- All claims are 0. -/
def allZero (x : Option Left) : Bool := x.any fun l => l.all.all (· == zeroE)

/-- The text returns, and some claim is not 0. -/
def someNot (x : Option Left) : Bool := x.any fun l => l.all.any (· != zeroE)

/-- The numbers, from 0, of the claims that are not 0. -/
def notZero (x : Option Left) : Option (List Nat) :=
  x.map fun l => (l.all.zipIdx.filter fun r => r.1 != zeroE).map (·.2)

/-! ## Tests on the harness's own numbers -/

-- the faces pass the verifier's tests on the numbers; the test fails at an order that is no
-- permutation
#guard f₁.ok && f₂.ok && !(face fun _ => [0]).ok
-- 73 slots, 8 rows that read hidden values alone, 50 rounds, written out; it would fail at another
-- size
#guard f₁.slots == 73 && f₁.lins == 8 && (entriesV f₁).length == 50
-- the honest data is honest, at each c: a row's count, read off its bits, is the number of places
-- that hold the row, the padding's place not counted; it would fail at an altered count or key
#guard (List.range 6).all fun c => (List.range 4).all fun u =>
  (((honest c).keys.zipIdx.filter fun k => k.2 != 6 && k.1 (e 9) == rowAt (e 9) u).length ==
    ((List.range 3).map fun j => if (honest c).bit u j == oneE then 2 ^ j else 0).sum)
-- the place, the cut and the challenges' numbers, against the small chain's sub-protocols (this
-- file's own, made of `entriesV`; against the real description's sub-protocols the lot's files
-- compare them): two rounds stand in front; the stages' rounds are the cut that Honest/BookOf.lean
-- makes of the rounds' names; it would fail if a stage's rounds were counted otherwise than the
-- verifier's entries run
#guard roundsInFront (blocks f₁) pL == some 2
#guard (stages f₁).map (Stage.rounds f₁) == partsCut (lookBlock f₁)
#guard partsCutFits (lookBlock f₁)
-- the book's entries fill the lookup's slots, one after the other, and no more
#guard ((bookOf f₁).ahead.map (·.count.e)).sum == f₁.slots
#guard ((bookOf f₁).ahead.foldl (fun (s : Option Nat) a =>
  s.bind fun n => if a.start.e == n then some (n + a.count.e) else none) (some first)) ==
    some (first + f₁.slots)

end ProofFile.Honest.K3.Toy
