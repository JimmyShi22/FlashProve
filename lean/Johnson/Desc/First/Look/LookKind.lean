-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/LookKind.lean: the public side of the kind «lookup» (K3) at a place of the
proof's first chain: its parameters, its rounds, its test on the plan, its guests. Definitions with
code; no theorem; nothing is evaluated in this file.

What it is for. A kind of block is a function from a place's public parameters to the block there
(Johnson/Desc/Block.lean: Kind, KindWithGuestIdentities). This file gives the lookup's parameters (P), how they are
made of the public record (placeAt, over lookAt), the shape that they fix (P.shape), the block's
rounds (P.rounds: the planner's own term for a lookup, by lookEntries of
Johnson/Desc/First/Look/LookRounds.lean, each entry as a declared round that opens nothing), what a
guest is (Guest) and the block's test on the plan (P.planOk). Its hearing and its claims are in
other files.

Limits. P.planOk asks the public tests of Johnson/Desc/First/Look/ShapeOwn.lean (shapeOwn, pubOk,
planesOk: the description's own text), the comparison that the verifier program makes in
Forest.paddingLaid (OnBytes/Model/Look.lean) and four clauses more. All three are proved to be
the program's, at every argument (ShapeOwnAgrees.lean, ShapeOwnAgrees2.lean; at the place:
LookKindAgrees.lean). It does not ask that the block's
rounds are the plan's entries: the file's description asks that of all blocks in a row. That the
first slot is the number at which the link's count of slots stands in front of the lookup is not
asked here. A guest's degrees are its kind's word: nothing here compares them with its form. The
count laid is the host's word: that it is the number of places which the host's key forms treat as
padding is the host's to show.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.LookAt
import Johnson.Desc.First.Look.LookRounds
import Johnson.Desc.First.Look.ShapeOwn
import Decl.Declared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- **The lookup's public parameters at a place**: numbers and public tables alone: no entry of the
plan, no declared round, no state. -/
structure P where
  name : String
  /-- the plan's setting: what the parameter file's lines fix -/
  set : Params.Setting
  /-- the link's number in the first chain, from 0 -/
  link : Nat
  /-- the lookup on the digits of the smallness test; else the one on the link's calls -/
  digits : Bool
  calls : Array Call
  /-- for each tree of the key side, how many of its places are padding -/
  pub : Array Nat
  /-- a cap on the logarithm of a tree's size -/
  lid : Nat
  /-- the number of the first scalar that the lookup's rounds send, among the link's -/
  first : Nat
  /-- how many scalars the link sends in all -/
  ns : Nat
  /-- the logarithm of the rows of the packed planes -/
  lm : Nat

/-- The parameters in a place's record: the two states and the plan's own shape are left out. -/
def P.ofPlace (set : Params.Setting) (digits : Bool) (x : Place) : P :=
  { name := x.name, set := set, link := x.link, digits := digits, calls := x.calls, pub := x.pub,
    lid := x.lid, first := x.F.next, ns := x.ns, lm := x.lm }

/-- **The parameters of link i's lookup, of the public record alone.** -/
def placeAt (X : Verify.Public) (i : Nat) (digits : Bool) : Option P :=
  (lookAt X i digits).map (P.ofPlace (Params.settingOf X.P.frame) digits)

/-- The shape that the parameters fix; none where the tests on the calls' numbers (`shapeOwn`) or on
the numbers of padding keys (`pubOk`) say no. -/
def P.shape (p : P) : Option Forest.Shape :=
  (shapeOwn p.calls p.lid).bind fun h0 =>
    if pubOk h0 p.pub then some { h0 with pub := p.pub } else none

/-- The plan's entries of the lookup's rounds; none where there is no shape or the planner refuses.
-/
def P.entries (p : P) : Option (List Fmt.Entry) := p.shape.bind (lookEntries p.set)

/-- **The lookup's rounds**, as declared rounds: no stored part and no tree is opened in them. Empty
where P.entries is none: P.planOk says no there. -/
def P.rounds (p : P) : List Fmt.DeclaredRound := (p.entries.getD []).map fun e => { entry := e }

/-- **A guest of the lookup**: another kind's identity that is tested at coordinates of the key
side's last point instead of at a point of its own. S: the carried record. Cl: the type of a claim.
The lookup is handed its guests before anything is heard, and calls form behind the last draw that
the guest borrows. -/
structure Guest (S Cl : Type) where
  name : String
  /-- pairs (i, k): the identity has degree k in the coordinate of bit i of a place's seat in its
  tree, the lowest bit being 0. These coordinates are drawn one a round, in the last key level's
  rounds; bit dT - 1 is that level's last draw -/
  coords : List (Nat × Nat)
  /-- what is tested, read off what was heard -/
  form : S → Option Cl

/-- Every bit that the guest names is a bit of a seat, and none is named twice. -/
def Guest.fits {S Cl : Type} (dT : Nat) (g : Guest S Cl) : Bool :=
  let bits := g.coords.map (·.1)
  bits.all fun i => decide (i < dT) && bits.count i == 1

/-- **The lookup's test on the plan**: no view, no record. The shape exists and the padding numbers
fit it; the planner makes the rounds; the planes' packing fits the shape; there are several calls,
so that the shift is drawn; the link has room for the lookup's scalars from the first slot on; the
host's count of padding places, tree by tree (laid), is the lookup's; every guest fits. -/
def P.planOk {S Cl : Type} (p : P) (laid : Array Nat) (guests : List (Guest S Cl)) : Bool :=
  match p.shape with
  | none => false
  | some h =>
    p.entries.isSome && planesOk h p.lm && decide (1 < h.NC) &&
      decide (p.first + Forest.elems h ≤ p.ns) && laid == p.pub && guests.all (Guest.fits h.dT)

end VerifiableInference.Desc.First.Look
