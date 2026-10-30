-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotPublic.lean: the honest side of the kind "lookup" (K3): further
tests on public data at a lookup's site (Honest/K3/Lot.lean), which theorems on the seated
sub-protocols and on the keys and bits take as hypotheses. Definitions with code, one named
hypothesis, one theorem. Nothing is evaluated in this file.

Terms. Honest/K3/GLOSSARY.md ("site", "shape", "slot", "step without a round").

What is defined and shown.
  `fsOf`: the shape that the plan itself holds for the lookup: the field fs of `First.Look.lookAt`.
  `ShapeIsFs`: the named hypothesis: the site's shape (made by `P.shape` of the place's calls) is
    that shape.
  `shapeIsFs`: the same as a test with code (`K3.sameShapeAll`: every field).
  `shapeIsFs_holds`: an acceptance by the test (`h`) gives the hypothesis (by `sameShapeAll_eq`,
    Johnson/Desc/First/Att/Door/ShapeSame.lean).
  `usedAt`: the plan's number of slots in use behind the digits' lookup, at a layers' or an
    attention link (the argument of `K3.quietAt`, Johnson/Desc/First/Look/K3Whole.lean: it writes
    out two arms of that text, by the site's caller and group; no lemma of this file ties the two).
  `publicTests` (`publicAll`, `askedAt`): the tests at one site, each with its name.
  `publicLines`: all sites' tests as lines for a print, with two alterations and the numbers of
    tests that each is due to make fail.

Who takes what as a hypothesis. `ShapeIsFs`: theorems on keys and bits are stated at the plan's own
shapes (X.y.fo, (X.A[g]).fs, X.HLy.fs, tl.f9), the row at the site's shape; the library has the same
hypothesis (`DigOK.shape`, Johnson/Desc/First/Look/K3Caller.lean). "The shape is the layout's": the
step without a round behind the lookup on the calls of a layers' link (`K3.quietLook`). "The planned
slots are taken": the step behind the lookup on the digits of a layers' or an attention link
(`K3.quietDigits`): the ledger's next slot behind the lookup is the place's first slot plus the
number of the lookup's slots. "One claim on the weights": the step behind the head's digits
(`K3.quietHead`), as far as it reads public data alone.

Limits. The tests are functions: they show something only where a program evaluates them at a public
part. That a plan's own maker always yields data that pass is not shown in this file. Shown in part,
under the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean), in two other files:
Johnson/AtFull/Shape/DigitsFree.lean (`used_at`): the test on the slots in use accepts at
every site on the digits of a link below 24; Johnson/AtFull/Shape/LookFree.lean (`shape_layers_at`):
at a site on the calls of a layers' link the site's shape is X.y.fo.
These two theorems speak of two of the
tests, and at the full size alone: that limit comes with `P5J.AtMgA`. The other tests of `quietHead`
read the state.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotSheet
import Johnson.Desc.First.Look.K3Borders
import Johnson.Desc.First.Att.Door.ShapeSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.Model (Verify.Public)
open OnBytes.Model.Forest (Shape)

/-- The shape that the plan itself holds for the lookup at a site. -/
def fsOf (X : OnBytes.Model.Verify.Public) (s : Site) : Option Shape :=
  (VerifiableInference.Desc.First.Look.lookAt X s.link s.digits).map (·.fs)

/-- **The named hypothesis: the site's shape is the shape that the plan itself holds for it.** -/
def ShapeIsFs (X : OnBytes.Model.Verify.Public) (s : Site) : Prop := fsOf X s = some s.shape

/-- The same as a test with code: every field. -/
def shapeIsFs (X : OnBytes.Model.Verify.Public) (s : Site) : Bool :=
  (fsOf X s).any fun fs => VerifiableInference.Desc.K3.sameShapeAll fs s.shape

/-- An acceptance by the test gives the hypothesis. -/
theorem shapeIsFs_holds (X : OnBytes.Model.Verify.Public) (s : Site) (h : shapeIsFs X s = true) :
    ShapeIsFs X s := by
  unfold shapeIsFs at h
  unfold ShapeIsFs
  cases hf : fsOf X s with
  | none => simp [hf] at h
  | some fs =>
    simp only [hf, Option.any_some] at h
    rw [H2K5.Door.sameShapeAll_eq h]

/-- The plan's number of slots in use behind the digits' lookup; nothing at the head. -/
def usedAt (X : OnBytes.Model.Verify.Public) (s : Site) : Option Nat :=
  match s.caller with
  | .layers => X.G[s.group]?.map (·.used)
  | .attention => X.A[s.group]?.map (·.nMsg)
  | .head => none

/-- **The tests at one site**, each with its name. A test that is not asked at a site accepts there.
-/
def publicTests (X : OnBytes.Model.Verify.Public) (s : Site) : List (String × Bool) :=
  [("the shape is the plan's own record of it, field by field", shapeIsFs X s),
   ("at a layers' link's calls: the shape is the layout's (seven numbers)",
      s.digits || s.caller != .layers ||
        VerifiableInference.Desc.First.Look.sameShape s.shape X.y.fo),
   ("at the digits, but for the head's: first slot + hidden values = the plan's slots in use",
      !s.digits || s.caller == .head || usedAt X s == some (s.p.first + s.at_.face.slots)),
   ("at the head's digits: the plan has one claim on the weights",
      !s.digits || s.caller != .head || X.H.NCL == 1)]

/-- The tests at a list of sites, each under its site's name. -/
def publicAll (X : OnBytes.Model.Verify.Public) (sites : List Site) : List (String × Bool) :=
  sites.flatMap fun s =>
    (publicTests X s).map fun t =>
      (s!"link {s.link}, " ++ (if s.digits then "digits" else "calls") ++ ": " ++ t.1, t.2)

/-- How many of the tests are asked at a site: the first at every site; each of the others at its
own sort of site. -/
def askedAt (s : Site) : Nat :=
  1 + (if !s.digits && s.caller == .layers then 1 else 0) + (if s.digits then 1 else 0)

/-- All sites' tests as lines: how many accept, and how many of them are asked at their site; those
that reject, by name; two alterations: every site's shape with one bit more in a tree's depth; every
site's first slot one more. -/
def publicLines (Z : Pub) : List String :=
  let sites := lookSites Z
  let ts := publicAll Z.p.X sites
  let deep := sites.map fun s => { s with shape := { s.shape with dT := s.shape.dT + 1 } }
  let later := sites.map fun s => { s with p := { s.p with first := s.p.first + 1 } }
  [s!"PUBLIC TESTS: yes {ts.length - (failing ts).length} of {ts.length}; asked at their site: " ++
     s!"{(sites.map askedAt).sum}"] ++
    (failing ts).map ("NO: " ++ ·) ++
  [bendLine "every site's shape: a tree one bit deeper"
     (sites.length + (sites.filter fun s => !s.digits && s.caller == .layers).length)
     (failing (publicAll Z.p.X deep)),
   bendLine "every site's first slot one more"
     (sites.filter fun s => s.digits && s.caller != .head).length
     (failing (publicAll Z.p.X later))] ++
  (lookSites Z).filterMap fun s =>
    if s.digits then
      some (s!"link {s.link}, digits: first slot {s.p.first} + hidden values {s.at_.face.slots}" ++
        s!" = {s.p.first + s.at_.face.slots}; the plan's slots in use: {usedAt Z.p.X s}")
    else none

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.shapeIsFs_holds
