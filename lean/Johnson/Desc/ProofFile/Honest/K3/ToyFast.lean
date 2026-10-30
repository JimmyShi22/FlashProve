-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/ToyFast.lean: the kind's row (Honest/K3/Row.lean), with the points
of Honest/K3/Heard.lean and the summands that fold tables (Honest/K3/JobsFast.lean), through the
test of Honest/K3/Toy.lean. Tests by evaluation (`#guard` lines) and the few definitions that they
need; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: the second writing is Honest/K3/ToyOwn.lean.

What is tested. Played by the frame's own functions and heard as the head of Honest/K3/Toy.lean
says, the row leaves 0 in all twelve claims; those alterations of Honest/K3/ToyGuards.lean that are
replayed here (section II.4: not all) make it fail; and its sent scalars are, round for round, those
of the second writing, whose summands go by another method: sums over all points. The points are
also compared with what the verifier's text has heard.

Imported, through Honest/K3/ToyGuards.lean. Files directly under Honest/.

Limits. Those of Honest/K3/Toy.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.ToyGuards
import Johnson.Desc.ProofFile.Honest.K3.Row
import Johnson.Desc.ProofFile.Honest.K3.Heard
import Johnson.Desc.ProofFile.Honest.K3.JobsFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Toy
open OnBytes (E addE subE mulE zeroE oneE)
open ProofFile.Honest.SumToy (e sig firsts turn)

/-- How the kind's row reads the run's points. -/
def reads : Reads := ⟨ptsOf, pointsAt⟩

/-- **The kind's row**, at the example's place. Here off is added to the true number of rounds in
front. -/
def rowIn (f : LFace) (J : LookJobs Hidden) (R : Reads := reads) (off : Nat := 0) : Row :=
  lookRow R J.asked { atOf f with base := baseOf f + off }

def F₁ : LookJobs Hidden := fastJobs f₁ rowAt
def F₂ : LookJobs Hidden := fastJobs f₂ rowAt

/-! ## II.1 The honest run -/

-- the table that the summands are handed is the face's own; the test fails at an altered row of the
-- table
#guard Fast.rowsFit f₁ rowAt (e 9) (e 5) && !Fast.rowsFit f₁ (fun t u => addE (rowAt t u) oneE)
  (e 9) (e 5)
-- all twelve claims are 0: three lists of challenges, two rows of coins, two orders
#guard (left f₁ (rowIn f₁ F₁) honest g₁ h₁).map (·.all.length) == some 12
#guard allZero (left f₁ (rowIn f₁ F₁) honest g₁ h₁)
#guard allZero (left f₁ (rowIn f₁ F₁) honest g₁ h₂)
#guard allZero (left f₁ (rowIn f₁ F₁) honest g₃ h₃)
#guard allZero (left f₂ (rowIn f₂ F₂) honest g₁ h₁)
#guard allZero (left f₂ (rowIn f₂ F₂) honest g₃ h₃)

/-! ## II.2 Against the second writing: equal sent scalars -/

-- row, points and summands all from the kind's files, against all from the second writing
#guard (run f₁ (rowIn f₁ F₁) honest g₁ h₁).isSome
#guard sig (run f₁ (rowIn f₁ F₁) honest g₁ h₁) == sig (run f₁ (rowOwn f₁ J₁) honest g₁ h₁)
#guard sig (run f₁ (rowIn f₁ F₁) honest g₃ h₃) == sig (run f₁ (rowOwn f₁ J₁) honest g₃ h₃)
#guard sig (run f₂ (rowIn f₂ F₂) honest g₃ h₃) == sig (run f₂ (rowOwn f₂ J₂) honest g₃ h₃)
-- piece by piece: the kind's row and points over the second writing's summands; the second
-- writing's row and points over the kind's summands
#guard sig (run f₂ (rowIn f₂ J₂) honest g₃ h₃) == sig (run f₂ (rowOwn f₂ J₂) honest g₃ h₃)
#guard sig (run f₂ (rowOwn f₂ F₂) honest g₃ h₃) == sig (run f₂ (rowOwn f₂ J₂) honest g₃ h₃)
-- on false data too the two writings send the same scalars, at these two data. (What is not sent,
-- each round's constant coefficient, is compared in Honest/K3/ToyWhole.lean [not in this library].)
#guard (run f₁ (rowIn f₁ F₁) badBit g₃ h₃).isSome && (run f₁ (rowIn f₁ F₁) badKey g₃ h₃).isSome
#guard sig (run f₁ (rowIn f₁ F₁) badBit g₃ h₃) == sig (run f₁ (rowOwn f₁ J₁) badBit g₃ h₃)
#guard sig (run f₁ (rowIn f₁ F₁) badKey g₃ h₃) == sig (run f₁ (rowOwn f₁ J₁) badKey g₃ h₃)

/-! ## II.2b The half as it is seated: by `Part.lift` -/

/-- A wider input, as a chain's halves are handed one: the data as a function of c, beside a number
that the lookup does not read. -/
structure Wide where
  idle : Nat
  data : Nat → Made

/-- The seated half's rounds: `proverSideOfLookupInChainAtOneOwner` with a wit that makes the small structure of
the wider input. -/
def runSeated (f : LFace) (J : LookJobs Hidden) (d : Nat → Made) (g : Nat → W3)
    (h : Nat → Nat → W3) : Option (List Fmt.RoundView) :=
  (playAll f (proverSideOfLookupInChainAtOneOwner (V₁ := Unit) (X₁ := Unit) reads J.asked (fun x : Wide => askOf x.data)
    (atOf f)).parts ⟨7, d⟩ g (drawsBy f h)).toOption.map (own f)

-- the seated half sends what the row sends, and all claims are 0; it would fail at a lift that
-- hands the part another input, other challenges or other stretches
#guard (runSeated f₁ F₁ honest g₃ h₃).isSome
#guard sig (runSeated f₁ F₁ honest g₃ h₃) == sig (run f₁ (rowIn f₁ F₁) honest g₃ h₃)
#guard (runSeated f₂ F₂ honest g₁ h₂).isSome &&
  sig (runSeated f₂ F₂ honest g₁ h₂) == sig (run f₂ (rowIn f₂ F₂) honest g₁ h₂)
#guard (runSeated f₁ F₁ honest g₃ h₃).any fun rs =>
  allZero (residues f₁ rs (maskOf g₃) (askOf honest (drawsBy f₁ h₃)))
-- it follows its input: other data, other scalars (no line asks that the run on `badKey` is played:
-- the `!=` would pass as well if it were not)
#guard sig (runSeated f₁ F₁ badKey g₃ h₃) != sig (runSeated f₁ F₁ honest g₃ h₃)

/-! ## II.3 The points against what the verifier's text has heard -/

/-- The points read off the whole list of challenges. -/
def ptsAll (f : LFace) (h : Nat → Nat → W3) : Pts := ptsOf f (baseOf f) (drawsBy f h)

-- theta, alpha; the key side's last point; the leaves' and the bits' challenges. It would fail at a
-- wrong number of a round, or at a point that is not reversed or not put back by the order
#guard (left f₂ (rowIn f₂ F₂) honest g₃ h₃).any fun x =>
  x.heard.theta == (ptsAll f₂ h₃).theta && x.heard.alpha == (ptsAll f₂ h₃).alpha &&
  x.heard.keys.map (·.1) == [(ptsAll f₂ h₃).keyPt 0 3] &&
  x.heard.zb0 == leavesR f₂ (baseOf f₂) (drawsBy f₂ h₃) &&
  x.heard.zb1 == bitsR f₂ (baseOf f₂) (drawsBy f₂ h₃)
-- the leaves' variables as the text heard them are summed at the kind's points
#guard (left f₂ (rowIn f₂ F₂) honest g₃ h₃).any fun x =>
  pointsOfVars x.heard.leaves.vars == pointsAt f₂ .leaves (ptsAll f₂ h₃)

/-! ## II.4 The alterations -/

#guard notZero (left f₁ (rowIn f₁ F₁) badKey g₁ h₁) == some [0]
#guard notZero (left f₁ (rowIn f₁ F₁) badCount g₁ h₁) == some [0, 10]
#guard notZero (left f₁ (rowIn f₁ F₁) badBit g₁ h₁) == some [0, 7, 10]
-- a wrong number of rounds in front
#guard someNot (left f₁ (rowIn f₁ F₁ reads 1) honest g₁ h₁)
-- a point that is not reversed: that of "JOIN"; that of "ZERO"
#guard someNot (left f₁ (rowIn f₁ F₁ ⟨fun f b l =>
  { ptsOf f b l with rhoT := (ptsOf f b l).rhoT.reverse
                     tabPt := fun k => if k == 0 then (ptsOf f b l).rhoT.reverse
                                       else (ptsOf f b l).tabPt k }, pointsAt⟩) honest g₁ h₁)
#guard someNot (left f₁ (rowIn f₁ F₁ ⟨fun f b l =>
  { ptsOf f b l with zeroPt := (ptsOf f b l).zeroPt.reverse }, pointsAt⟩) honest g₁ h₁)
-- one order's summands under the other order's text
#guard someNot (left f₂ (rowIn f₂ F₁) honest g₁ h₁)
-- each of the 73 coins, changed in the evaluation; each of the 73 sent scalars
#guard (run f₁ (rowIn f₁ F₁) honest g₁ h₁).any fun rs => (List.range f₁.slots).all fun j =>
  someNot (residues f₁ rs (maskOf fun i => if i == first + j then ((g₁ i).1 + 1, 0, 0) else g₁ i)
    (askOf honest (drawsBy f₁ h₁)))
#guard (run f₁ (rowIn f₁ F₁) honest g₁ h₁).any fun rs =>
  rs.zipIdx.all fun r => (List.range r.1.vals.length).all fun j =>
    someNot (residues f₁ (turn rs r.2 j) (maskOf g₁) (askOf honest (drawsBy f₁ h₁)))

/-! ## II.5 The kind's list of stretches against the example's book -/

-- name, first entry and count of every stretch are those of the book's entries, which
-- Honest/K3/Toy.lean counts off the verifier's calls; it would fail at a moved stretch or an
-- altered name
#guard (stretches (atOf f₁) first).map (fun t => (t.name, t.first, t.count)) ==
  (bookOf f₁).ahead.map fun a => (a.name, a.start.e, a.count.e)

end ProofFile.Honest.K3.Toy
