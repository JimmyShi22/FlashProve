-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.AtFullPlain
import Johnson.Desc.K12.Law.Sizes.ShapesAtScope
/-
H2K12/ShapesAtSeats.lean: `ShapesFull`
(Johnson/Desc/K12/Law/Sizes/ShapesAtScope.lean) ON THE PLAIN ROAD, IN THE GOALS' SCOPE: at what
ProofFile's plain planner returns, at the record that its madeOf makes, and at the plain road's public
part: the seated description's own «made». An assembly: H2K12/AtFullPlain.lean's three steps with
`shapesFull_of_public` in `atFull_of_publicO`'s place.
  `shapes_of_plain`, `shapes_of_plainMade`, `shapes_in_scope`: two premises each: the files are in
    scope; the road's return.
What it is not: all that stands in ShapesAtScope.lean's head: IT SPEAKS OF THE PLAN's SHAPES AND THE
PLAN's CODES: that a record's message has the plan's shape and that a record's codes are the plan's
are two equations more, neither here. No soundness is claimed. Nothing on hiding.

-/
set_option autoImplicit false
namespace H2K.Sizes
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify

/-- On the plain road, at every o. -/
theorem shapes_of_plain {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) {lay : Option ByteArray} {p : Verify.Planned}
    (hp : ProofFile.Plain.planned o Z.pol Z.KL lay = .ok p) : ShapesFull p.chains.made := by
  obtain ⟨_, shapes, _, _, _, rl, _, hX, _, _, _, _, hc, _, _, _, he⟩ := H2K.Made.plain_parts hp
  exact shapesFull_of_public (publicO_at_scope hZ hX) hc he

/-- The same at the record that the plain madeOf makes. -/
theorem shapes_of_plainMade {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) {m : Johnson.G.OfPlan.Made}
    (hm : ProofFile.PlainG.madeOf o Z.pol Z.lay Z.KL = .ok m) : ShapesFull m.p.chains.made :=
  shapes_of_plain hZ (ProofFile.Law.madeOf_planned hm)

/-- **The same at the plain road's public part: the seated description's own «made».** -/
theorem shapes_in_scope {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) {Y : ProofFile.Pub}
    (hY : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Y) : ShapesFull Y.made.p.chains.made :=
  shapes_of_plainMade hZ (ProofFile.Law.pubBy_made
    (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts Z.pol Z.lay Z.KL = .ok Y from hY))

end H2K.Sizes

#print axioms H2K.Sizes.shapes_of_plain
#print axioms H2K.Sizes.shapes_of_plainMade
#print axioms H2K.Sizes.shapes_in_scope
