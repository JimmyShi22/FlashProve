-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BuiltLinksPlain.lean: THE SEGMENTS' RECORDS IN THE PROOF FILE's PUBLIC PART ARE
A FUNCTION OF ITS PUBLIC RECORD X: wherever the description's own way of computing the public part
returns Z (ProofFile.pureRoad.pub, Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean): linksPlain returns at Z.p.X, and
declareLinks returns at what it returns, with Z.p.built.links as its first part. General in the
three public files and in the letter for the format's second hash function. A joining of four laws of the
library.

What it is for. The table of steps reads Z.p.built.links at the opening, at the 23 switches and
behind each closing (TableOfSteps.lean). Where X is known (at the stored full-size files: the value
of Johnson/AtFull/Public/Join.lean) this law makes the segments' records a term in X.

  **built_links_plain**: by pub_planned and planned_chains
    (Johnson/Desc/ProofFile/Law/PlainMade.lean: the plain planner's builtOf returns Z.p.built) and
    buildLinksH_cut (Johnson/Road/K4/Rec/BuiltTests.lean: what it returns is declareLinks' first
    part).
  linksOfX X, **built_links_eq**: the same as one equation: Z.p.built.links = linksOfX Z.p.X, where
    linksOfX X is that first part, and no record where a routine refuses.
  builtOfX X, **ground_eq**: and of the ground G₀ that blankBy makes of Z on that road: G₀.built =
    builtOfX Z.p.X, G₀.W = Z.p.X, G₀.first = Z.first (blank_ground, Johnson/IMR/PureJoin.lean). Of
    its fourth field, cov, nothing is said.

Limits. From a return. Nothing says that any routine returns. Nothing on what the records hold.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Law.PlainMade
import Johnson.Road.K4.Rec.BuiltTests
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- **The segments' records are what declareLinks makes of linksPlain's.** -/
theorem built_links_plain {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∃ ls declared, ProofFile.Plain.linksPlain Z.p.X = .ok ls ∧
      declareLinks ls Z.p.X.NGr Z.p.X.p4 = .ok (Z.p.built.links, declared) := by
  have hb := (ProofFile.Law.planned_chains (ProofFile.Law.pub_planned h)).2.2
  unfold ProofFile.Plain.builtOf at hb
  obtain ⟨ls, h1, h2⟩ := OnBytes.Params.exc_bind hb
  obtain ⟨declared, h3, -⟩ := OnBytes.Road.K4.Rec.buildLinksH_cut h2
  exact ⟨ls, declared, h1, h3⟩

/-- The segments' records off the public record; none where a routine refuses. -/
def linksOfX (X : Verify.Public) : Array LinkH :=
  match ProofFile.Plain.linksPlain X with
  | .ok ls =>
    match declareLinks ls X.NGr X.p4 with
    | .ok y => y.1
    | .error _ => #[]
  | .error _ => #[]

/-- **The same as one equation.** -/
theorem built_links_eq {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) : Z.p.built.links = linksOfX Z.p.X := by
  obtain ⟨ls, declared, h1, h2⟩ := built_links_plain h
  unfold linksOfX
  rw [h1]
  dsimp only
  rw [h2]

/-- The ground's segments' records off the public record: the built ones, each with the routine of
linksPlain's record at its number (lettersBy's own line, Johnson/Desc/ProofFile/Pub.lean). It is the
empty array where a routine refuses; if the built records and linksPlain's are not as many, it is as
long as the shorter list. -/
def builtOfX (X : Verify.Public) : Array LinkH :=
  match ProofFile.Plain.linksPlain X with
  | .ok ls => (linksOfX X).zipWith (fun b l => { b with run := l.run }) ls
  | .error _ => #[]

/-- **The blank ground's three fields that the table reads, off the public record.** -/
theorem ground_eq {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    G₀.built = builtOfX Z.p.X ∧ G₀.W = Z.p.X ∧ G₀.first = Z.first := by
  obtain ⟨ls, h1, h2, h3, h4⟩ := IM.blank_ground hG
  refine ⟨?_, h2, h4⟩
  unfold builtOfX
  rw [h1, h3, ← built_links_eq h]
  rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.built_links_plain
#print axioms Johnson.AtFull.Shape.built_links_eq
#print axioms Johnson.AtFull.Shape.ground_eq
#print axioms Johnson.AtFull.Shape.linksOfX
#print axioms Johnson.AtFull.Shape.builtOfX
