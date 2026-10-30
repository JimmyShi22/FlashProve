-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SpecLawful.lean: the honest side of the kind "lookup" (K3). The
statement that the specification's summands (Honest/K3/JobsSpec.lean) meet `Lawful`, the hypothesis
on which every statement on values of Honest/K3/Law/Statements.lean is conditional. Definitions with
code, definitions of propositions. The statement is not proved in this file: `lawfulSpec`
(Honest/K3/Law/SpecProof.lean) proves it. It is none of the library's goals.

Terms. Honest/K3/GLOSSARY.md ("course", "lawful", "relation after the challenge", "specification").
`up` (JobsSpec.lean) and `rd` (Statements.lean) are one function: an element of the program, read in
the library's field.

What is defined.
  `NumsAre f N`: the specification's public numbers are the face's: one part of keys; the planes
    that count lie among the 2 ^ mu; the orders are those by which the verifier's text goes.
  `cornerW`, `planesOf D`: what the planes come to under a product form: the sum over all leaves
    (row u, plane j; number u 2 ^ w + j) of the form's value at the leaf's corner times the bit
    there.
  `keysOf D`: what the keys come to at a point: their extension at the translated point.
  `SameFor`, `Numbered R`: facts on the numbering of challenges alone: what a stage's job reads of
    the challenges in front of the stage is what the whole run's points hold; the points behind a
    level are made of that level's own challenges; lengths.
  `SpecAt R N w`: the course's summands are the specification's at N, asked as a row is seated; the
    input yields the one structure w at every stage's front; N's numbers are the face's; the public
    factor, the table and the count of padding are the face's; the relation after the challenge
    holds of the input's keys and bits.
  `LawfulSpec`: the statement.

Hypotheses that remain, in `LawfulSpec`, and where each may be shown.
  `Fit R`.
  `Numbered R` reads no summand and no input: it follows from `Fit R`
    (Honest/K3/Law/NumberedOfFit.lean at one part; at any number of parts
    Honest/K3/Parts/Corollaries.lean);
    it is not shown here.
  `SpecAt`: that the input yields one structure is the caller's to show (on a link's calls the
    function is constant). At a proof file's lookup the orders are shown in JobsSpec.lean
    (`numsF_oK` and its like), factor and table in Honest/K3/JobsSpecTies.lean (both conditional on
    `FoNums.ok h`). The relation after the challenge is what Johnson/HonestTrace/CountsLaw.lean and
    its kin conclude of a trace.

Users. This file is imported by Honest/K3/Law/SpecCourse.lean and Honest/K3/Law/SpecPlanes.lean.

Limits. One part of keys. No course is shown here that meets the three hypotheses. Nothing is said
of a course whose summands fold tables.
An instance: Honest/K3/Law/SpecMember.lean (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Statements
import Johnson.Desc.ProofFile.Honest.K3.JobsSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE oneE)
open OnBytes.Model (orderDefault)
open OnBytes.HonestTrace.Look (Data)

/-- **The specification's public numbers are the face's.** -/
structure NumsAre {P : Type} (f : LFace) (N : TwV.Nums P KE) : Prop where
  parts : f.parts = [N.v' + 1]
  d : N.d = f.d
  w : N.w = f.mu
  planes : f.planes = N.n + 2
  room : N.n + 2 ≤ 2 ^ N.w
  oK : ∀ l, N.oK l = f.orders 0 l
  /-- each level's order of the key tree lists that level's variables, each once -/
  permK : ∀ l, l < N.v' + 1 → (N.oK l).Perm (List.range l)
  oT : ∀ l, N.oT l = orderDefault (f.mu + l)
  oE : N.oE = orderDefault (f.mu + f.d)
  oB : N.oB = orderDefault (f.mu + f.d)

/-- The value of a product form at corner X: one pair for each variable, the lowest variable first:
the pair's first component where the variable's bit of X is 0, its second where it is 1. -/
def cornerW : List (E × E) → Nat → KE
  | [], _ => 1
  | p :: l, X => (if X % 2 = 1 then up p.2 else up p.1) * cornerW l (X / 2)

/-- **What the planes of the counts' bits come to under a product form.** -/
def planesOf {P : Type} (D : Data P KE) (pairs : List (E × E)) : KE :=
  ∑ X ∈ Finset.range (2 ^ (D.N.w + D.N.d)), cornerW pairs X * D.bitAt X

/-- **What the keys come to at a point** that is given as the verifier's text keeps it, the
highest variable first: their extension at the translated point. There is one part. -/
def keysOf {P : Type} (D : Data P KE) (_ : Nat) (z : Array E) : KE :=
  OnBytes.HonestTrace.Look.ext D.v D.key (byBit z)

/-- Two structures of points agree in what a stage's job reads. Written for one part of keys: at a
parts' step, as at every stage that is not named, it says nothing. -/
def SameFor (f : LFace) : Stage → Pts → Pts → Prop
  | .tie _, p, q => p.theta = q.theta ∧ p.alpha = q.alpha
  | .key i m, p, q => p.theta = q.theta ∧ p.alpha = q.alpha ∧ p.keyPt i m = q.keyPt i m
  | .tab l, p, q => p.theta = q.theta ∧ p.alpha = q.alpha ∧ p.tabPt l = q.tabPt l
  | .leaves, p, q => p.theta = q.theta ∧ p.alpha = q.alpha ∧ p.tabPt f.d = q.tabPt f.d
  | .bits, p, q => p.theta = q.theta ∧ p.alpha = q.alpha ∧ p.zeroPt = q.zeroPt
  | _, _, _ => True

/-- **Facts on the numbering of a course's challenges.** -/
structure Numbered {W : Type} (R : Course W) : Prop where
  /-- what a stage's job reads of the challenges in front of it is what the whole
  run's points hold -/
  same : ∀ s ∈ stages R.f, SameFor R.f s (ptsOf R.f R.a.base (R.front s).heard) R.pts
  /-- a stage's sumcheck has a challenge for each variable, Y among them -/
  len : ∀ s ∈ stages R.f, (R.r s).length = (shapeAt R.a s).all.length
  /-- the point behind a key level is made of that level's own challenges -/
  key : ∀ m, m < R.f.parts.headD 0 → R.pts.keyPt 0 (m + 1) =
    behind m (R.f.orders 0 m) ((R.r (.key 0 m)).take m) (R.xiK 0 m)
  /-- the like on the table's side -/
  tab : ∀ l, l < R.f.d → R.pts.tabPt (l + 1) =
    behind (R.f.mu + l) (orderDefault (R.f.mu + l)) ((R.r (.tab l)).take (R.f.mu + l)) (R.xiT l)
  /-- the two points that the claims on the planes read are the sumchecks' own challenges -/
  zb0 : R.zb0 = (R.r .leaves).toArray
  zb1 : R.zb1 = ((R.r .bits).take (R.f.mu + R.f.d)).toArray
  /-- a stage's second stretch has a mask entry for each end value -/
  masks : ∀ s ∈ stages R.f, (R.masks s).length = s.tail R.f

/-- **The course's summands are the specification's, at public numbers that are the face's, and the
relation after the challenge holds.** w: the one structure of keys and bits that the input yields at
the challenges in front of every stage. -/
structure SpecAt {P : Type} (R : Course Ask) (N : KE → TwV.Nums P KE) (w : Hidden) : Prop where
  J : R.J = (specJobs N).asked
  /-- the input yields one structure at all the stages' fronts -/
  one : ∀ s ∈ stages R.f, R.t.input (R.front s).heard = w
  nums : NumsAre R.f (N (up R.pts.theta))
  /-- the public factor -/
  factor : up R.factor = (dataAt N w R.pts).a
  /-- the table, at the leaves' sumcheck's own point -/
  leaf : up (R.f.leaf R.pts.theta R.pts.alpha R.zb0) =
    ((List.range (2 ^ R.f.d)).map fun r => TwV.eqN ((byBit R.zb0).drop R.f.mu) r *
      (up R.pts.alpha - 1 - (N (up R.pts.theta)).tab r)).sum
  /-- as many keys are padding -/
  padding : ((N (up R.pts.theta)).pads.map (·.2)).sum = (R.f.padding.map (·.1)).sum
  /-- the relation after the challenge -/
  mid : (dataAt N w R.pts).Mid

/-- **The statement: conditional on `Fit`, `Numbered` and `SpecAt`, the specification's summands are
lawful**, at the planes' values of the structure's own bits and the extension of the structure's own
keys. Not proved here; a lemma's statement, none of the library's goals. -/
def LawfulSpec : Prop :=
  ∀ (P : Type) (N : KE → TwV.Nums P KE) (w : Hidden) (R : Course Ask),
    Fit R → Numbered R → SpecAt R N w →
      Lawful R (planesOf (dataAt N w R.pts)) (keysOf (dataAt N w R.pts))

end ProofFile.Honest.K3.Law.Spec
