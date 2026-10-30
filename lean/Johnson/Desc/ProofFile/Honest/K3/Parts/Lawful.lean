-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Lawful.lean: the honest side of the kind "lookup" (K3): THE
STATEMENT that the specification's summands AT SEVERAL PARTS OF KEYS (Honest/K3/Parts/Jobs.lean)
meet `Lawful`, the premise on which every statement on values of Honest/K3/Law/Statements.lean is
conditional. Definitions with code, definitions of propositions. THE STATEMENT IS NOT PROVED IN THIS
FILE. It is none of the library's goals.

  `NumsShared f N`   the specification's public numbers that all parts share are the face's: rows,
                     planes, the orders on the table's side. The parts' sizes and orders are taken
                     from the face itself; that each order lists its level's variables comes
                     out of `Fit`
  `keysOfP A`        what part i's keys come to at a point: their extension at the translated point
  `SameForP`, `NumberedP R`   facts on the numbering of a course's challenges, at every part
  `SpecAtP R N w`    the course's summands are the specification's at parts; the input yields
                     one structure; the public factor, the table, the count of padding are the
                     face's; THE RELATION AFTER THE CHALLENGE AT PARTS HOLDS
  `LawfulSpecP`      the statement

Against Honest/K3/Law/SpecLawful.lean (one part): `SameFor`, `planesOf`, `cornerW` are taken from
there. `NumberedP` differs from `Numbered` in two clauses: `key` (every part) and `same`
(`SameForP`: at a parts' step theta and alpha too). No clause asks one part.

What is premise and who pays it. `NumberedP R` reads no summand and no input: it follows from
`Fit R` alone (Honest/K3/Parts/Numbered.lean). `SpecAtP`'s public clauses at a key file's lookup:
Honest/K3/Parts/KeyFace.lean and KeyAt.lean. `SpecAtP.mid` IS FOR THE FILES THAT STATE THE KEY
FILE'S HONEST PROVER: it is what a statement on that prover's trace concludes; it is
not stated here.

Limits. No course is shown here that meets the premises (one, by evaluation:
Honest/K3/Parts/Member.lean). Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.Jobs
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecLawful

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE)
open OnBytes.Model (orderDefault)
open ProofFile.Honest.K3.Law (Course Fit Lawful shapeAt)
open ProofFile.Honest.K3.Law.Spec (SameFor planesOf)

/-- **The public numbers that all parts share are the face's.** -/
structure NumsShared {P : Type} (f : LFace) (N : TwV.Nums P KE) : Prop where
  d : N.d = f.d
  w : N.w = f.mu
  planes : f.planes = N.n + 2
  oT : ∀ l, N.oT l = orderDefault (f.mu + l)
  oE : N.oE = orderDefault (f.mu + f.d)
  oB : N.oB = orderDefault (f.mu + f.d)

/-- **What part i's keys come to at a point** that is given as the verifier's text keeps it, the
highest variable first: their extension at the translated point. -/
def keysOfP {P : Type} (A : DataP P) (i : Nat) (z : Array E) : KE :=
  OnBytes.HonestTrace.Look.ext (A.part i).v (A.key i) (byBit z)

/-- Two structures of points agree in what a stage's job reads: at a parts' step theta and alpha
(the roots are made of both); elsewhere as at one part. -/
def SameForP (f : LFace) : Stage → Pts → Pts → Prop
  | .split _, p, q => p.theta = q.theta ∧ p.alpha = q.alpha
  | s, p, q => SameFor f s p q

/-- **Facts on the numbering of a course's challenges, at every part.** -/
structure NumberedP {W : Type} (R : Course W) : Prop where
  /-- what a stage's job reads of the challenges in front of it is what the whole
  run's points hold -/
  same : ∀ s ∈ stages R.f, SameForP R.f s (ptsOf R.f R.a.base (R.front s).heard) R.pts
  /-- a stage's sumcheck has a challenge for each variable, Y among them -/
  len : ∀ s ∈ stages R.f, (R.r s).length = (shapeAt R.a s).all.length
  /-- the point behind a key level of any part is made of that level's own challenges -/
  key : ∀ y ∈ R.f.parts.zipIdx, ∀ m, m < y.1 → R.pts.keyPt y.2 (m + 1) =
    behind m (R.f.orders y.2 m) ((R.r (.key y.2 m)).take m) (R.xiK y.2 m)
  /-- the like on the table's side -/
  tab : ∀ l, l < R.f.d → R.pts.tabPt (l + 1) =
    behind (R.f.mu + l) (orderDefault (R.f.mu + l)) ((R.r (.tab l)).take (R.f.mu + l)) (R.xiT l)
  /-- the two points that the claims on the planes read are the sumchecks' own challenges -/
  zb0 : R.zb0 = (R.r .leaves).toArray
  zb1 : R.zb1 = ((R.r .bits).take (R.f.mu + R.f.d)).toArray
  /-- a stage's second stretch has a mask entry for each end value -/
  masks : ∀ s ∈ stages R.f, (R.masks s).length = s.tail R.f

/-- **The course's summands are the specification's at parts, at shared numbers that are the face's,
and the relation after the challenge at parts holds.** w: the one structure of keys and bits that
the input yields at the challenges in front of every stage. -/
structure SpecAtP {P : Type} (R : Course Ask) (N : KE → TwV.Nums P KE) (w : Hidden) : Prop where
  J : R.J = (specJobsP N R.f.parts R.f.orders).asked
  /-- the input yields one structure at all the stages' fronts -/
  one : ∀ s ∈ stages R.f, R.t.input (R.front s).heard = w
  nums : NumsShared R.f (N (up R.pts.theta))
  /-- the public factor -/
  factor : up R.factor = (dataAt N w R.pts).a
  /-- the table, at the leaves' sumcheck's own point -/
  leaf : up (R.f.leaf R.pts.theta R.pts.alpha R.zb0) =
    ((List.range (2 ^ R.f.d)).map fun r => TwV.eqN ((byBit R.zb0).drop R.f.mu) r *
      (up R.pts.alpha - 1 - (N (up R.pts.theta)).tab r)).sum
  /-- as many keys are padding -/
  padding : ((N (up R.pts.theta)).pads.map (·.2)).sum = (R.f.padding.map (·.1)).sum
  /-- the relation after the challenge, at parts -/
  mid : (dataP N R.f.parts R.f.orders w R.pts).Mid

/-- **The statement: CONDITIONAL ON `Fit`, `NumberedP` AND `SpecAtP`, the specification's summands
at several parts are lawful**, at the planes' values of the structure's own bits and the extension
of each part's own keys. Not proved here; a lemma's statement, none of the library's goals. -/
def LawfulSpecP : Prop :=
  ∀ (P : Type) (N : KE → TwV.Nums P KE) (w : Hidden) (R : Course Ask),
    Fit R → NumberedP R → SpecAtP R N w →
      Lawful R (planesOf (dataAt N w R.pts)) (keysOfP (dataP N R.f.parts R.f.orders w R.pts))

end ProofFile.Honest.K3.Parts
