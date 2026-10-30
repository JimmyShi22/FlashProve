-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WideLines.lean: the declared widths of what the proof file's
three tests open of older trees, as closed numbers at the typed sizes, first by Lean's evaluator, then
by the kernel. It can say no.

  `shapeWords`   the words of each table that a sending's messages make: no row is read
  `tableWidth`   the width of the shared chain's own tree n, at the two sendings' tables at a plan
  `oldWidthsAt`, `wide_U`, `wide_U_bent`   every opening with an old source is own n, at that width:
                 at `piUFull`, three trees in front: yes; at widths bent by one: no
  `oldBelowAt`, `wide_O`, `wide_O_bent`   the same with n below 3: at `piOFull`, seven trees in front:
                 yes; at eight, own tree 7 would be old: no
  `oldOpens`, `old_W`, `old_W_bent`   what the last chain's test opens of older trees is just the
                 three taken trees of its first reading round: at `piWFull`, no own tree in front:
                 yes; at one own tree in front: no

Why. `RunPlays.old` (K12/PlaysK12.lean) asks that each old opening has a table of the declared width.
At the two shared tests these widths are public: a sending's table has the width of its messages'
shapes. The statements are of the form (realSized.all …) = true, which would be true for nothing if
realSized were none; it is not (real_members, Johnson/Desc/K1/Law/CondReal.lean).

Limits. Public numbers at the written places and the typed sizes. That a seated place's rounds are the
written ones: PlanAtSeat.lean. Of the trees that the last chain takes over, this file says which they
are and not what they hold: their widths are `widthsW` (K12/AtProof/JobW.lean), at the job, and their
tables are the thread's. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.ColsReturn
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K14.Sendings
import Johnson.Desc.ProofFile.Honest.K14.Thread2Full
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest.K14 (SendPub jobU jobOmega treesU)
open ProofFile.Honest.K12 (oldSrc)
open ProofFile.Honest.K12.Light (planOf)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K1 (realSized)
open H2K.Member (piUFull piOFull piWFull)

/-- The words of each table of a sending. -/
def shapeWords (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) : List Nat :=
  ((VerifiableInference.Desc.Own.treesMade codes sent).getD {}).shapes.toList.map fun t =>
    t.mainWidth + t.maskWidth

/-- The width of the shared chain's own tree n. -/
def tableWidth (A : SendPub) (n : Nat) : Nat :=
  if n < treesU A.P then
    (shapeWords (jobU A).Q.codes (jobU A).Q.sent).getD n 0
  else
    (shapeWords (jobOmega A).Q.codes (jobOmega A).Q.sent).getD (n - treesU A.P) 0

/-- Every opening of the place's rounds with an old source is own n, at the width f n. -/
def oldWidthsAt (p : P12) (f : Nat → Nat) (sent : Nat) : Bool :=
  (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.all fun d => d.opens.all fun o =>
    !oldSrc sent o.2 || match o.2 with
      | .own n => o.1.W == f n
      | .taken _ _ => false

/-- Every opening with an old source is own n below 3, at the width f n. -/
def oldBelowAt (p : P12) (f : Nat → Nat) (sent : Nat) : Bool :=
  (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.all fun d => d.opens.all fun o =>
    !oldSrc sent o.2 || match o.2 with
      | .own n => decide (n < 3) && o.1.W == f n
      | .taken _ _ => false

/-- The openings of the place's rounds with an old source, in order. -/
def oldOpens (p : P12) (sent : Nat) : List (Fmt.Shape × Fmt.TreeSource) :=
  ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.flatMap (·.opens)).filter fun o => oldSrc sent o.2

-- The widths, and what the rounds declare.
#eval realSized.map fun q => (List.range 3).map (tableWidth (planOf q.2 q.1.shape))
#eval ((proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).rounds.flatMap (·.opens)).map fun o => (o.2, o.1.W)
#eval ((proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).rounds.flatMap (·.opens)).map fun o => (o.2, o.1.W)
#eval ((proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds.flatMap (·.opens)).map fun o => (o.2, o.1.W)

-- Foretold: yes at the three lines. Controls: no.
#guard realSized.all fun q => oldWidthsAt piUFull (tableWidth (planOf q.2 q.1.shape)) 3
#guard realSized.all fun q => !oldWidthsAt piUFull (fun n => tableWidth (planOf q.2 q.1.shape) n + 1) 3
#guard realSized.all fun q => oldBelowAt piOFull (tableWidth (planOf q.2 q.1.shape)) 7
#guard realSized.all fun q => !oldBelowAt piOFull (tableWidth (planOf q.2 q.1.shape)) 8
#guard oldOpens piWFull 0 == piWFull.nums.first
#guard oldOpens piWFull 1 != piWFull.nums.first

theorem wide_U : (realSized.all fun q =>
    oldWidthsAt piUFull (tableWidth (planOf q.2 q.1.shape)) 3) = true := by decide +kernel

theorem wide_U_bent : (realSized.all fun q =>
    !oldWidthsAt piUFull (fun n => tableWidth (planOf q.2 q.1.shape) n + 1) 3) = true := by
  decide +kernel

theorem wide_O : (realSized.all fun q =>
    oldBelowAt piOFull (tableWidth (planOf q.2 q.1.shape)) 7) = true := by decide +kernel

theorem wide_O_bent : (realSized.all fun q =>
    !oldBelowAt piOFull (tableWidth (planOf q.2 q.1.shape)) 8) = true := by decide +kernel

theorem old_W : oldOpens piWFull 0 = piWFull.nums.first := by decide +kernel

theorem old_W_bent : oldOpens piWFull 1 ≠ piWFull.nums.first := by decide +kernel

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.tableWidth
#print axioms ProofFile.Honest.K12.AtFile.wide_U
#print axioms ProofFile.Honest.K12.AtFile.wide_U_bent
#print axioms ProofFile.Honest.K12.AtFile.wide_O
#print axioms ProofFile.Honest.K12.AtFile.wide_O_bent
#print axioms ProofFile.Honest.K12.AtFile.old_W
#print axioms ProofFile.Honest.K12.AtFile.old_W_bent
