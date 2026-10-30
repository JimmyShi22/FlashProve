-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5RowTwins.lean: kind K5's lot, forward: TWO TWINS BY FIELD, EACH WITH
ITS LAW "twin = the lot's own text": what the third conjunct of the test on the plan (claimsOkAtO,
Johnson/Desc/First/Att/SeatO.lean) reads of a plan, and what "before" (H2K5.k5Before?,
Johnson/Desc/ProofFile/Lot/K5.lean) reads of the public part. General laws: at every plan, every Z.
NOTHING IS EVALUATED; NO WRITTEN VALUE IS NAMED.

Main names (namespace H2K5.Row):
  claimsBy geo iU3 nW K mats fs: claimsOk at these letters. **claimsOkAtO_by**:
    claimsOkAtO p = claimsBy (geoOf p.S) p.iU3 p.nW
    ‹the planned array's columns, 0 where there is none› ‹the matrices' rows and columns› p.fs: by
    unfolding.
  roundsBy | rootsBy | beforeBy cuts rb nm: the lot's texts at the cuts' pairs (look, take) and at a
    function "the roots in front of a round". **k5Before_by**:
    k5Before? Z nm = beforeBy ‹Z.cuts' pairs› ‹Z.D.1's roots› nm.
claimsBy AS IT STANDS HAS BEEN PUT TO NO KERNEL: its road reaches Lean's List.mergeSort
(claimsOk → dryOk → blankPts → pointsOf → piecesOf, Johnson/Desc/First/Att/Points.lean), which was
seen to stop the kernel at other call sites. Its twin, with the equation:
Johnson/Desc/First/Att/Row/K5DryTwin.lean.
IS IT EMPTY HERE? Equations at letters: nothing to meet.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Lot.K5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P

/-- The claims' tests on the plan alone, at what they read. -/
def claimsBy (geo : Geo) (iU3 nW K : ℕ) (mats : Array (ℕ × ℕ)) (fs : Forest.Shape) : Bool :=
  claimsOk { geo := geo, iU3 := iU3, nW := nW, mats := mats } K (padOfO fs) (VerifiableInference.Desc.First.Look.planesOk fs geo.lmb) fs.dT

/-- **The third conjunct reads these six alone.** -/
theorem claimsOkAtO_by (p : Attention.Plan) :
    claimsOkAtO p = claimsBy (geoOf p.S) p.iU3 p.nW (((p.seam.Fp.trees[p.iU3]?).map (·.K)).getD 0) (p.mats.map fun M => (M.m, M.k)) p.fs := rfl

/-- The rounds in front of a named step, off the cuts' pairs (look, take). -/
def roundsBy (cuts : List (String × ℕ)) (look : String) : Option ℕ :=
  if cuts.any fun c => c.1 == look then some ((cuts.takeWhile fun c => c.1 != look).foldl (fun n c => n + c.2) 0) else none

theorem roundsBefore_by (Z : ProofFile.Pub) (look : String) :
    Z.roundsBefore? look = roundsBy (Z.cuts.map fun c => (c.look, c.take)) look := by
  unfold ProofFile.Pub.roundsBefore? ProofFile.Pub.roundsBefore roundsBy
  rw [List.any_map, List.takeWhile_map, List.foldl_map]
  rfl

/-- The roots in front of a named step. rb k: the roots that the first k rounds declare. -/
def rootsBy (cuts : List (String × ℕ)) (rb : ℕ → ℕ) (look : String) : Option ℕ := (roundsBy cuts look).map rb

/-- "before", off the cuts' pairs and the roots. -/
def beforeBy (cuts : List (String × ℕ)) (rb : ℕ → ℕ) (nm : String) : Option (List (ℕ × ℕ)) := do
  let r0 ← rootsBy cuts rb (nm ++ ".0.call")
  let r1 ← rootsBy cuts rb (nm ++ ".2.scores")
  pure (beforeOf r0 r1)

/-- The roots that the first k declared rounds of the first chain send. -/
def rootsOf (Z : ProofFile.Pub) (k : ℕ) : ℕ := (Z.D.1.take k).foldl (fun n r => n + r.entry.roots) 0

/-- **"before" reads the cuts' pairs and the roots alone.** -/
theorem k5Before_by (Z : ProofFile.Pub) (nm : String) :
    H2K5.k5Before? Z nm = beforeBy (Z.cuts.map fun c => (c.look, c.take)) (rootsOf Z) nm := by
  unfold H2K5.k5Before? H2K5.k5Roots? beforeBy rootsBy
  rw [roundsBefore_by, roundsBefore_by]
  rfl

end H2K5.Row

#print axioms H2K5.Row.claimsOkAtO_by
#print axioms H2K5.Row.roundsBefore_by
#print axioms H2K5.Row.k5Before_by
