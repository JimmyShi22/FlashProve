-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LayPremisesStatement.lean: IN THE GOALS' SCOPE, AT EACH OF THE TWELVE FEED-FORWARD
LAYERS' SEGMENTS: THE PREMISES ON PUBLIC DATA OF `LayLiveTables`
(Johnson/Desc/K8/Honest/LayLiveTablesStatement.lean) HOLD, at the public part's own layout, lists of
points, list of matrices and plan. A STATEMENT ALONE: one definition of a proposition; no definition
of another kind. NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals: a lemma's
statement.

THE TEN CLAUSES. (1) `readsOf` returns the lists · (2) each of the six matrices is read at the
lookup's point · (3) the pairs (rows, columns) that the own rounds' text lays the tables over are
those of the plan's list of matrices · (4) the plan's number of matrices · (5) every part of the six
matrices has the kit's rows and columns · (6) a block's rows divide the rows of af, qa and the two
of the stream · (7) the positions divide the rows of ad and ar · (8) the matrix b has 2 ^ lmb rows ·
(9) the positions are 2 ^ lt · (10) la = ls + lt.

WHAT IT IS NOT. On public data alone: no state, no draw, no weight. That g is below 12 and that hp
is the plan's entry number g are premises. The full size alone.

NEAR. `pub34_all` (Johnson/Goal/Meaning/Pub34All.lean), `points_of_layout`
(Johnson/Road/FormsKeysAdmit.lean), `tails_pair`, `rows_of_laid2` (FormsKeysTab.lean), `tails_size`
(Johnson/Meaning/ReadsPlan.lean), `tailsOf_b` (OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean),
`layout_caps` (OnBytes/Model/Fit/LayoutCaps.lean): called. `asks_pos`, `sizesPos_in_scope`
(Johnson/Desc/First/Link/Law/LayTablesInScope.lean): every family's length is AT MOST its matrix's
rows; here: it DIVIDES them, at the seven families that are spent.

Limits. Facts on public numbers. Nothing on any property.
-/
import Johnson.Road.FormsKeysMat
import OnBytes.Model.Verify
import Ladder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Road (firstM partsM rowsM colsM)

/-- **The statement of the title.** Not proved here; a lemma's statement, none of the library's
goals. -/
def LayPremises : Prop :=
  ∀ (P : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : Option ByteArray) (X : Verify.Public) (g : Nat)
    (hp : Layer.HPlan2), VerifierAndGoals.InScope P = true → VerifierAndGoals.readFiles P = .ok pp →
    Verify.publicOf P.pol P.KL lay = .ok X → g < 12 → X.G[g]? = some hp →
    Layer.readsOf X.layers.y = .ok X.layers.rd ∧
    ("Z" ∈ X.layers.rd.rdAF ∧ "Z" ∈ X.layers.rd.rdQA ∧ "Z" ∈ X.layers.rd.rdXI ∧
      "Z" ∈ X.layers.rd.rdXO ∧ "zt" ∈ X.layers.rd.rdAD ∧ "zt" ∈ X.layers.rd.rdAR) ∧
    (∀ M, ((X.layers.tails.getD g {}).mats.map fun M => (M.m, M.k)).getD M (0, 0) =
      ((hp.tl.mats.getD M {}).m, (hp.tl.mats.getD M {}).k)) ∧
    hp.tl.NM = (Layer.matIx X.layers.y).iXI + 1 ∧
    (∀ mat, mat ≤ 5 → ∀ q, q < partsM X.layers.y mat →
      ((X.layers.tails.getD g {}).mats.map fun M => (M.m, M.k)).getD
        (firstM X.layers.y mat + q) (0, 0) = (rowsM X.layers.y mat, colsM X.layers.y mat)) ∧
    (∀ mat ∈ [0, 3, 4, 5], rowsM X.layers.y mat % 2 ^ X.layers.y.h.la = 0) ∧
    (∀ mat ∈ [1, 2], rowsM X.layers.y mat % X.layers.y.T = 0) ∧
    (∃ k, ((X.layers.tails.getD g {}).mats.map fun M => (M.m, M.k)).getD
      (Layer.matIx X.layers.y).iB (0, 0) = (2 ^ X.layers.y.h.lmb, k)) ∧
    X.layers.y.T = 2 ^ X.layers.y.h.lt ∧ X.layers.y.h.la = X.layers.y.ls + X.layers.y.h.lt

end P1K8

#print axioms P1K8.LayPremises
