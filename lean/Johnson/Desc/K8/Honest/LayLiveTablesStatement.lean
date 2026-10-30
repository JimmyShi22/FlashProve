-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/LayLiveTablesStatement.lean: AT A FEED-FORWARD LAYERS' SEGMENT EVERY MATRIX
HAS, IN THE VERIFIER's LIST OF TABLES, ONE TABLE NONE OF WHOSE WEIGHTS READS 0 (`LiveTable`,
Johnson/Desc/K8/Honest/ReadsLiveOf.lean), WHERE NO COORDINATE OF THE POINT THAT THE LOOKUP ON THE
SEGMENT's CALLS LEFT READS 0 OR 1. On the verifier's own functions (OnBytes/Model/Layer.lean,
LayerForms.lean); no state, no chain, no prover. STATEMENTS ALONE: three definitions of
propositions; no definition of another kind. NOTHING IS PROVED IN THIS FILE, and none is one of the
library's goals: they are lemmas' statements.

WHAT IT IS NOT. CONDITIONAL: that the functions return, the six memberships, the facts on the
matrices' rows and THE PREMISE ON THE LOOKUP's POINT are premises; none is shown of anything here.
No draw of the segment's own rounds is spoken of: the tables chosen are the six at the lookup's
point and the one of public numbers.

  `LayTablesHas`    where `layTables` returns, every family that was asked lies in what is laid,
                    with its parts as `layParts` lays them
  `FamTables`       so every part of a family whose parts have one shape has its table in the list
                    that `funsOf` returns: the part's matrix, the family's length and weights,
                    vector number 2
  `LayLiveTables`   the title

WHICH TABLES. af (its parts), qa, xbI, xbO: the long table at Z, the last la coordinates of the
lookup's point. ad (its parts), ar: the short table at zt, its last lt. b: "b-pin", whose weights
are public numbers.

NEAR. `layTables_mem` (Johnson/Desc/First/Link/Law/LayTablesLive.lean), `layTables_laid`
(Johnson/Road/FormsKeysPoint.lean), `layTables_both` (Johnson/Road/K4/OwnedOfInTab.lean): from what
is laid to what was asked: the first statement is the way back. `laid_of_layTables`
(Johnson/Road/K4/C/Laid.lean, another group of authors', a file that is not in this library): the
families laid are those asked, in their order: with `layTables_mem` it gives the first statement.
`funsOf_mem`, `weights_of_names` (FormsKeysPoint.lean), `six_numbers`, `layParts_eq`
(FormsKeysTab.lean): called. `points_of_layout` (FormsKeysAdmit.lean): the six memberships.
`HeadLiveTables` (HeadLiveTablesStatement.lean of this folder): the like at the output head. That no
weight of a table of equality weights, or of a product of two, reads 0 where no coordinate reads 0
or 1 stands typed more than once: `eqTab_ne` (PlanesLiveOf.lean of this folder) and `longPhiNe`
(HeadLiveTables.lean), which are called; `eqTab_val_ne` (Johnson/Desc/K5/Honest/Law/EqTabNz.lean)
and `blockRows_eq_val_ne` (LiveValAt.lean there); `weight_ne`
(Johnson/Desc/ProofFile/Honest/K3/Good/Join.lean, a file that is not in this library).

Limits. Inequations on weights, under premises. Nothing on any property.
-/
import Johnson.Desc.K8.Honest.ReadsLiveOf
import OnBytes.Model.Layer
import Johnson.Road.FormsKeysMat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model

/-- The statement on the laying. Not proved here; a lemma's statement, none of the library's goals.
-/
def LayTablesHas : Prop :=
  ∀ (mats : Array (Nat × Nat)) (asks : List Layer.TableAsk) (p : Nat)
    (r : List Layer.TableAt × List (Layer.TableAsk × List (Nat × Nat)) × Nat),
    Layer.layTables mats asks p = some r →
    ∀ a ∈ asks, ∃ b, (a, (Layer.layParts mats a a.parts b).1) ∈ r.2.1

/-- The statement on one family. Not proved here; a lemma's statement, none of the library's goals.
-/
def FamTables : Prop :=
  ∀ (y : Layer.Lay) (fo : Forest.Heard) (pts : List (String × Array E))
    (mats : Array (Nat × Nat)) (asks : List Layer.TableAsk) (p : Nat)
    (r : List Layer.TableAt × List (Layer.TableAsk × List (Nat × Nat)) × Nat) (funs : Array HFun)
    (a : Layer.TableAsk) (m k : Nat) (phi : Array E),
    Layer.layTables mats asks p = some r → a ∈ asks →
    (∀ q, q < a.parts → mats.getD (a.M0 + q) (0, 0) = (m, k)) →
    Layer.funsOf y fo pts r.2.1 = some funs → Layer.phiOf y fo pts a = some phi →
    ∀ i, i < a.parts →
      ∃ Fn ∈ funs.toList, Fn.mat = a.M0 + i ∧ Fn.len = a.L ∧ Fn.phi = phi ∧ Fn.tree = 2

/-- **The statement of the title.** Not proved here; a lemma's statement, none of the library's
goals. -/
def LayLiveTables : Prop :=
  ∀ (y : Layer.Lay) (rd : Layer.Reads) (g : Nat) (mats : Array (Nat × Nat)) (H : Layer.Heard)
    (hd : Level) (hd2 : Option Level) (pts : List (String × Array E))
    (r : List Layer.TableAt × List (Layer.TableAsk × List (Nat × Nat)) × Nat) (funs : Array HFun)
    (tl : HTailF2),
    Layer.readsOf y = .ok rd → "Z" ∈ rd.rdAF → "Z" ∈ rd.rdQA → "Z" ∈ rd.rdXI → "Z" ∈ rd.rdXO →
    "zt" ∈ rd.rdAD → "zt" ∈ rd.rdAR → Layer.pointsOf y H hd hd2 = some pts →
    lastOf H.fo.zx y.h.lt = .ok H.ztF →
    Layer.layTables mats (Layer.tableAsks y rd g) 0 = some r →
    Layer.funsOf y H.fo pts r.2.1 = some funs → tl.funs = funs →
    (∀ M, mats.getD M (0, 0) = ((tl.mats.getD M {}).m, (tl.mats.getD M {}).k)) →
    tl.NM = (Layer.matIx y).iXI + 1 →
    (∀ mat, mat ≤ 5 → ∀ q, q < OnBytes.Road.partsM y mat →
      mats.getD (OnBytes.Road.firstM y mat + q) (0, 0) =
        (OnBytes.Road.rowsM y mat, OnBytes.Road.colsM y mat)) →
    (∀ mat ∈ [0, 3, 4, 5], OnBytes.Road.rowsM y mat % 2 ^ y.h.la = 0) →
    (∀ mat ∈ [1, 2], OnBytes.Road.rowsM y mat % y.T = 0) →
    (∃ k, mats.getD (Layer.matIx y).iB (0, 0) = (2 ^ y.h.lmb, k)) →
    y.T = 2 ^ y.h.lt → y.h.la = y.ls + y.h.lt →
    (∀ w ∈ H.fo.zx.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) →
    ∀ mu, mu < tl.NM → ∃ Fn, LiveTable tl mu Fn

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.LayTablesHas
#print axioms VerifiableInference.Desc.First.K8.Honest.FamTables
#print axioms VerifiableInference.Desc.First.K8.Honest.LayLiveTables
