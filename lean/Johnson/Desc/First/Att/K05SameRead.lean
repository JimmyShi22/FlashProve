-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05SameRead.lean: kind K5: WHAT THE CLAIMS' SEAT READS OF THE LOOKUP's
RECORD: five equations between two records of what a lookup returned, under which the seat's tables
are the law's.

Why. The claims' seat (seatCO, Johnson/Desc/First/Att/SeatO.lean) reads the open segment's own field
g. The law's letter gOf a is what the lookup has heard, which the lookup's promise pins at another
reader of the record. The two fields need not be one record; the table of joints' item on them is a
Bool that compares them field by field. The seat's readings hang on five of these fields alone.

IS IT EMPTY HERE? SeatReadsSame g g holds (seatReadsSame_refl).

Main names:
  `SeatReadsSame g gL`: the key points zk, the point zx, the two points zb0 and zb1 at which the
    planes are read, and the shape are the same.
  `lookOfO_same`: under it what the lookup hands the tables (lookOfO,
    Johnson/Desc/First/Att/LookO.lean) is the same.
  `funsAt_same`: **funsAt A s is the law's list of tables**, where the open segment's field g holds
    a record with SeatReadsSame to the law's gL: funsAt_fields
    (Johnson/Desc/First/Att/Claims/FunsAt.lean) at g, with the law's returns carried over.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.FunsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open K5Law (oldOf funsAt funsAt_fields matsOf)

/-- What the claims' seat reads of the lookup's record is the same at the two. -/
structure SeatReadsSame (g gL : Forest.Heard) : Prop where
  zk : g.zk = gL.zk
  zx : g.zx = gL.zx
  zb0 : g.zb0 = gL.zb0
  zb1 : g.zb1 = gL.zb1
  shape : g.shape = gL.shape

theorem seatReadsSame_refl (g : Forest.Heard) : SeatReadsSame g g := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- What the lookup hands the tables is the same. -/
theorem lookOfO_same {g gL : Forest.Heard} (h : SeatReadsSame g gL) (lmb : ℕ) :
    lookOfO lmb g = lookOfO lmb gL := by
  unfold lookOfO Look.phiBOwn Look.planesOk Forest.Heard.zb
  simp only [h.zx, h.zb0, h.zb1, h.shape]

/-- **The seat's tables are the law's list**, at a field g with SeatReadsSame to the law's record.
-/
theorem funsAt_same (A : Attention.Plan) {s : First.S} {a₀ : First.AttOwn} {i : Runs.In}
    {g gL : Forest.Heard} {h : Heard} {G : Fork} {l : Left} (hs : s.here = .att a₀)
    (hg : a₀.g = some g) (hsr : SeatReadsSame g gL) (h5 : a₀.heard5 = some h) (hF : a₀.F = G)
    (left : LeftIs (geoOf A.S) gL.zk h G l) (geo : i.g = geoOf A.S)
    (points : pointsOf i.g gL.zk h l = some i.p)
    (tables : tablesP i.g (matsOf A.seam.tl.mats) A.nW (lookOfO (parCOf A).geo.lmb gL) i.p = some i.t)
    (hT : (G.trees[A.iU3]?).isSome = true) : funsAt A s = (oldOf A.S gL i).t.funs.toList := by
  rw [← hsr.zk] at left points
  rw [← lookOfO_same hsr] at tables
  have e := funsAt_fields A hs hg h5 hF left geo points tables hT
  exact e

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.lookOfO_same
#print axioms VerifiableInference.Desc.First.Att.P.funsAt_same
