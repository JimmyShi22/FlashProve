-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/FunsAt.lean: kind K5: THE LIST OF TABLES THAT THE CLAIMS' SEAT MAKES AT A RECORD IS THE LIST OF A LAW THAT HOLDS THE ROAD's RETURNS AS
PREMISES. funsAt A s: what the seat's reading at s (inOf at seatCO) lays as its tables, as records of OnBytes/Model; [] where the seat reads
nothing.

Main names:
  funsAt.
  inAt_of_is: from LeftIs, pointsOf's return, tablesP's return and "the array of the reads is in the ledger": what inAt (Claims/InAt.lean) returns.
  funsAt_is: so at a record in an attention segment that holds gL, h and the ledger G: funsAt A s = (tabBack t).funs.toList.
  funsAt_old: the same with the right side written as (oldOf S gL i).t.funs.toList (Claims/Any.lean), at i.t = t.
  funsAt_fields: the same, its premises in the form of the fields left · geo · points · tables of a law's record of returns.
Over Claims/LeftIsBack.lean (leftP_of_is) and Claims/InAt.lean (inOf_isAt).
PREMISES THAT A READER MAY NOT EXPECT: hT: (G.trees[A.iU3]?).isSome: the seat's reading also reads the array's width: where the array is not in the ledger
  it gives nothing and funsAt is []. (The tables are tablesP's at (parCOf A).mats: that is matsOf A.mats and matsOf A.seam.tl.mats, both by rfl: Plan.mats is
  the seam's record's list by its own text, OnBytes/Model/AttentionPlan.lean.)
IS IT EMPTY HERE? An equation under returns that are shown of nothing here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.LeftIsBack
import Johnson.Desc.First.Att.Claims.InAt
import Johnson.Desc.First.Att.Claims.Any

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard Left Pts TablesP)

/-- The tables that the claims' seat makes at the record. -/
def funsAt (A : Attention.Plan) (s : First.S) : List HFun :=
  ((P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) s).map fun z => (tabBack z.1.t).funs.toList).getD []

theorem parCOf_mats (A : Attention.Plan) : (P.parCOf A).mats = matsOf A.mats := rfl

variable {c : ParC} {gL : Forest.Heard} {h : Heard} {G : Fork} {l : Left} {p : Pts} {t : TablesP}

/-- What inAt returns, from the road's returns. -/
theorem inAt_of_is (hl : P.LeftIs c.geo gL.zk h G l) (hp : P.pointsOf c.geo gL.zk h l = some p)
    (ht : P.tablesP c.geo c.mats c.nW (P.lookOfO c.geo.lmb gL) p = some t) {T : HTree}
    (hT : G.trees[c.iU3]? = some T) :
    inAt c gL h G = some ({ g := c.geo, p := p, t := t, zk := gL.zk, iU3 := c.iU3 }, T.K) := by
  unfold inAt
  rw [ptsFrom_of_is hl hp]
  simp only [Option.bind_eq_bind, Option.bind_some, ht, hT, Option.map_some]
  rfl

/-- **The seat's list is the road's.** -/
theorem funsAt_is (A : Attention.Plan) {s : First.S} {a₀ : First.AttOwn} (hs : s.here = .att a₀) (hg : a₀.g = some gL)
    (h5 : a₀.heard5 = some h) (hF : a₀.F = G) (hl : P.LeftIs (P.parCOf A).geo gL.zk h G l)
    (hp : P.pointsOf (P.parCOf A).geo gL.zk h l = some p)
    (ht : P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW (P.lookOfO (P.parCOf A).geo.lmb gL) p = some t)
    (hT : (G.trees[A.iU3]?).isSome = true) : funsAt A s = (tabBack t).funs.toList := by
  obtain ⟨T, hT'⟩ := Option.isSome_iff_exists.1 hT
  unfold funsAt
  rw [inOf_isAt hs, hg, h5, hF]
  show ((inAt (P.parCOf A) gL h G).map _).getD [] = _
  rw [inAt_of_is hl hp ht (T := T) hT']
  rfl

/-- The same, the right side as a law writes it. -/
theorem funsAt_old (A : Attention.Plan) {s : First.S} {a₀ : First.AttOwn} {i : P.Runs.In} (hs : s.here = .att a₀)
    (hg : a₀.g = some gL) (h5 : a₀.heard5 = some h) (hF : a₀.F = G) (hl : P.LeftIs (P.parCOf A).geo gL.zk h G l)
    (hp : P.pointsOf (P.parCOf A).geo gL.zk h l = some i.p)
    (ht : P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW (P.lookOfO (P.parCOf A).geo.lmb gL) i.p = some i.t)
    (hT : (G.trees[A.iU3]?).isSome = true) (S : Attention.Shape) :
    funsAt A s = (oldOf S gL i).t.funs.toList :=
  funsAt_is A hs hg h5 hF hl hp ht hT

/-- The plan's list of matrices is its smallness test's record's: by the plan's own text. -/
theorem parCOf_mats' (A : Attention.Plan) : (P.parCOf A).mats = matsOf A.seam.tl.mats := rfl

/-- **The same, its premises in the form of the fields left · geo · points · tables of a law's record of returns**, at S := A.S, the key points gL.zk, the
smallness test's record A.seam.tl, the length A.nW and the seat's own look. -/
theorem funsAt_fields (A : Attention.Plan) {s : First.S} {a₀ : First.AttOwn} {i : P.Runs.In} (hs : s.here = .att a₀)
    (hg : a₀.g = some gL) (h5 : a₀.heard5 = some h) (hF : a₀.F = G) (left : P.LeftIs (P.geoOf A.S) gL.zk h G l)
    (geo : i.g = P.geoOf A.S) (points : P.pointsOf i.g gL.zk h l = some i.p)
    (tables : P.tablesP i.g (matsOf A.seam.tl.mats) A.nW (P.lookOfO (P.parCOf A).geo.lmb gL) i.p = some i.t)
    (hT : (G.trees[A.iU3]?).isSome = true) : funsAt A s = (oldOf A.S gL i).t.funs.toList := by
  rw [geo] at points tables
  exact funsAt_old A hs hg h5 hF left points tables hT A.S

end K5Law

#print axioms K5Law.funsAt_fields
#print axioms K5Law.inAt_of_is
#print axioms K5Law.funsAt_is
#print axioms K5Law.funsAt_old
