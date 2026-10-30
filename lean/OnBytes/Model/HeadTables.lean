-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/HeadTables.lean: the tables of reads of the sub-proof of the output head.

The claims of the sub-proof do not read the committed cells themselves. The prover commits to one
more vector, the reads. It is made of tables. A table belongs to a matrix and to a public vector of
weights on a stretch of that matrix's rows. The table has one entry for each column and each stretch
of the matrix: the sum of the cells of that stretch of that column under these weights. The
smallness test ties the reads to the cells (OnBytes/Model/Tail.lean). This file lists the head's
fifteen tables in their fixed order and gives the one function through which the head's own claims
name an entry. The C++ counterpart is the middle part of runForkHidH2 in vf_output_head_check.inc.

Main definitions: `Tables`, `addFun`, `costWeights`, `tablesOf`, `Run`, `tabAt`, `U3at`.
What is not claimed: no theorem is stated here.
-/
import OnBytes.Model.HeadHeard

namespace OnBytes.Model.Head

/-- The names of this file's refusals, without the prefix "H:" that cp_verify puts before
some of them. Where cp_verify appends the name of a segment or of a table to a name, the name here
ends before it. -/
def Tables.names : List String :=
  ["internal-f-fun-closed", "plan-tensor-layout", "internal-segment", "forest-planes",
   "internal-h-table-index", "internal-W-length-H", "internal-table"]

/-- The tables added so far. -/
structure Tables where
  /-- one record for each part of each table, in the order of the vector -/
  funs : Array HFun := #[]
  /-- the length of the vector so far -/
  p : Nat := 0
  /-- for each table: its name, its first entry, and its length over all parts -/
  tab : List (String × Nat × Nat) := []
  deriving Inhabited

/-- Adds one table: a record for each of the parts M0, M0 + 1 and so on of a matrix. Lf is the
length of a stretch. The caller must see that phi, the weights, has this length; the smallness
test refuses another one. An empty table would share its first entry with the next one and is
refused. -/
def addFun (mats : Array TMat) (t : Tables) (M0 parts Lf : Nat) (phi : Array E) (nm : String) :
    Option Tables :=
  let r := (List.range parts).foldl
    (fun (s : Array HFun × Nat) q =>
      let M := mats.getD (M0 + q) {}
      (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
        s.2 + M.k * (M.m / Lf)))
    (t.funs, t.p)
  if r.2 == t.p then none
  else some { funs := r.1, p := r.2, tab := t.tab ++ [(nm, t.p, r.2 - t.p)] }

/-- Returns phiC, ERC and rhoCv, in this order, from the position point zt of the call with the
segment HD0. phiC and rhoCv are vectors over the positions. phiC[t] is eq(zt, t) at the positions
that have a cost (`Covered.hOnC`, OnBytes/Model/HeadLayout.lean) and 0 elsewhere. ERC is the sum of
phiC's entries. rhoCv is 1 at these positions and 0 elsewhere. -/
def costWeights (cov : Covered) (zt : Array E) : Array E × E × Array E :=
  let e := eqTab zt
  let phiC := e.mapIdx fun t x => if cov.hOnC.getD t false then x else zeroE
  (phiC, phiC.foldl addE zeroE, e.mapIdx fun t _ => if cov.hOnC.getD t false then oneE else zeroE)

/-- The head's tables, in the order of the vector of reads. -/
def tablesOf (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x : Heard) : SubM Tables := do
  mustAs "internal-f-fun-closed" hp.tl.funOpen
  let mats := hp.tl.mats
  let iHF := 0
  let iHD := h.NHf
  let iHR := iHD + 1
  let iBH := iHR + 1
  let iXL := iBH + 1
  let La := 2 ^ h.la
  let ZV ← held (lastOf x.wpl.r h.la)
  let lowN ← held (cutLast (zjOf L x.g1 x.qN) h.ls)
  let YN := longPoint lowN.2 x.tN.r
  mustAs "plan-tensor-layout" (YN.size == h.la && h.la == h.ls + h.lt)
  let (phiC, _, rhoCv) := costWeights cov (ztOf h L x.g1 x.qH)
  -- weight 1 on each of a block's S2 features, phiC on the positions
  let phiZ := (Array.range La).map fun i => phiC.getD (i % h.T) zeroE
  let qFC ← getAs "internal-segment" (callNo L "CNF")
  let qROW ← getAs "internal-segment" (callNo L "ROW")
  let mb := 2 ^ h.lmbH
  let b0 ← getAs "forest-planes" (Forest.phiB x.g1 h.lmbH 0)
  let b1 ← getAs "forest-planes" (Forest.phiB x.g1 h.lmbH 1)
  let asks : List (Nat × Nat × Nat × Array E × String) := [
    (iHF, h.NHf, La, longPhi x.Zl h.ls h.lt, "hf@Z"),
    (iHF, h.NHf, La, phiZ, "hf@phiZ"),
    (iXL, 1, La, longPhi ZV h.ls h.lt, "xbL@Z_V"),
    (iXL, 1, La, longPhi YN h.ls h.lt, "xbL@Y_N"),
    (iHD, 1, h.T, eqTab (ztOf h L x.g1 qFC), "hd@zt_FC"),
    (iHD, 1, h.T, eqTab x.tH.r, "hd@r_H"),
    (iHR, 1, h.T, eqTab (ztOf h L x.g1 qROW), "hr@zt_ROW"),
    (iHR, 1, h.T, eqTab x.PV, "hr@P_V"),
    (iHR, 1, h.T, eqTab x.tV.r, "hr@r_tV"),
    (iHR, 1, h.T, eqTab x.tN.r, "hr@rt_N"),
    (iHR, 1, h.T, phiC, "hr@phiC"),
    (iHR, 1, h.T, rhoCv, "hr@rhoC"),
    (iBH, 1, mb, b0, "bH-bits-0"),
    (iBH, 1, mb, b1, "bH-bits-1"),
    (iBH, 1, mb, Forest.phiP h.lmbH, "bH-pin")]
  let t ← getAs "internal-h-table-index"
    (asks.foldlM (fun t a => addFun mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) {})
  mustAs "internal-W-length-H" (t.p == hp.nU.getD 2 0)
  pure t

/-- All that the claims of the sub-proof are made from. -/
structure Run where
  /-- the public numbers -/
  h : Shape
  /-- the layout -/
  L : HL
  /-- the matrix of the residual stream -/
  b : Border
  /-- the plan -/
  hp : HPlanH2
  /-- the covered positions -/
  cov : Covered
  /-- what was received and drawn -/
  x : Heard
  /-- the tables of reads -/
  t : Tables
  /-- the number of the vector of reads in the sub-proof's list of arrays -/
  iU3 : Nat

/-- The first entry of the table with this name. -/
def tabAt (R : Run) (n : String) : SubM Nat := do
  getAs "internal-table" ((R.t.tab.find? fun e => e.1 == n).map (·.2.1))

/-- Entry i of the table that begins at entry t of the reads, all its parts together. The head's own
claims name an entry through this function alone. The smallness test's claims do not pass through
it: `readEnts` (OnBytes/Model/Tail.lean) computes an entry's place itself, by the rule of `uEnt`.
Refused: an index at or beyond the table's length, or a t at which no table begins. A wrong index
inside the right table is not noticed, nor a t at which another table than the one meant begins. -/
def U3at (R : Run) (t i : Nat) : SubM Aff := do
  mustAs "internal-h-table-index" (R.t.tab.any fun e => e.2.1 == t && decide (i < e.2.2))
  uEnt R.iU3 (t + i)

end OnBytes.Model.Head
