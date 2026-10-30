-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Fresh.lean: THE SHAPE OF THE LEDGER FROM WHICH A SUB-PROOF STARTS
(startFork, Johnson/Desc/First/Walk/FirstQuiet.lean), AS A FUNCTION OF THE SHAPE OF THE PLAN's OWN
LEDGER AND THE PLAN's NUMBER OF SLOTS. A general law; nothing is evaluated.

Why. startFork gives every virtual row its K weights, all 0, and lays four arrays of n zeros or
marks. At the protocol's sizes a row has up to a million weights. Whoever wants that ledger's shape
as a written value must not build these arrays to count them. Here the shape is had from numbers: a
row's number of entries becomes its array's number of columns; three sizes become n; the marks
become a list of n marks "not filled".

  `LedSh.fresh L n`: that function on shapes.
  **`ledSh_startFork`**: ledSh (startFork X n) = (ledSh X.Fp).fresh n.

Limits. The list of n marks is still built (n is some thousands). The shape of the plan's own ledger
X.Fp is read off that ledger: that its rows hold no long vector is the plan's maker's matter and is
not shown here. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Shape.Parts
import Johnson.Desc.First.Walk.FirstQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model
open Johnson.Desc.First.Walk (LinkPub startFork emptySlots weightsAtZero)

/-- A virtual row with as many entries as its array has columns. -/
def RowSh.filled (r : RowSh) (K : Nat) : RowSh := RowSh.mk r.coef K r.col0 r.form r.ones r.first

/-- An array with every virtual row filled. -/
def TreeSh.filled (T : TreeSh) : TreeSh := T.setRows (T.rows.map fun r => r.filled T.K)

/-- **The shape of the ledger from which a sub-proof starts.** n: the plan's number of slots. -/
def LedSh.fresh (L : LedSh) (n : Nat) : LedSh :=
  LedSh.mk n n n (List.replicate n false) L.owed L.planClaims (L.trees.map TreeSh.filled) L.next n
    L.claims L.drawn L.handed L.shut

theorem treeSh_filled (X : HTree) :
    treeSh { X with rows := X.rows.map fun r => { r with L := Array.replicate X.K zeroE } } =
      (treeSh X).filled := by
  show TreeSh.mk X.name (X.kind == .symbols) X.R X.K
    ((X.rows.map fun r => { r with L := Array.replicate X.K zeroE }).toList.map rowSh)
    X.root.isSome =
    TreeSh.mk X.name (X.kind == .symbols) X.R X.K
      ((X.rows.toList.map rowSh).map fun r => r.filled X.K) X.root.isSome
  rw [Array.toList_map, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  show RowSh.mk r.coef.size (Array.replicate X.K zeroE).size r.L0 r.rowForm r.rowOnes r.rowFirst =
    RowSh.mk r.coef.size X.K r.L0 r.rowForm r.rowOnes r.rowFirst
  rw [Array.size_replicate]

/-- **THE FRESH LEDGER's SHAPE, FROM NUMBERS.** -/
theorem ledSh_startFork (X : LinkPub) (n : Nat) :
    ledSh (startFork X n) = (ledSh X.Fp).fresh n := by
  have e : (X.Fp.trees.map fun Y =>
      { Y with rows := Y.rows.map fun r => { r with L := Array.replicate Y.K zeroE } }).toList.map
        treeSh = (X.Fp.trees.toList.map treeSh).map TreeSh.filled := by
    rw [Array.toList_map, List.map_map, List.map_map]
    exact List.map_congr_left fun Y _ => treeSh_filled Y
  show LedSh.mk n (Array.replicate n zeroE).size (Array.replicate n zeroE).size
      (Array.replicate n false).toList (X.Fp.owed.toList.map (·.added)) X.Fp.planClaimsF
      ((X.Fp.trees.map fun Y =>
        { Y with rows := Y.rows.map fun r => { r with L := Array.replicate Y.K zeroE } }).toList.map
          treeSh)
      X.Fp.next (Array.replicate n zeroE).size X.Fp.nClaim X.Fp.thetaDrawnF X.Fp.kapMapF.toList
      X.Fp.doorShutF = _
  rw [e, Array.size_replicate, Array.toList_replicate]
  rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.treeSh_filled
#print axioms VerifiableInference.Desc.First.Shape.ledSh_startFork
#print axioms VerifiableInference.Desc.First.Shape.RowSh.filled
#print axioms VerifiableInference.Desc.First.Shape.TreeSh.filled
#print axioms VerifiableInference.Desc.First.Shape.LedSh.fresh
