-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/TestsReturns.lean: when the smallness test's three steps behind a
sub-proof's last claim (testsP, Johnson/Desc/First/TailClaims/SelfRows.lean) return, with the
ledger read through its shape alone. General laws; nothing is evaluated.

The form. "Premises on sizes, counts, names and marks IN FRONT of the steps, and the named tests on
values, give: the steps return, and the ledger's shape behind them is this function of the shape in
front."

  `treeAt_ledSh`, `rowAt_treeSh`: the shape's readers against the ledger's own.
  `updCoef tl zb0 zb1 L`: the ledger's shape behind the step that lays the virtual rows' weights:
    the writes of coefWrites (CoefWrites.lean), one after the other, each laying one size and the
    three marks of a product form; which arrays are tables and how many rows an array has is read
    off L.
  **`ledSh_coefBody`**: ledSh (coefBody tl g F) = updCoef tl .. (ledSh F).
  `headL`, `piecesL`, `tieL`, `planesL`, `sizesL`, `readL`, `shapeL`: the guards of shapeT
    (TestsCut.lean) with the ledger's shape L in the ledger's place: the verifier's texts
    (OnBytes/Model/Tail.lean: piecesTile, tieShapeHeld, planesShapeHeld, readShapeHeld) once more,
    reading L. **`shapeT_eq`**: shapeT .. Fc = shapeL .. (ledSh Fc): so shapeT reads of the ledger
    its shape alone: by Lean.
  **`tests_return`**: the three look-ups are there · shapeL accepts at updCoef .. (ledSh F) · valsT
    accepts ⊢ testsP nU tl F = .ok (coefBody tl g F), and the ledger's shape behind is
    updCoef .. (ledSh F).

Limits. OF THE SMALLNESS TEST's OWN STRUCTURE tl AND OF WHAT THE LOOKUP HEARD (g) THE GUARDS STILL
READ THE STRUCTURES THEMSELVES: that they read numbers, names and sizes of these alone is said by
reading their texts, not by a theorem here. That shapeL or valsT accepts anywhere is not shown.
valsT is asked at the ledger itself, in front of and behind the weights' step. In updCoef an array
that is not there counts as a table; the write made for it falls outside the list and is dropped in
silence. tests_return has no caller; its second conjunct needs no premise. TestsShape.lean's
tests_shape has its guards' premise at shapes alone (its valsAt stays at the structures), but ends
in "there is a ledger": the ledger by name stands here and in TestsCut.lean's tests_returns. shapeL
here is another thing than Johnson.AtFull.Shape.shapeL. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.First.TailClaims.TestsCut
import Johnson.Desc.First.TailClaims.CoefWrites
import Johnson.Desc.First.Shape.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Tests
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Shape (LedSh TreeSh RowSh ledSh treeSh rowSh ledSh_onRow)

/-! ## 1 The readers -/

theorem getD_map_toList {α β : Type} (a : Array α) (f : α → β) (i : Nat) (d : α) :
    (a.toList.map f).getD i (f d) = f (a.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases a[i]? <;> rfl

theorem treeAt_ledSh (F : Fork) (t : Nat) : (ledSh F).treeAt t = treeSh (F.trees.getD t {}) :=
  getD_map_toList F.trees treeSh t {}

theorem rowAt_treeSh (T : HTree) (e : Nat) : (treeSh T).rowAt e = rowSh (T.rows.getD e {}) :=
  getD_map_toList T.rows rowSh e {}

theorem rows_treeSh (T : HTree) : (treeSh T).rows.length = T.rows.size := by
  show (T.rows.toList.map rowSh).length = _
  simp

/-! ## 2 The shape behind the step that lays the weights -/

/-- One write, on the shape. -/
def layCoef (L : LedSh) (w : Write) : LedSh :=
  L.modRow w.1 w.2.1 fun r => (r.setCoef w.2.2.1).setForm true w.2.2.2.1 w.2.2.2.2

/-- **The ledger's shape behind the step that lays the weights.** -/
def updCoef (tl : HTailF2) (zb0 zb1 : Nat) (L : LedSh) : LedSh :=
  (coefWrites tl zb0 zb1 (fun t => !(L.treeAt t).symbols) (fun t => (L.treeAt t).R)).foldl
    layCoef L

theorem isTable_sh (T : HTree) : (T.kind == HKind.table) = !(treeSh T).symbols := by
  show _ = !(T.kind == HKind.symbols)
  cases T.kind <;> rfl

theorem ledSh_coefBody (tl : HTailF2) (g : Forest.Heard) (F : Fork) :
    ledSh (coefBody tl g F) = updCoef tl (g.zb 0).size (g.zb 1).size (ledSh F) := by
  have h := (lays_coefBody tl g F).reads ledSh layCoef fun F t r n o a f hf =>
    ledSh_onRow F t r f (fun r => (r.setCoef n).setForm true o a) fun x => by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf x
      show RowSh.mk (f x).coef.size (f x).L.size (f x).L0 (f x).rowForm (f x).rowOnes
        (f x).rowFirst = RowSh.mk n x.L.size x.L0 true o a
      rw [h1, h2, h3, h4, h5, h6]
  rw [h]
  unfold updCoef
  congr 2
  · funext t
    rw [treeAt_ledSh, isTable_sh]
  · funext t
    rw [treeAt_ledSh]
    rfl

/-! ## 3 The guards, reading the ledger's shape -/

def headL (tl : HTailF2) (g : Forest.Heard) (nbW : Nat) (L : LedSh) : Bool :=
  (L.treeAt tl.ix.ZZ).rows.length == 2 * nbW + 2 && tl.forestHeld g &&
    [0, 1].all (tl.callHeld g nbW)

def piecesL (tl : HTailF2) (L : LedSh) (W : List Want) : Bool :=
  let T := L.treeAt tl.ix.ZZ
  T.name == "ZZ" && T.R == tl.tau && T.K == 2 * tl.mz && noneMeet W &&
    (W.foldl (fun s w => s + w.Rp * w.Cp) 0) == T.R * T.K &&
    W.all fun w =>
      let p := (tl.zOf w.call).pieces.getD w.i {}
      let row := T.rowAt w.row
      p.tree == tl.ix.ZZ && p.row == w.row && p.r0 == w.r0 && p.Rp == w.Rp && p.c0 == w.c0 &&
        p.Cp == w.Cp && decide (w.r0 + w.Rp ≤ T.R) && decide (w.c0 + w.Cp ≤ T.K) &&
        row.coef == T.R && row.entries == T.K

def tieL (tl : HTailF2) (L : LedSh) (mu : Nat) : Bool :=
  let s := tl.shp.getD mu {}
  let X := L.treeAt (tl.gtTree.getD mu 0)
  let row := X.rowAt 0
  let mS2 := ((tl.mats.getD mu {}).m + 2) / 3
  X.symbols && X.rows.length == 1 && X.R == s.Rr && X.K == s.Kc &&
    decide (mu < tl.tieObj.size) && mS2 == s.mS && s.J == 1 && s.R == mS2 && s.Rr == mS2 &&
    s.Rd == 0 && s.k == (tl.mats.getD mu {}).k && s.K1 == s.k && s.Kc == s.k &&
    (tl.rowX.getD mu #[]).size == mS2 && (tl.loX.getD mu #[]).size == 1 &&
    decide (tl.tieObj.getD mu 0 < L.planClaims) && row.coef == s.Rr && row.entries == s.k &&
    (tl.gamX.getD mu #[]).size == s.k && (tl.gamV.getD mu #[]).size == s.k

def planesL (tl : HTailF2) (L : LedSh) (g : Forest.Heard) : Bool :=
  let B := L.treeAt tl.ix.BZ
  let lKB := tl.f9.kT + tl.f9.cK
  B.rows.length == 3 && B.R == 32 && B.K == tl.bzColumns && tl.f9.NC == 2 && tl.f9.cK == 1 &&
    B.K == 2 ^ lKB &&
    (List.range 3).all (fun r => (B.rowAt r).coef == 32 && (B.rowAt r).entries == B.K) &&
    g.zb0.size == 5 + lKB && g.zb1.size == 5 + lKB

def sizesL (tl : HTailF2) (g : Forest.Heard) (nbW : Nat) (L : LedSh) : Bool :=
  ((L.treeAt tl.ix.ZZ).rowAt (2 * nbW)).coef == tl.tau &&
    ((L.treeAt tl.ix.ZZ).rowAt (2 * nbW + 1)).coef == tl.tau &&
    ((L.treeAt tl.ix.ZZ).rowAt (2 * nbW + 1)).entries == 2 * tl.mz && tl.gamX.size == tl.NM &&
    tl.gamV.size == tl.NM && (List.range tl.NM).all (tieL tl L) &&
    tl.shp.foldl (fun n s => n + s.m) 0 == tl.mz && planesL tl L g

/-- readShapeHeld's text with n, the row's number of entries, in the row's place: of the row's
weights that test reads their number alone (read_eq). -/
def readL (tl : HTailF2) (n : Nat) : Bool :=
  let read := tl.funs.filter fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)
  n == 2 * tl.mz &&
    (read.all fun Fn =>
      let m := (tl.mats.getD Fn.mat {}).m
      m != 0 && Fn.len != 0 && m % Fn.len == 0 && Fn.phi.size == Fn.len) &&
    read.foldl (fun q Fn => q + (tl.mats.getD Fn.mat {}).m / Fn.len) 0 == tl.nX4Laid &&
    (List.range tl.NM).foldl (fun n mu => n + (tl.mats.getD mu {}).m) 0 == tl.mz

/-- **The guards on sizes, counts, names and marks, reading the ledger's shape.** -/
def shapeL (nU : Array Nat) (tl : HTailF2) (g : Forest.Heard) (nbW : Nat) (Wn : List Want)
    (L : LedSh) : Bool :=
  nU == tl.nUF && tl.lsTail.size == tl.slotB - tl.slotA && headL tl g nbW L &&
    piecesL tl L Wn && sizesL tl g nbW L &&
    readL tl ((L.treeAt tl.ix.ZZ).rowAt (2 * nbW)).entries

variable {nU : Array Nat} {tl : HTailF2} {F : Fork} {g : Forest.Heard} {jo nbW : Nat}
  {Wn : List Want}

theorem headT_eq (F : Fork) : headT tl g nbW F = headL tl g nbW (ledSh F) := by
  unfold headT headL
  rw [treeAt_ledSh, rows_treeSh]

theorem piecesTile_eq (F : Fork) (W : List Want) : tl.piecesTile F W = piecesL tl (ledSh F) W := by
  unfold piecesTile piecesL
  simp only [treeAt_ledSh, rowAt_treeSh]
  rfl

theorem tie_eq (F : Fork) (mu : Nat) : tl.tieShapeHeld F mu = tieL tl (ledSh F) mu := by
  unfold tieShapeHeld tieL
  simp only [treeAt_ledSh, rowAt_treeSh, rows_treeSh]
  rfl

theorem planes_eq (F : Fork) : tl.planesShapeHeld F g = planesL tl (ledSh F) g := by
  unfold planesShapeHeld planesL
  simp only [treeAt_ledSh, rowAt_treeSh, rows_treeSh]
  rfl

theorem sizesT_eq (F : Fork) : sizesT tl g nbW F = sizesL tl g nbW (ledSh F) := by
  have e : tl.tieShapeHeld F = tieL tl (ledSh F) := funext (tie_eq F)
  unfold sizesT sizesL
  simp only [treeAt_ledSh, rowAt_treeSh, planes_eq, e]
  rfl

theorem read_eq (L4 : Array E) : tl.readShapeHeld L4 = readL tl L4.size := rfl

/-- **shapeT reads of the ledger its shape alone.** -/
theorem shapeT_eq (Fc : Fork) : shapeT nU tl g nbW Wn Fc = shapeL nU tl g nbW Wn (ledSh Fc) := by
  unfold shapeT shapeL
  rw [headT_eq, piecesTile_eq, sizesT_eq, read_eq, treeAt_ledSh, rowAt_treeSh]
  rfl

/-! ## 4 The law -/

/-- **THE THREE STEPS RETURN, AND THE LEDGER's SHAPE BEHIND THEM.** -/
theorem tests_return (hg : tl.heard = some g) (hjo : tl.joinObj9 = some jo)
    (hw : tl.wants = some (nbW, Wn))
    (hS : shapeL nU tl g nbW Wn (updCoef tl (g.zb 0).size (g.zb 1).size (ledSh F)) = true)
    (hV : valsT nU tl F g jo nbW Wn (coefBody tl g F) = true) :
    testsP nU tl F = .ok (coefBody tl g F) ∧
      ledSh (coefBody tl g F) = updCoef tl (g.zb 0).size (g.zb 1).size (ledSh F) :=
  ⟨tests_returns hg hjo hw (by rw [shapeT_eq, ledSh_coefBody]; exact hS) hV,
    ledSh_coefBody tl g F⟩

end VerifiableInference.Desc.First.TailClaims.Law.Tests

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.treeAt_ledSh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.ledSh_coefBody
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.shapeT_eq
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.tests_return
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.getD_map_toList
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.rowAt_treeSh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.rows_treeSh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.layCoef
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.updCoef
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.isTable_sh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.headL
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.piecesL
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.tieL
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.planesL
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.sizesL
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.readL
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.shapeL
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.headT_eq
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.piecesTile_eq
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.tie_eq
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.planes_eq
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.sizesT_eq
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.read_eq
