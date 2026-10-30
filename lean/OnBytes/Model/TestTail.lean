-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTail.lean: small examples for FormF.lean, Trees.lean and Tail.lean.

The expected values were worked out by hand from the C++ source
(verifier/src/vf_smallness_packing.h, vf_subproof_segment.h, vf_smallness_test.h,
vf_smallness_test_members.inc; for the pieces' a, b and off vf_lookup_helpers.h; for the lookup's
numbers and the name forest-only-padding vf_lookup_argument.h). No C++ program printed them. One
refusal has no counterpart there: a list hasU of three entries (internal-t2f-lists); the C++
declares hasU as an array of four. The terms are explained in OnBytes/Model/Tail.lean (the docstring
of HTailF2 says where). The file is not imported by the program. -/
import OnBytes.Model.Tail

namespace OnBytes.Model.TestTail

open OnBytes OnBytes.Model

/-! ## Packing -/

#guard radb == 1048576
#guard (ShP.of 7 5 2).mS == 3 && (ShP.of 7 5 2).aX == 2 && (ShP.of 7 5 2).Kc == 5
#guard (ShP.of 6 5 1).mS == 2 && (ShP.of 1 1 1).mS == 1 && (ShP.of 1 1 1).aX == 0

/-- Four rows of cells in two rows of symbols: the weights 2, 2 B, 2 B^2 and 3. -/
def left : Option (Array E) := tieLeft (ShP.of 4 2 1) #[ofNat 2, ofNat 3] #[oneE]

#guard left == some #[ofNat 2, ofNat (2 * 2 ^ 20), ofNat (2 * 2 ^ 40), ofNat 3]
#guard tieLeft (ShP.of 4 2 1) #[ofNat 2] #[oneE] == none
#guard tieRight (ShP.of 4 2 1) #[oneE] #[ofNat 5, ofNat 7] == some #[ofNat 5, ofNat 7]
#guard tieRight (ShP.of 4 2 1) #[oneE] #[ofNat 5] == none

/-- A point with three coordinates. -/
def point : Array E := #[ofNat 3, ofNat 5, ofNat 11]

#guard (List.range 8).all fun i => eqPlainF point i == (eqTab point).getD i zeroE
#guard EqRun.all point 0 8 fun i e => e == eqPlainF point i
#guard EqRun.all point 3 5 fun i e => e == eqPlainF point (3 + i)
-- EqRun.all is not vacuous: a test that fails only at index 6 makes it false.
#guard !EqRun.all point 0 8 fun i e => i != 6 || e != eqPlainF point 6
#guard allBelow 5 (· < 5) && !allBelow 6 (· < 5) && allBelow 0 fun _ => false

/-- An owner's record that is whole. -/
def own : PlaceF :=
  { owner := some 1, rootIndex := some 2, sh := some (ShP.of 6 4 2), matrix := some (0, 4, 6),
    hb := 100, mS := 2, lanes := 3, padRows := 2, J := 1, K := 4 }

#guard own.whole
#guard samePlaceF own own == ""
#guard samePlaceF own { own with owner := some 0 } == "P0"
#guard samePlaceF own { own with sh := some (ShP.of 6 4 1) } == "P1"
#guard samePlaceF own { own with matrix := some (0, 3, 6) } == "P3"
#guard samePlaceF { own with K := 3 } { own with K := 3 } == "P3"
#guard samePlaceF own { own with matrix := some (0, 4, 5) } == "P4"
#guard samePlaceF own { own with rootIndex := some 0 } == "P5"
#guard samePlaceF own { own with hb := 99 } == "P6"
#guard samePlaceF own { own with padRows := 4 } == "P9"

/-! ## Product forms of weights on rows -/

/-- An array of six rows. -/
def six : HTree := { R := 6, K := 1 }

/-- The equality polynomial of a point with one coordinate on the rows 4 and 5. -/
def onTwoRows : HRow := { rowForm := true, rowPoint := #[ofNat 9], rowFirst := 4 }

#guard rowFormOK six onTwoRows
#guard !rowFormOK six { onTwoRows with rowFirst := 5 }
#guard !rowFormOK six { onTwoRows with rowFirst := 6 }
#guard (productWritten (rowProduct six onTwoRows)).extract 0 6 ==
  #[zeroE, zeroE, zeroE, zeroE, subE oneE (ofNat 9), ofNat 9]
#guard (productWritten (rowProduct six { rowForm := true, rowOnes := true })).extract 0 6 ==
  Array.replicate 6 oneE
#guard (productWritten (rowProduct six (HTailF2.formPowers {} (ofNat 2) 6))).extract 0 6 ==
  #[ofNat 1, ofNat 2, ofNat 4, ofNat 8, ofNat 16, ofNat 32]
#guard productWritten (pickIndex 2 2) == #[zeroE, zeroE, oneE, zeroE]

/-! ## The smallness test's public numbers -/

#guard t2D1 == 8
#guard (t2BL 160).toOption == some #[(0, 128), (128, 32)]
#guard (t2BL 128).toOption == some #[(0, 128)]
#guard (t2BL 96).toOption == some #[(0, 64), (64, 32)]
#guard t2fKappaByText (ofNat 3) 4 == ofNat 81

/-- One matrix of the sub-proof's own, with six rows of cells and two columns. Of U1 to U3 the
sub-proof has only U3. -/
def small : Except String HTailF2 :=
  ({} : HTailF2).shape #[{ name := "x", m := 6, k := 2 }] #[none] #[] #[false, false, true, false]
    160

/-- True if the example has a shape and the shape passes the test. -/
def smallHas (test : HTailF2 → Bool) : Bool :=
  match small with
  | .ok tl => test tl
  | .error _ => false

#guard smallHas fun tl => tl.mz == 6 && tl.NM == 1 && tl.off == #[0] && tl.gtTree == #[1]
#guard smallHas fun tl =>
  tl.ix == { U := #[none, none, some 0, none], PK := #[1], ZZ := 2, BZ := 3, count := 4 }
#guard smallHas fun tl => tl.zzBlocks == 2 && tl.zzRowReads == 4 && tl.zzRowTies == 5
#guard smallHas fun tl => tl.z1.call.n == 11 && tl.z2.call.n == 11 && tl.z2.call.k == 8
#guard smallHas fun tl =>
  (tl.z1.pieces.map fun p => (p.row, p.r0, p.Rp, p.c0, p.Cp, p.CP, p.off, p.a, p.b)) ==
    #[(0, 0, 128, 0, 6, 8, 0, 7, 10), (1, 128, 32, 0, 6, 8, 1024, 5, 8)]
#guard smallHas fun tl =>
  (tl.z2.pieces.map fun p => (p.row, p.c0)) == #[(2, 6), (3, 6)]
#guard smallHas fun tl =>
  tl.f9.dT == 11 && tl.f9.kT == 10 && tl.f9.NT == 2 && tl.f9.rK == 1 && tl.f9.cK == 1
#guard smallHas fun tl => tl.f9.pub == #[1088, 1088]
#guard smallHas fun tl => tl.bzColumns == 2048 && tl.stepF == 256
#guard smallHas fun tl => tl.lins 1 == 61 && tl.equationsF 1 == 768
#guard smallHas fun tl => tl.zzCol 0 1 5 == some 11 && tl.zzCol 0 0 6 == none
#guard smallHas fun tl => tl.foldColumns == 2

/-- The name under which a shape is refused; the empty string if it is not. -/
def refusal (r : Except String HTailF2) : String :=
  match r with
  | .error e => e
  | .ok _ => ""

-- The argument tau (128) differs from the record's tau (160).
#guard refusal (({} : HTailF2).shape #[] #[] #[] #[false, false, true, false] 128) == "hid-tau"
#guard refusal (({} : HTailF2).shape #[] #[] #[] #[false, false, true] 160) == "internal-t2f-lists"
-- A list without a matrix: both lookup calls would hold nothing but padding.
#guard (refusal (({} : HTailF2).shape #[] #[] #[] #[false, false, true, false] 160)).startsWith
  "forest-only-padding"
#guard refusal (({} : HTailF2).shape #[{ name := "x", m := 6, k := 8192 }] #[none] #[]
  #[false, false, true, false] 160) == "hid-k-range"

/-- The example's list of arrays, closed. U3 has four entries. hbLine: the security level in the
statement, in bits. -/
def planned (hbLine : Nat) : Except String (HTailF2 × Fork × Tail2) := do
  let (tl, F, T) ← (← small).addTrees {} {} #[0, 0, 4] #[] 100 hbLine
  pure (tl, F, ← t2Plan F T)

/-- True if the example has a list and the list passes the test. -/
def plannedHas (test : HTailF2 → Fork → Tail2 → Bool) : Bool :=
  match planned 128 with
  | .ok (tl, F, T) => test tl F T
  | .error _ => false

#guard plannedHas fun _ F _ =>
  (F.trees.map fun X => (X.name, X.R, X.K, X.rows.size)) ==
    #[("U3", 1, 4, 1), ("PK0", 2, 2, 1), ("ZZ", 160, 12, 6), ("BZ", 32, 2048, 3)]
#guard plannedHas fun _ _ T => T.planned && (T.nt.map (·.ec)) == #[3, 1, 1, 1]
#guard plannedHas fun tl _ _ => tl.tabLen == #[0, 4] && tl.shp == #[ShP.of 6 2 1]
#guard
  match planned 161 with
  | .error e => e == "policy-tau-hb"
  | .ok _ => false

end OnBytes.Model.TestTail
