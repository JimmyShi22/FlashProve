-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTreesConditions.lean: conditions of FormF.lean and Trees.lean, one at a time, and
forestSize of RoundSizes.lean.

Most guards take an input on which a function's conditions all hold and change it so that one
condition fails. That only one fails is by the choice of the change; the file does not test it. The
list of conditions is that of the Lean text: this file does not test that the list is complete.
Where a routine fails (rowWeights, doorTerms), a guard sees only that it fails, not under which
name. Of Trees.lean, conditions of t2AddN, t2AddP and t2Plan are tested in
OnBytes/Model/TestTailRefusals.lean, conditions of rootInH, t2Batch and doorH in
OnBytes/Model/TestTailNames.lean and TestTreesChannel.lean. No guard here calls smallSize
(RoundSizes.lean). The expected numbers were worked out by hand. No proof is read. The file is not
imported by the program.
-/
import OnBytes.Model.RoundSizes

namespace OnBytes.Model.TestTreesConditions

open OnBytes OnBytes.Model

/-- True if held is true of base and false of each changed copy. -/
def eachBreaks {σ : Type} (held : σ → Bool) (base : σ) (changes : List (σ → σ)) : Bool :=
  held base && changes.all fun change => !held (change base)

/-! ## FormF.lean -/

/-- An owner's record that is complete. -/
def place : PlaceF :=
  { owner := some 1, rootIndex := some 2, sh := some (ShP.of 6 4 2), matrix := some (0, 4, 6),
    hb := 1, mS := 2, lanes := 3, padRows := 2, J := 1, K := 4 }

#guard eachBreaks PlaceF.whole place [
  fun p => { p with owner := none }, fun p => { p with rootIndex := none },
  fun p => { p with sh := none }, fun p => { p with matrix := none }, fun p => { p with hb := 0 }]
-- The six remaining fields, one at a time.
#guard [{ place with mS := 3 }, { place with lanes := 2 }, { place with padRows := 3 },
  { place with J := 2 }, { place with K := 5 }, { place with off := 1 }].all fun r =>
    samePlaceF place r == "P9"
-- The matrix's columns end at the array's last column, or one past it.
#guard samePlaceF { place with matrix := some (1, 3, 6) } { place with matrix := some (1, 3, 6) } ==
  ""
#guard samePlaceF { place with matrix := some (1, 4, 6) } { place with matrix := some (1, 4, 6) } ==
  "P3"
#guard samePlaceF place { place with matrix := some (1, 4, 6) } == "P3"
#guard (ShP.of 7 5 2) ==
  { m := 7, k := 5, mS := 3, J := 1, cJ := 0, aX := 2, a := 2, R := 3, Rd := 0, Rr := 3, K1 := 5,
    Kc := 5 }
-- Two rows of symbols in one row of the array: the symbol in row x of the two and column c is at
-- place 2 c + x, with the weight gam[c] lo[x]. Cell row i belongs to row (i / 3) / 2 of the array.
#guard tieRight { ShP.of 12 2 1 with J := 2 } #[ofNat 2, ofNat 3] #[ofNat 5, ofNat 7] ==
  some #[ofNat 10, ofNat 15, ofNat 14, ofNat 21]
#guard (tieLeft { ShP.of 12 2 1 with J := 2, Rr := 2 } #[ofNat 5, ofNat 7] #[ofNat 2, ofNat 3]).map
    (fun w => [0, 3, 6, 9].map fun i => w.getD i zeroE) ==
  some [ofNat 10, ofNat 15, ofNat 14, ofNat 21]
#guard tieLeft (ShP.of 4 2 1) #[ofNat 2, ofNat 3] #[] == none
#guard tieRight (ShP.of 4 2 1) #[] #[ofNat 5, ofNat 7] == none

/-- A point with four coordinates. -/
def point : Array E := #[ofNat 3, ofNat 5, ofNat 11, ofNat 13]

-- EqRun over all sixteen indices, from every first index, and past the last index.
#guard (List.range 16).all fun first =>
  EqRun.all point first (16 - first) fun i e => e == (eqTab point).getD (first + i) zeroE
#guard (EqRun.start point 5).pre.size == 5 && (EqRun.start point 5).value == eqPlainF point 5
#guard (EqRun.start point 15).next.value == eqPlainF point 0
#guard (EqRun.start point 7).next.idx == 8 && (EqRun.start point 7).next.pre.size == 5
#guard (EqRun.start #[] 0).value == oneE && (EqRun.start #[] 0).next.value == oneE

/-! ## RoundSizes.lean -/

-- v = dT + rK and d = kT + cK.
#guard forestSize { dT := 23, rK := 1, kT := 10, cK := 1, NC := 2 } ==
  { v := 24, d := 11, shifted := true }
#guard forestSize { dT := 23, rK := 1, kT := 10, cK := 1, NC := 1 } ==
  { v := 24, d := 11, shifted := false }

/-! ## The list of arrays -/

/-- An array of 3 rows and 4 columns. -/
def tree : HTree := { R := 3, K := 4 }

#guard eachBreaks (fun (x : N2 × HTree) => t2SameShape x.1 x.2 {} tree) ({}, tree) [
  fun x => (x.1, { x.2 with R := 4 }), fun x => (x.1, { x.2 with K := 5 }),
  fun x => ({ x.1 with ec := 3 }, x.2), fun x => ({ x.1 with a := 2 }, x.2),
  fun x => ({ x.1 with p := some (ShP.of 9 4 1) }, x.2)]
-- Whether the array is an earlier sub-proof's does not count.
#guard t2SameShape { foreign := true } tree {} tree

#guard eachBreaks (fun (x : Fork × Tail2) => t2Open x.1 x.2)
  ({ trees := #[tree] }, { link := true, nt := #[{}] }) [
  fun x => (x.1, { x.2 with link := false }), fun x => (x.1, { x.2 with planned := true }),
  fun x => (x.1, { x.2 with nt := #[] }), fun x => ({ x.1 with trees := #[] }, x.2)]

-- t2FillL fills the rows of listed arrays that have no weights yet, and no other row.
#guard
  let F : Fork :=
    { trees := #[{ tree with rows := #[{}, { L := #[oneE, oneE, oneE, oneE] }] },
                 { tree with rows := #[{}] }] }
  ((t2FillL F { nt := #[{}] }).trees.map fun X => X.rows.map (·.L)) ==
    #[#[Array.replicate 4 zeroE, Array.replicate 4 oneE], #[#[]]]

/-! ## Runs -/

/-- One array with one virtual row, whose L holds the columns 2, .., 5. -/
def trees : Array HTree :=
  #[{ R := 1, K := 6, rows := #[{ L := Array.replicate 4 zeroE, L0 := 2 }] }]

/-- A run of two weights, w[1] and w[2], on the columns 4 and 5. -/
def run : Run2 :=
  { first := 4, coef := ofNat 3, w := #[ofNat 5, ofNat 7, ofNat 11], w0 := 1, n := 2 }

#guard eachBreaks (runFits trees) run [
  fun r => { r with tree := 1 }, fun r => { r with row := 1 },
  -- the weights: w0 past the end; one weight too many
  fun r => { r with w0 := 4, n := 0 }, fun r => { r with w0 := 2 },
  -- the columns: before the first, past the last, one column too many
  fun r => { r with first := 1 }, fun r => { r with first := 7, n := 0 },
  fun r => { r with first := 5 }]
#guard runFits trees { run with w0 := 3, n := 0 } &&
  runFits trees { run with first := 6, n := 0 } && runFits trees { run with first := 2 }
-- 2 * 3 * (7, 11) is added to the last two of the four weights.
#guard ((pushRun (ofNat 2) trees run).map fun t => (t.getD 0 {}).rows.map (·.L)) ==
  some #[#[zeroE, zeroE, ofNat 42, ofNat 66]]
#guard (pushRun (ofNat 2) trees { run with first := 5 }).isNone
#guard (({ trees := trees } : Fork).pushRuns (ofNat 2) #[run, { run with first := 5 }]).isNone
#guard runLoop (ofNat 2) #[ofNat 5, zeroE, ofNat 7] 0 1 3 0 (Array.replicate 4 oneE) ==
  #[oneE, ofNat 11, oneE, ofNat 15]

/-! ## Product forms -/

/-- An array of six rows: three bits. -/
def six : HTree := { R := 6, K := 1 }

/-- Given factors for three bits. -/
def given : HRow :=
  { rowForm := true, rowLo := Array.replicate 3 oneE, rowHi := #[ofNat 2, ofNat 4, ofNat 16] }

#guard eachBreaks (rowFormOK six) given [
  fun r => { r with rowOnes := true }, fun r => { r with rowLo := Array.replicate 2 oneE },
  fun r => { r with rowHi := #[ofNat 2, ofNat 4] }, fun r => { r with rowFirst := 1 },
  fun r => { r with rowPoint := #[oneE] }, fun r => { r with rowLo := #[] },
  fun r => { r with rowHi := #[] }]
#guard eachBreaks (rowFormOK six) { rowForm := true, rowOnes := true } [
  fun r => { r with rowFirst := 2 }, fun r => { r with rowPoint := #[oneE] }]
#guard eachBreaks (rowFormOK six) { rowForm := true, rowPoint := #[oneE, oneE], rowFirst := 4 } [
  fun r => { r with rowFirst := 2 }, fun r => { r with rowFirst := 8 },
  fun r => { r with rowPoint := #[oneE, oneE, oneE, oneE], rowFirst := 0 }]
#guard rowFormOK six { rowForm := true, rowPoint := #[oneE, oneE, oneE] }
#guard rowFactors given 1 == (oneE, ofNat 4)
#guard rowFactors { given with rowLo := #[] } 1 == (zeroE, ofNat 4)
#guard rowFactors { given with rowHi := #[] } 1 == (oneE, zeroE)
#guard rowFactors { rowOnes := true } 2 == (oneE, oneE)
-- The point's last coordinate belongs to bit 0. Above the point the bits of rowFirst are picked.
#guard (List.range 4).map (rowFactors { rowPoint := #[ofNat 9, ofNat 7], rowFirst := 4 }) ==
  [(subE oneE (ofNat 7), ofNat 7), (subE oneE (ofNat 9), ofNat 9), (zeroE, oneE), (oneE, zeroE)]

/-! ## The terms that doorH hands to the chain -/

/-- A context with no rounds. -/
def noRounds : Ctx := { ch := { dry := false, entries := [] } }

/-- What a routine returns on an empty state, if it does not fail. -/
def result {α : Type} (x : SubM α) : Option α := ((x {}).outcome noRounds).map (·.1.1)

/-- The powers of 2 on six rows, written out and as a product form. -/
def powers2 : HRow :=
  { given with coef := #[ofNat 1, ofNat 2, ofNat 4, ofNat 8, ofNat 16, ofNat 32], L := #[ofNat 5] }

#guard (result (rowWeights six powers2)).isSome
-- In the first two guards one written-out weight differs from the product form. In the third the
-- form itself is not well formed.
#guard (result (rowWeights six { powers2 with coef := powers2.coef.set! 5 (ofNat 33) })).isNone
#guard (result (rowWeights six { powers2 with coef := powers2.coef.set! 0 (ofNat 2) })).isNone
#guard (result (rowWeights six { powers2 with rowFirst := 1 })).isNone

/-- The number of terms that doorTerms makes for an array of six rows with the one virtual row r. -/
def termsOf (r : HRow) : Option Nat :=
  (result (doorTerms 3 "A" { six with rows := #[r] })).map (·.size)

#guard termsOf powers2 == some 1
#guard termsOf { powers2 with rowForm := false } == some 6
#guard termsOf { powers2 with coef := powers2.coef.push oneE } == none
#guard termsOf { powers2 with L := #[ofNat 5, ofNat 5] } == none
#guard termsOf { powers2 with L0 := 1 } == none
-- A row without a product form: term i carries the weight of row i. That it picks row i, and its
-- column weights, are compared for i = 5 only.
#guard (result (doorTerms 3 "A" { six with rows := #[{ powers2 with rowForm := false }] })).any
  fun t => (t.map fun x => (x.born, x.array, x.scale)) ==
      (Array.range 6).map (fun i => (3, "A", ofNat (2 ^ i))) &&
    (t.getD 5 {}).onRows.lo == (pickIndex 3 5).lo &&
    (t.getD 5 {}).onRows.hi == (pickIndex 3 5).hi &&
    (t.getD 5 {}).onColumns.values == some #[ofNat 5]

end OnBytes.Model.TestTreesConditions
