-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTailRun.lean: the claims of the smallness test, run on fixed challenges.

The smallness test of a sub-proof computes most weights of its claims twice. HTailF2.objectsF and
coefficientsF set them. HTailF2.tileSelfTestF computes them again in another way and compares; its
docstring says which weights it compares entry by entry. Here both run on a small example: one
matrix with six rows of cells and two columns, one table with two segments, and challenges that are
fixed numbers. No proof is read, and nothing is said about a prover. The example shows that the two
computations agree, that every column that a virtual row is meant to read has a weight that is not 0
(selfTestF), and that each written-out vector of row weights equals its product form. It also shows
that the tests fail for each of twelve changes of one weight or number (spoils), and that every
public condition holds in a dry run, in which all values are 0.

Of the reads only the weights on ZZ have a second computation (readWeightsAgain); those on U3 and
the constant have none. So the tie and the reads are also evaluated on the entries that an honest
prover would commit to for a small matrix of integers. This file computes these entries itself
(honest); no prover program made them. The equation holds. It fails for each of three changed
entries, one in each array that these claims read.

The terms (tie, read, table, the arrays U1 to U3, PK, PX, ZZ, BZ) are explained in
OnBytes/Model/Tail.lean (the docstring of HTailF2 says where); dry run in OnBytes/Iop/Ground.lean.

The file is not imported by the program.
-/
import OnBytes.Model.Tail

namespace OnBytes.Model.TestTailRun

open OnBytes OnBytes.Model

/-- A fixed element of the extension field; 0 for the dry run. -/
def el (dry : Bool) (n : Nat) : E :=
  if dry then zeroE else E.mk3 (fOfNat (7 * n + 3)) (fOfNat (n * n + 1)) (fOfNat (n + 5))

/-- count fixed elements. -/
def els (dry : Bool) (seed count : Nat) : Array E :=
  (Array.range count).map fun i => el dry (seed + i)

/-- The example's list of arrays. U3 has four entries: two columns times two segments. -/
def planned : Except String (HTailF2 × Fork) := do
  let tl ← ({} : HTailF2).shape #[{ name := "x", m := 6, k := 2 }] #[none] #[]
    #[false, false, true, false] 160
  let (tl, F, _) ← tl.addTrees {} {} #[0, 0, 4] #[] 100 128
  pure (tl, F)

/-- One table on U3: segments of three rows of cells. -/
def funs (dry : Bool := false) : Array HFun :=
  #[{ mat := 0, len := 3, phi := els dry 50 3, tree := 2, start := 0 }]

/-- What the lookup would have received and drawn: fixed numbers in the right shapes. Each of the
two calls has 2^11 keys in one tree, so the point of each call (zk) is zx. -/
def heard (dry : Bool) (tl : HTailF2) : Forest.Heard :=
  let el := el dry
  let els := els dry
  let zy := els 100 1
  let zx := els 200 11
  { shape := tl.f9, theta := el 1, alpha := el 2,
    rows := Array.replicate (Forest.lins tl.f9) (Aff.slot 8),
    leaves :=
      { started := true, first := 0, eps := el 3, claim := el 4,
        vars := #[OnBytes.Psc.Weight.plain 3], r := #[el 5] },
    leavesA := el 6, sBit := 9, zx := zx, zy := zy,
    e := #[subE oneE (zy.getD 0 zeroE), zy.getD 0 zeroE], cEnd := Aff.slot 7,
    zb0 := els 300 16, zb1 := els 400 16, zk := #[zx, zx] }

/-- The smallness test's state after its messages, with fixed entries -1, 0, 1 in place of the drawn
matrix C. -/
def afterMessages (tl : HTailF2) (dry : Bool := false) : HTailF2 :=
  { tl with
    funClosed := true, funs := funs dry,
    cfF := (Array.range 320).map fun i => if dry then 0 else Int.ofNat ((i * i + i / 3) % 3) - 1,
    cfFirst := #[0, 2], foldDrawn := 1, slotA := 0, slotB := 10, heard := some (heard dry tl) }

/-- The sub-proof's state after the batching element is drawn. The plan has only the claims of the
smallness test. -/
def afterDraw (tl : HTailF2) (F : Fork) (dry : Bool := false) : Fork :=
  let claims := tl.lins 2
  { F.fillL.slots 10 with
    planClaimsF := claims, theta := el dry 9, thetaDrawnF := true,
    kapMapF := Array.replicate claims false }

/-- A context (Ctx, OnBytes/Iop/Ground.lean) with no rounds: the routines under test receive and
draw nothing. -/
def noRounds (dry : Bool) : Ctx := { ch := { dry := dry, entries := [] } }

/-- Adds the claims. dry: as a dry run, with all values 0. -/
def claimsAdded (dry : Bool) : Option (HTailF2 × Fork) :=
  match planned with
  | .error _ => none
  | .ok (tl0, F) =>
    let course : SubM HTailF2 := do
      let tl ← (afterMessages tl0 dry).objectsF (funs dry)
      SubM.must ((← SubM.claims) == tl0.lins 2 && tl.foldAllTakenF)
      SubM.must (tl.equationsLaidF == some (tl0.equationsF 2))
      pure tl
    ((course (afterDraw tl0 F dry)).outcome (noRounds dry)).map (·.1)

/-- Runs all tests on the weights. True if everything passes. -/
def testsPass (dry : Bool) (tl : HTailF2) (F : Fork) : Bool :=
  let course : SubM Unit := do
    tl.selfTestF #[0, 0, 4]
    tl.coefficientsF
    tl.tileSelfTestF
    for X in (← get).trees do
      for r in X.rows do
        let _ ← rowWeights X r
  ((course F).outcome (noRounds dry)).isSome

/-! ## The ties and the reads on honest data -/

/-- The cell in row i, column c of the example's matrix of cells: an integer from -3 to 3. -/
def cell (i c : Nat) : Int := Int.ofNat ((5 * i + 3 * c) % 7) - 3

/-- Combination u of row i of cells under the fixed matrix tl.cfF (afterMessages), plus beta. It is
not negative. -/
def moved (tl : HTailF2) (i u : Nat) : Nat :=
  ((List.range 2).foldl (fun s c => s + tl.cfF.getD (c * 160 + u) 0 * cell i c) (2 ^ lbz)).toNat

/-- What an honest prover would have committed to, computed here; no prover program made it. The
value is entry (r, c) of array t. U3 holds, for column c and segment sg, the sum of the segment's
cells under the table's weights. PK0 holds the symbols. ZZ holds the low digits, then the high
digits, of the combinations plus beta. BZ is given as 0: the tie and the reads put no weight on it.
One entry of array number spoiled is changed by 1. With spoiled = 3 all entries are honest. -/
def honest (tl : HTailF2) (spoiled t r c : Nat) : E :=
  if t == 0 then
    (List.range 3).foldl
      (fun s j =>
        let weight := ((funs false).getD 0 {}).phi.getD j zeroE
        addE s (mulE weight (ofInt (cell (c % 2 * 3 + j) (c / 2)))))
      (if spoiled == 0 && c == 3 then oneE else zeroE)
  else if t == 1 then
    ofInt ((List.range 3).foldl (fun s l => s + (2 : Int) ^ (20 * l) * cell (3 * r + l) c)
      (if spoiled == 1 && r == 1 && c == 0 then 1 else 0))
  else if t == 2 then
    let digit := if c < 6 then moved tl c r % 1024 else moved tl (c - 6) r / 1024
    ofNat (digit + if spoiled == 2 && r == 5 && c == 8 then 1 else 0)
  else zeroE

/-- The left side of the one equation on given entries: the sum over all virtual rows of coef[r] *
L[c] * entry t r c, plus c0. The part on the slots is left out; the tie and the reads put no weight
there. -/
def valueOn (F : Fork) (entry : Nat → Nat → Nat → E) : E :=
  (List.range F.trees.size).foldl
    (fun s t =>
      let X := F.trees.getD t {}
      X.rows.foldl
        (fun s row =>
          (List.range X.K).foldl
            (fun s c =>
              let w := row.L.getD c zeroE
              if isZeroE w then s
              else
                (List.range X.R).foldl
                  (fun s r => addE s (mulE (mulE (row.coef.getD r zeroE) w) (entry t r c))) s)
            s)
        s)
    F.c0

/-- Adds the tie, the two reads, or both, and no other claim. Returns the equation's value on the
honest entries, of which one in array number spoiled is changed. -/
def valueOf (tie reads : Bool) (spoiled : Nat) : Option E :=
  match planned with
  | .error _ => none
  | .ok (tl0, F) =>
    let course : SubM E := do
      let tl ← (afterMessages tl0).weightsF
      if tie then tl.linTie 0
      if reads then
        let table := (funs false).getD 0 {}
        let sums := mulE (sumE table.phi) (sumE tl.vt)
        tl.linRead table 0 0 sums
        tl.linRead table 1 1 sums
      tl.coefficientsF
      pure (valueOn (← get) (honest tl spoiled))
    let start : Fork :=
      { afterDraw tl0 F with planClaimsF := 3, kapMapF := Array.replicate 3 false }
    ((course start).outcome (noRounds false)).map (·.1.1)

/-- True if there is a value and it is not 0. -/
def fails (v : Option E) : Bool := v.isSome && v != some zeroE

#guard valueOf true true 3 == some zeroE
#guard valueOf true false 3 == some zeroE
#guard valueOf false true 3 == some zeroE
-- An entry of U3 is read only by the reads, a symbol only by the tie, a digit by both.
#guard fails (valueOf false true 0) && valueOf true false 0 == some zeroE
#guard fails (valueOf true false 1) && valueOf false true 1 == some zeroE
#guard fails (valueOf true false 2) && fails (valueOf false true 2)

/-! ## Spoiled weights -/

/-- Adds 1 to column weight c of virtual row r of array t. -/
def nudge (t r c : Nat) (F : Fork) : Fork :=
  HTailF2.onRow F t r fun row => { row with L := row.L.modify c fun v => addE v oneE }

/-- Changes of one weight, or of one number that the second computation reads. -/
def spoils : List ((HTailF2 → HTailF2) × (Fork → Fork)) := [
  (fun tl => { tl with bitFactor9 := el false 77 }, id),
  (fun tl => { tl with joinObj9 := tl.joinObj9.map (· + 1) }, id),
  (fun tl => { tl with gamX := tl.gamX.modify 0 fun g => g.modify 1 fun v => addE v oneE }, id),
  (fun tl => { tl with lsTail := tl.lsTail.modify 3 fun v => addE v oneE }, id),
  (id, nudge 1 0 1), (id, nudge 2 0 3), (id, nudge 2 0 7), (id, nudge 2 3 11), (id, nudge 2 5 4),
  (id, nudge 3 0 2047), (id, nudge 3 1 5), (id, nudge 3 2 31)]

#guard (claimsAdded false).any fun (tl, F) =>
  testsPass false tl F && spoils.all fun s => !testsPass false (s.1 tl) (s.2 F)
#guard (claimsAdded true).any fun (tl, F) => testsPass true tl F

end OnBytes.Model.TestTailRun
