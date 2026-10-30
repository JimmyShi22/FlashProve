-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestWeights.lean: tests of OnBytes/Model/Weights.lean, run when this file compiles.

The program does not import this file.

What is tested, on small made-up shapes of a model and several numbers of column bits:
 1. The definition. A claim says that the weights of a unit, each times a product of factors, sum to
    a value. For every cell of every unit, the claim's value on the cell's column (wsEpsT) times its
    weight on the cell's row (wsGamma) must be the product of the factors at the cell's indices,
    times 256^digit. At every place of the unit's rows that holds no cell the product must be 0.
    The rule for where a cell lies is written here a second time (place). It reads each group's
    fields t, cb0, z, high and left from the layout under test. OnBytes/Model/TestWeightsGiven.lean
    compares those fields with the C++ verifier's at one other layout (smallKit, 11 column bits).
 2. The extension. wsEpsT at a made-up point is the multilinear extension of its values on the
    columns.
 3. The sum. For every unit, wsGammaAdd adds the claim's coefficients to the unit's rows of a vector
    of ones and leaves every other row as it was.
 4. Numbers of layouts, and refusals of WsLay.build, wsClaimShape and wsGammaAdd. No two units of a
    layout have the same kind and layer.
verifier/tests/weights_twin_test.cpp tests properties 1 and 2 on the C++ verifier.
-/
import OnBytes.Model.Weights

namespace OnBytes.Model.TestWeights

/-- A made-up element of the extension field, from a number. The multiplier and the increment are
those of the linear congruential generator of D. E. Knuth's MMIX, a publicly known generator, as in
verifier/tests/weights_twin_test.cpp. They protect nothing here. -/
def madeUp (n : Nat) : E :=
  let a := (n * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  let b := (a * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  let c := (b * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  E.mk3 (UInt64.ofNat (a / 2048 % 1000003)) (UInt64.ofNat (b / 2048 % 1000003))
    (UInt64.ofNat (c / 2048 % 1000003))

/-- n made-up elements. -/
def madeUpList (seed n : Nat) : Array E := Array.ofFn (n := n) fun i => madeUp (seed * 4099 + i.val)

/-- A claim's factor at one index of its group, by the definition of WsFac. -/
def factorAt (g : WsGrp) (f : WsFac) (index : Nat) : E :=
  if g.cls == 'A' then f.AV.getD index zeroE
  else
    (List.range g.z).foldl
      (fun r b =>
        let x := f.pt.getD (g.z - 1 - b) zeroE
        mulE r (if index / 2 ^ b % 2 == 1 then x else subE oneE x))
      (f.HV.getD (index / 2 ^ g.z) zeroE)

/-- Where an index of a group goes: its part of the column's number, and its part for the row. -/
def place (g : WsGrp) (index : Nat) : Nat × Nat :=
  if g.cls == 'A' then
    if 0 < g.t then (index * 2 ^ g.cb0, 0) else (0, index)
  else
    let lo := index % 2 ^ g.z
    let hi := index / 2 ^ g.z
    let taken := if g.high then lo / 2 ^ (g.z - g.t) else lo % 2 ^ g.t
    let rest := if g.high then lo % 2 ^ (g.z - g.t) else lo / 2 ^ g.t
    (taken * 2 ^ g.cb0, hi * 2 ^ (g.z - g.t) + rest)

/-- All cells of some groups. The groups come in the order of their places in the row's number, the
most significant first; the caller reverses the unit's list. acc holds the cells so far. A cell is
its column, its row and the product of its factors. -/
def cells : List (WsGrp × WsFac) → List (Nat × Nat × E) → List (Nat × Nat × E)
  | [], acc => acc
  | (g, f) :: rest, acc =>
    cells rest (acc.flatMap fun (col, row, v) =>
      (List.range g.R).map fun i =>
        let p := place g i
        (col + p.1, row * g.left + p.2, mulE v (factorAt g f i)))

/-- A claim with made-up factors on unit number ui. -/
def claimOn (u : WsUnit) (ui : Nat) : WsClaim where
  ui := ui
  f := u.g.zipIdx.map fun (g, k) =>
    if g.cls == 'A' then { AV := madeUpList (100 * ui + k) g.R }
    else { HV := madeUpList (100 * ui + k) g.o, pt := madeUpList (100 * ui + k + 50) g.z }

/-- The point whose coordinates are the bits of col, the highest column bit first. -/
def pointOf (lk col : Nat) : Array E :=
  Array.ofFn (n := lk) fun i => if col / 2 ^ (lk - 1 - i.val) % 2 == 1 then oneE else zeroE

/-- Tests 1 to 3 on one unit. -/
def unitOK (lay : WsLay) (ui : Nat) : Bool :=
  match lay.U[ui]? with
  | none => false
  | some u =>
    let c := claimOn u ui
    let ka := madeUp (7 * ui + 1)
    let wgt := madeUp (7 * ui + 2)
    let cols := 2 ^ lay.lk
    let gamma := wsGamma u (wsRowPart lay c ka) wgt
    let eps := Array.ofFn (n := cols) fun col => wsEpsT lay c (pointOf lay.lk col.val)
    let start := (List.range u.nlw).map fun l =>
      (0, l, mulE (mulE wgt ka) (ofNat (256 ^ l)))
    let all := cells (u.g.zip c.f).reverse start
    let want := all.foldl (fun (t : Array E) (col, row, v) => t.set! (row * cols + col) v)
      (Array.replicate (u.rows * cols) zeroE)
    let marks := all.foldl
      (fun (t : Array Nat) (col, row, _) => t.modify (row * cols + col) (· + 1))
      (Array.replicate (u.rows * cols) 0)
    let rm := madeUpList (9000 + ui) lay.lk
    let added :=
      match wsGammaAdd (Array.replicate lay.m0 oneE) lay (wsRowPart lay c ka) wgt with
      | .ok G =>
        G.size == lay.m0 && (List.range lay.m0).all fun y =>
          G.getD y zeroE ==
            if u.off ≤ y && y < u.off + u.rows then addE oneE (gamma.getD (y - u.off) zeroE)
            else oneE
      | .error _ => false
    added && (wsClaimShape lay c).isOk && gamma.size == u.rows &&
    all.all (fun (col, row, _) => decide (col < cols) && decide (row < u.rows)) &&
    marks.all (· ≤ 1) &&
    (List.range (u.rows * cols)).all (fun i =>
      mulE (eps.getD (i % cols) zeroE) (gamma.getD (i / cols) zeroE) == want.getD i oneE) &&
    wsEpsT lay c rm == wsDot cols eps (eqTab rm)

/-- A small shape, with D = 32. -/
def shape (L d dh dkv dq f fe NE V : Nat) (moe eh : Bool) : WsShape :=
  wsSetMoe { D := 32, L := L, d := d, dh := dh, dkv := dkv, dq := dq, f := f, fe := fe, NE := NE,
             V := V, eh := if eh then 1 else 0 } moe

/-- Tests 1 to 3 on every unit of a shape's layout. -/
def shapeOK (s : WsShape) (lk : Nat) : Bool :=
  match WsLay.build s lk with
  | .error _ => false
  | .ok lay => (List.range lay.U.size).all (unitOK lay)

/-- Sizes with odd parts; every second layer a mixture of experts. -/
def oddParts : WsShape := shape 2 24 4 8 16 40 12 6 10 true true

/-- Powers of two alone. -/
def powersOfTwo : WsShape := shape 2 16 2 4 8 32 8 4 16 true true

/-- Odd sizes alone: no group of class 'E' has a bit to give. -/
def oddAlone : WsShape := shape 1 3 1 5 7 9 0 0 3 false true

/-- A size of 1 in every place that takes one. -/
def ones : WsShape := shape 2 1 1 1 1 1 1 1 1 true true

#guard shapeOK oddParts 3
#guard shapeOK oddParts 8
#guard shapeOK powersOfTwo 5
#guard shapeOK oddAlone 8
#guard shapeOK ones 1
#guard shapeOK (shape 3 8 2 4 8 12 4 3 0 true false) 2

/-- The numbers of a layout: its units, its rows up to the end of the last unit, and all its rows,
which is the second number rounded up. -/
def numbers (s : WsShape) (lk : Nat) : Option (Nat × Nat × Nat) :=
  match WsLay.build s lk with
  | .error _ => none
  | .ok lay => some (lay.U.size, (lay.U.back?.map fun u => u.off + u.rows).getD 0, lay.m0)

/-- The shape of a small configuration, spelled out here. -/
def smallKit : WsShape :=
  wsSetMoe { D := 2048, L := 8, d := 512, dh := 128, dkv := 256, dq := 512, f := 1024, fe := 512,
             NE := 4, V := 512, eh := 1 } true

-- 66 and 59392 are the C++ verifier's (OnBytes/Model/TestWeightsGiven.lean). The other numbers of
-- layouts below were computed apart from this library, by the rule of WsLay::build in
-- verifier/src/vf_weights_layout.h.
#guard numbers smallKit 11 == some (66, 58120, 59392)
#guard numbers { smallKit with MOE := 0, moe := Array.replicate 8 false } 11
  == some (50, 48896, 49152)

/-- A shape of full size, spelled out here. -/
def fullSize : WsShape :=
  wsSetMoe { D := 2048, L := 48, d := 5120, dh := 128, dkv := 1024, dq := 5120, f := 16384,
             fe := 8192, NE := 128, V := 202048, eh := 1 } true

-- 3,076,096 is also the number of rows that blocks/frame/files.h gives for the full size.
#guard numbers fullSize 18 == some (386, 3076080, 3076096)

/-- True if the layout's number of rows is the least multiple of D that holds all units. -/
def roundedUp (s : WsShape) (lk : Nat) : Bool :=
  match numbers s lk with
  | some (_, rows, m0) => m0 % s.D == 0 && decide (rows ≤ m0) && decide (m0 < rows + s.D)
  | none => false

-- with 1 and 2 column bits the units of oddParts and powersOfTwo fill a multiple of D exactly
#guard [oddParts, powersOfTwo, oddAlone, ones].all fun s =>
  (List.range 8).all fun i => roundedUp s (i + 1)
#guard numbers oddParts 1 == some (18, 23232, 23232)
#guard numbers powersOfTwo 2 == some (18, 4384, 4384)

-- wsSetMoe: no layer, or every second layer, is a mixture of experts
#guard ((wsSetMoe { L := 4 } false).MOE, (wsSetMoe { L := 4 } false).moe)
  == (0, #[false, false, false, false])
#guard ((wsSetMoe { L := 4 } true).MOE, (wsSetMoe { L := 4 } true).moe)
  == (1, #[false, true, false, true])

/-- True if unitOf finds every unit of the layout under the unit's own number. Then no two units
have the same kind and layer. -/
def unitsApart (s : WsShape) (lk : Nat) : Bool :=
  match WsLay.build s lk with
  | .ok lay =>
    (List.range lay.U.size).all fun i => (lay.U[i]?.bind fun u => lay.unitOf u.X u.l) == some i
  | .error _ => false

#guard unitsApart smallKit 11
#guard unitsApart { smallKit with MOE := 0, moe := Array.replicate 8 false } 11
#guard unitsApart fullSize 18
#guard unitsApart oddParts 3
-- a kind that a layer does not have; the embedding and the head stand after the layers
#guard ((WsLay.build smallKit 11).toOption.map fun lay =>
    [lay.unitOf 5 0, lay.unitOf 3 1, lay.unitOf 12 0, lay.unitOf 12 8, lay.unitOf 13 8])
  == some [none, none, none, some 64, some 65]

/-- The name under which a shape is refused. -/
def refusal (s : WsShape) (lk : Nat) : Option String :=
  match WsLay.build s lk with
  | .error e => some e
  | .ok _ => none

#guard refusal smallKit 0 == some "w-shape-lk"
#guard refusal smallKit 21 == some "w-shape-lk"
#guard refusal smallKit 20 == none
#guard refusal { smallKit with D := 64 } 11 == some "shape-D"
#guard refusal { smallKit with L := 9 } 11 == some "shape-words"
#guard refusal { smallKit with L := 0, moe := #[] } 11 == some "shape-words"
#guard refusal { smallKit with L := 4097, MOE := 0, moe := Array.replicate 4097 false } 11
  == some "shape-words"
#guard refusal { smallKit with MOE := 2 } 11 == some "shape-words"
#guard refusal { smallKit with MOE := 0 } 11 == some "internal-shape-moe"
#guard refusal { smallKit with moe := Array.replicate 8 false } 11 == some "internal-shape-moe"
#guard refusal { smallKit with d := 0 } 11 == some "shape-words"
#guard refusal { smallKit with f := 2 ^ 24 + 1 } 11 == some "shape-words"
#guard refusal { smallKit with NE := 0 } 11 == some "shape-words"
#guard [{ smallKit with dh := 0 }, { smallKit with dkv := 0 }, { smallKit with dq := 0 },
    { smallKit with fe := 0 }].map (refusal · 11) == List.replicate 4 (some "shape-words")
#guard refusal { smallKit with eh := 2 } 11 == some "shape-words"
#guard refusal { smallKit with V := 0 } 11 == some "shape-words"
-- with 1 column bit unit 0 has exactly 2^22 rows, which is allowed; the sum with unit 1 is refused
#guard refusal smallKit 1 == some "w-shape-mW"
-- with 4 column bits the units have 7,439,360 rows, more than 2^22 = 4,194,304; with 5 they have
-- 3,719,680
#guard refusal smallKit 4 == some "w-shape-mW"
#guard refusal smallKit 5 == none
-- with dh = 256 and 1 column bit unit 0 alone has 2^23 rows
#guard refusal { smallKit with dh := 256 } 1 == some "w-shape-mW"

/-- The name under which the layout of a request's check is refused. -/
def refusalOf (s : WsShape) (p3 : Bool) (lk : Nat) : Option String :=
  match wsLayOf s p3 lk with
  | .error e => some e
  | .ok _ => none

#guard (wsLayOf { smallKit with eh := 0, MOE := 0, moe := #[] } true 11).toOption.map (·.m0)
  == some 59392
#guard refusalOf smallKit true 9 == none
#guard refusalOf smallKit true 8 == some "hid-vocab-cols"
#guard refusalOf { smallKit with V := 1 } true 11 == some "w-list-token-factor"
#guard refusalOf { smallKit with V := 2 } true 11 == none
#guard refusalOf { smallKit with V := 0 } true 11 == some "w-list-token-factor"
#guard (tokenFactorUnits { lk := 3, U := #[{ X := 12, g := [WsLay.E_ "x" 8 true] }] }).isOk == false
#guard (tokenFactorUnits { lk := 3, U := #[{ X := 13, g := [WsLay.A_ "x" 8] }] }).isOk == false
#guard (tokenFactorUnits { lk := 3, U := #[{ X := 11, g := [WsLay.A_ "x" 8] }] }).isOk

/-- The layout for the tests of a claim's sizes. Its unit 0 has the groups hd and cd of class 'A'
and kk of class 'E'. -/
def sizesLay : WsLay := (WsLay.build oddParts 3).toOption.getD {}

/-- A claim on unit 0 of sizesLay with the right sizes. -/
def sizesClaim : WsClaim := claimOn (sizesLay.U.getD 0 {}) 0

/-- The name under which a claim's sizes are refused; none if they are not. -/
def sizesName (c : WsClaim) : Option String :=
  match wsClaimShape sizesLay c with
  | .error e => some e
  | .ok _ => none

/-- sizesName of sizesClaim with factor number k changed. -/
def factorName (k : Nat) (change : WsFac → WsFac) : Option String :=
  sizesName { sizesClaim with
    f := sizesClaim.f.zipIdx.map fun (x, i) => if i == k then change x else x }

#guard (sizesLay.U.getD 0 {}).g.map (·.cls) == ['A', 'A', 'E']
#guard factorName 0 id == none
-- class 'E': each of its three sizes
#guard factorName 2 (fun x => { x with HV := x.HV.push oneE }) == some "internal-claim-factors"
#guard factorName 2 (fun x => { x with pt := x.pt.push oneE }) == some "internal-claim-factors"
#guard factorName 2 (fun x => { x with AV := #[oneE] }) == some "internal-claim-factors"
-- class 'A': each of its three sizes
#guard factorName 0 (fun x => { x with AV := x.AV.pop }) == some "internal-claim-factors"
#guard factorName 0 (fun x => { x with HV := #[oneE] }) == some "internal-claim-factors"
#guard factorName 0 (fun x => { x with pt := #[oneE] }) == some "internal-claim-factors"
-- a factor too few; a unit that is not in the layout
#guard sizesName { sizesClaim with f := sizesClaim.f.dropLast } == some "internal-claim-factors"
#guard sizesName { sizesClaim with ui := sizesLay.U.size } == some "internal-claim-unit"

/-- The name under which wsGammaAdd refuses what is left of a claim, on a vector of n rows. -/
def gammaName (n : Nat) (c : WsRecClaim) : Option String :=
  match wsGammaAdd (Array.replicate n zeroE) sizesLay c oneE with
  | .error e => some e
  | .ok _ => none

/-- What is left of sizesClaim. -/
def sizesLeft : WsRecClaim := wsRowPart sizesLay sizesClaim oneE

/-- The row after the last row of unit 0. -/
def sizesEnd : Nat := (sizesLay.U.getD 0 {}).off + (sizesLay.U.getD 0 {}).rows

#guard gammaName sizesEnd sizesLeft == none
-- a vector that ends before the unit; a unit that is not in the layout
#guard gammaName (sizesEnd - 1) sizesLeft == some "internal-gamma-rows"
#guard gammaName sizesEnd { sizesLeft with ui := sizesLay.U.size } == some "internal-gamma-rows"
-- a factor too many, which changes no size; a factor that is too long
#guard gammaName sizesEnd { sizesLeft with f := sizesLeft.f ++ [{}] } == some "internal-gamma-rows"
#guard gammaName sizesEnd { sizesLeft with
    f := sizesLeft.f.map fun x => { x with HV := x.HV.push oneE } } == some "internal-gamma-rows"

-- every name that a test above expects is in the file's list, and the list has no other name
#guard Weights.names.length == 10 && ["w-shape-lk", "shape-D", "shape-words", "internal-shape-moe",
    "w-shape-mW", "hid-vocab-cols", "w-list-token-factor", "internal-claim-factors",
    "internal-claim-unit", "internal-gamma-rows"].all Weights.names.contains

end OnBytes.Model.TestWeights
