-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/SelfTests.lean: the smallness test's two tests of the program on itself
as plain functions on data.

They are typed after `HTailF2.selfTestF` (OnBytes/Model/Tail.lean:1135-1159) and
`HTailF2.tileSelfTestF` (:1589-1622), line for line, and call the program's pure routines by name
(`weightsOf`, `noneZero`, `allBelow`; `wants`, `forestHeld`, `callHeld`, `piecesTile`, `pointsHeld`,
`pieceWeightsHeld`, `tieShapeHeld`, `tieWeightsHeld`, `planesShapeHeld`, `planesWeightsHeld`,
`readShapeHeld`, `readWeightsHeld`). They close no round, read no view and leave the state as it is.

Main names:
  `selfUnits`, `selfDigits`, `selfLinked`, `selfPlanes`, `selfSymbols`: the five conjuncts of "no weight
    that must not be 0 is 0"; `selfSlots`: the comparison of the test's own slots.
  `selfTestP tl nU F`: the first test: four guards.
  `rkSelfTestP tl F`: the test by a second computation: eleven guards.

Refusals: a guard with a name in the program keeps that name, and "routine:line" of the program's text
stands behind it; a guard without a name has "routine:line" alone. So each guard has a name of its own.
There is no dry run: a test on values (`testAs`) refuses as a test on public numbers (`mustAs`) does.

Kin: `OnBytes.K.Kc.still (tl.selfTest nU)`, `still tl.rkSelfTest` (OnBytes/K/Kc/Quiet.lean,
TailQuiet.lean): the program's routines themselves, run from an empty context, without a name of
refusal.
Not claimed: no law is stated here. By the program's own word these tests are meant to fail on no file.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Model.Tail

set_option autoImplicit false

namespace VerifiableInference.Desc.First.TailClaims
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

/-- No entry of a table U1, U2, U3 has the weight 0. -/
def selfUnits (tl : HTailF2) (nU : Array Nat) (F : Fork) : Bool :=
  (List.range 3).all fun n =>
    match tl.ix.U.getD n none with
    | none => true
    | some t =>
      let Kw := (F.trees.getD t {}).K
      allBelow (nU.getD n 0) fun x =>
        !isZeroE ((weightsOf F t (x / Kw)).getD (x % Kw) zeroE)

/-- No digit's weight on the pieces' rows of ZZ is 0. -/
def selfDigits (tl : HTailF2) (F : Fork) : Bool :=
  let nb := tl.zzBlocks
  (List.range nb).all fun b =>
    noneZero (weightsOf F tl.ix.ZZ b) 0 tl.mz &&
      noneZero (weightsOf F tl.ix.ZZ (nb + b)) tl.mz tl.mz

/-- No weight on the reads' row and on the ties' row of ZZ is 0. -/
def selfLinked (tl : HTailF2) (F : Fork) : Bool :=
  noneZero (weightsOf F tl.ix.ZZ tl.zzRowReads) 0 (2 * tl.mz) &&
    noneZero (weightsOf F tl.ix.ZZ tl.zzRowTies) 0 (2 * tl.mz)

/-- No weight on the three rows of BZ is 0. -/
def selfPlanes (tl : HTailF2) (F : Fork) : Bool :=
  (List.range 3).all fun r => noneZero (weightsOf F tl.ix.BZ r) 0 tl.bzColumns

/-- No weight on a symbol array is 0. -/
def selfSymbols (tl : HTailF2) (F : Fork) : Bool :=
  (List.range tl.NM).all fun mu =>
    let s := tl.shp.getD mu {}
    noneZero (weightsOf F (tl.gtTree.getD mu 0) 0) 0 (s.J * s.k)

/-- The coefficients of the test's own slots are those that were kept. -/
def selfSlots (tl : HTailF2) (F : Fork) : Bool :=
  F.LS.extract tl.slotA tl.slotB == tl.lsTail

/-- **The first test.** -/
def selfTestP (tl : HTailF2) (nU : Array Nat) (F : Fork) : Except String Unit := do
  unless nU == tl.nUF do throw "selfTestF:1156"
  unless selfUnits tl nU F && selfDigits tl F && selfLinked tl F && selfPlanes tl F &&
      selfSymbols tl F do
    throw "internal-t2f-untyped selfTestF:1157"
  unless tl.lsTail.size == tl.slotB - tl.slotA do throw "internal-f-tail-slot selfTestF:1158"
  unless selfSlots tl F do throw "internal-f-tail-slot selfTestF:1159"

/-- **The test by a second computation.** -/
def rkSelfTestP (tl : HTailF2) (F : Fork) : Except String Unit := do
  let some g := tl.heard | throw "tileSelfTestF:1590"
  let some jo := tl.joinObj9 | throw "tileSelfTestF:1591"
  let some (nbW, W) := tl.wants | throw "tileSelfTestF:1592"
  let rowsZZ := (F.trees.getD tl.ix.ZZ {}).rows.size
  unless rowsZZ == 2 * nbW + 2 && tl.forestHeld g && [0, 1].all (tl.callHeld g nbW) do
    throw "internal-t2f-untiled tileSelfTestF:1594"
  unless tl.piecesTile F W do throw "internal-t2f-untiled tileSelfTestF:1596"
  unless tl.pointsHeld g do throw "internal-t2f-untiled tileSelfTestF:1597"
  let kappa := t2fKappaByText F.theta jo
  unless W.all (tl.pieceWeightsHeld F g kappa) do
    throw "internal-t2f-untiled tileSelfTestF:1598"
  let T := F.trees.getD tl.ix.ZZ {}
  unless (T.rows.getD (2 * nbW) {}).coef.size == tl.tau &&
      (T.rows.getD (2 * nbW + 1) {}).coef.size == tl.tau &&
      (T.rows.getD (2 * nbW + 1) {}).L.size == 2 * tl.mz &&
      tl.gamX.size == tl.NM && tl.gamV.size == tl.NM &&
      (List.range tl.NM).all (tl.tieShapeHeld F) &&
      tl.shp.foldl (fun n s => n + s.m) 0 == tl.mz && tl.planesShapeHeld F g do
    throw "internal-f-tie-weights tileSelfTestF:1603"
  let c4 := (T.rows.getD (2 * nbW) {}).coef
  let c5 := (T.rows.getD (2 * nbW + 1) {}).coef
  let L5 := (T.rows.getD (2 * nbW + 1) {}).L
  unless ((List.range tl.tau).all fun u =>
        c4.getD u zeroE == powE F.theta u && c5.getD u zeroE == c4.getD u zeroE) &&
      (List.range tl.NM).all (tl.tieWeightsHeld F L5) && tl.planesWeightsHeld F g jo do
    throw "internal-f-tie-weights tileSelfTestF:1612"
  let L4 := (T.rows.getD (2 * nbW) {}).L
  unless tl.readShapeHeld L4 do throw "internal-f-read-weights tileSelfTestF:1621"
  unless tl.readWeightsHeld F L4 do throw "internal-f-read-weights tileSelfTestF:1622"

end VerifiableInference.Desc.First.TailClaims
