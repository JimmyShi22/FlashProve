-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/SmallPlaceBase.lean: the small example place placePadInMain, whose one row is
over the base field and holds the pad, with executable checks of the sender and its simulator
against values written by hand from the small example padInMain of the general model.
Terms: Johnson/SendSim/At/Sim.lean; for the small examples, Johnson/SendSim/At/SmallPlaces.lean.
Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. Definitions and #guard checks; no theorem. placePadInMain has one oracle
message: one main row over the base field, with the code (3, 4, 1), no mask row, and one answer, in
the extension field. Entry 0 of the row is the datum d; entries 1 to 3 are the pad. The matching
example padInMain has a datum and a pad of three coins in one row, and three answers. The following
is checked by #guard when the file is compiled.
  (1) The job fits its place (sendFits), and K1's test on the plan accepts (K1.planOk). The sender
      takes 4 coins of the base field and none of the extension field.
  (2) Which coin is placed where: the tail t, then the pad's coins p₀, p₁, p₂ at the last three
      entries.
  (3) At concrete coins and seeds and three lists of queried positions, the simulator outputs shownR
      at no data, and the honest sender, executed by the framework's play, discloses shownR at its
      data.
  (4) Formulas. With the evaluation point ζ, the symbol is t + ζ d + ζ² p₀ + ζ³ p₁ + ζ⁴ p₂ in the
      base field. With the seed (z₀, z₁, β) and the generator θ of the extension field, the answer
      is (1 - z₀)(1 - z₁) d + β (p₀ + p₁ θ + p₂ θ²).
  (5) Read over the base field the one answer is three. Coordinate i of the answer is
      a i * d + Σ k, M i k * p k, where a i is coordinate i of (1 - z₀)(1 - z₁) and M i k is
      coordinate i of β θ ^ k. These are the three answers of padInMain at these weights (by
      inspection, not proved: this file does not import padInMain).
  (6) The checks can fail: the check of (4) is repeated three times, each with one thing modified,
      and then differs.

Limits. The checks are evaluations at concrete values; no distribution is named. One place, and one
family of coins, data and seeds. The expected values were written by the same hand as the small
example with which they are compared, so they are not an independent check.

How it fits. The checks are those of Johnson/SendSim/At/SmallPlaces.lean at one more place.
-/
import Johnson.SendSim.At.SmallPlaces

set_option autoImplicit false

namespace OnBytes.SendSim.At.Small
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- The small example place with one main row over the base field, of four entries and a tail of one
entry, no mask row and one answer. -/
def placePadInMain : K1.Par :=
  smallPar ⟨#[⟨3, 4, 1⟩], #[]⟩
    [{ code := 0, mainRows := 1, mainDeg := 1, maskRows := 0, maskCode := 0, answers := 1 }]

#guard sendFits placePadInMain noRide && K1.planOk placePadInMain
#guard dueR placePadInMain noRide == ⟨4, 0⟩
#guard placePadInMain.trees.length == 1 && placePadInMain.seeds == 1 &&
  placePadInMain.coordinates == 2

-- which coin is placed where: the tail; no coin at the datum's entry; the pad's three coins
#guard (listOfN 1 fun q => (Slice.ofF ((rowsR placePadInMain noRide (fun _ _ _ => none)
    (countCoins _) 0).mainTlF 0 q)).toNat) == [1]
#guard (listOfN 4 fun j => (Slice.ofF ((rowsR placePadInMain noRide (fun _ _ _ => none)
    (countCoins _) 0).mainF 0 j)).toNat) == [0, 2, 3, 4]

/-- Coin number i of the base field in writtenCoins. -/
def baseCoin (i : Nat) : GF := toF (300 + 7 * i).toUInt64
/-- The concrete datum. -/
def baseDatum : GF := toF 2000
/-- The data with the one entry baseDatum, at oracle message 0, main row 0, entry 0. -/
def baseData : Nat → Nat → Nat → Option (GF ⊕ GE) := fun k r j =>
  if k == 0 && r == 0 && j == 0 then some (.inl baseDatum) else none

-- the simulator outputs shownR at no data
#guard [[[[5]], []], [[[1, 5]], []], []].all fun asks => tellsOk placePadInMain noRide asks
-- the sender, executed by play at its data, discloses shownR at these data
#guard [[[[5]], []], [[[1, 5]], []], []].all fun asks =>
  ((play ((sendPart (V := Empty) (⟨placePadInMain, 0, noRide, fun _ _ => baseData⟩ :
      SendJob Unit Unit)).steps "" smallAddr (roundsOf placePadInMain) none
      (writtenCoins _, (), ())) smallSeeds [] standIn).toOption.map fun y => shownOf y.1 asks) ==
    some (shownR placePadInMain 0 noRide baseData smallSeeds asks (writtenCoins _))

/-- The generator of the extension field. -/
def genOfE : GE := toE (0, 1, 0)
def pointOfF (a x : Nat) : GF := toF (Fmt.M1.point a x)
def liftToE (x : GF) : GE := algebraMap GF GE x

/-- The expected value of shownR: at each position in xs the one word of the symbol s x; then the
answer y. -/
def baseExpected (xs : List Nat) (s : Nat → GF) (y : GE) : List Shown :=
  [⟨[], [xs.map fun x => (x, [Slice.ofF (s x)])]⟩, ⟨[(Said.answer y).got], []⟩]

/-- The pad's value: the coins number a, b, c times the powers 0, 1, 2 of the generator. -/
def padValue (a b c : Nat) : GE :=
  liftToE (baseCoin a) + liftToE (baseCoin b) * genOfE + liftToE (baseCoin c) * genOfE ^ 2
/-- The row's symbol at position x, where the pad's coins have the numbers a, b, c. -/
def baseSymbol (a b c x : Nat) : GF :=
  baseCoin 0 + pointOfF 3 x * baseDatum + pointOfF 3 x ^ 2 * baseCoin a +
    pointOfF 3 x ^ 3 * baseCoin b + pointOfF 3 x ^ 4 * baseCoin c

def baseAnswer : GE :=
  (1 - fieldZ0) * (1 - fieldZ1) * liftToE baseDatum + fieldFactor * padValue 1 2 3

#guard shownR placePadInMain 0 noRide baseData smallSeeds [[[5, 2]], []] (writtenCoins _) ==
  baseExpected [5, 2] (baseSymbol 1 2 3) baseAnswer

/-- Coordinate i of an element of the extension field. -/
def coordinateAt (x : GE) (i : Nat) : GF := if i == 0 then x.c0 else if i == 1 then x.c1 else x.c2

-- read over the base field, the one answer is three
#guard (List.range 3).all fun i =>
  Slice.ofF (coordinateAt baseAnswer i) ==
    Slice.ofF (coordinateAt ((1 - fieldZ0) * (1 - fieldZ1)) i * baseDatum +
      coordinateAt fieldFactor i * baseCoin 1 + coordinateAt (fieldFactor * genOfE) i * baseCoin 2 +
      coordinateAt (fieldFactor * genOfE ^ 2) i * baseCoin 3)

/-! ## The checks above can fail: each again with one thing modified -/

-- the pad's coins in the order third, second, first
#guard shownR placePadInMain 0 noRide baseData smallSeeds [[[5]], []] (writtenCoins _) !=
  baseExpected [5] (baseSymbol 3 2 1)
    ((1 - fieldZ0) * (1 - fieldZ1) * liftToE baseDatum + fieldFactor * padValue 3 2 1)
-- the weight on the datum: (1 - z₀) z₁
#guard shownR placePadInMain 0 noRide baseData smallSeeds [[[5]], []] (writtenCoins _) !=
  baseExpected [5] (baseSymbol 1 2 3)
    ((1 - fieldZ0) * fieldZ1 * liftToE baseDatum + fieldFactor * padValue 1 2 3)
-- no power of the generator at the pad's coins
#guard shownR placePadInMain 0 noRide baseData smallSeeds [[[5]], []] (writtenCoins _) !=
  baseExpected [5] (baseSymbol 1 2 3)
    ((1 - fieldZ0) * (1 - fieldZ1) * liftToE baseDatum +
      fieldFactor * (liftToE (baseCoin 1) + liftToE (baseCoin 2) + liftToE (baseCoin 3)))

end OnBytes.SendSim.At.Small
