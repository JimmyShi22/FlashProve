-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/LayoutSanity.lean: numbers of the layout and the lookup plan, computed from
Inst/Model/Layout.lean.
Theorems by evaluation in the kernel; to audit the relation `RinfPP` (Inst/Model/Scales.lean),
nothing of this file need be read.
Notation: `ppref`: `Params`; the reference parameters (Inst/Model/Program.lean).
-/
import Inst.Model.Layout
import Mathlib.Tactic

set_option autoImplicit false

namespace Inst.Model.Layout.Sanity
open Inst.Model Inst.Model.Layout

/-- the rows of the units at `ppref` -/
theorem rows_table21 :
    rows kRef (uQK ppref) = 320 ∧
    rows kRef (uV ppref) = 40 ∧
    rows kRef (uO ppref) = 200 ∧
    rows kRef (uGU ppref ppref.f) = 640 ∧
    rows kRef (uD ppref ppref.f) = 640 ∧
    rows kRef (uGU ppref ppref.fe) = 320 ∧
    rows kRef (uGUr ppref) = 40960 ∧
    rows kRef (uD ppref ppref.fe) = 320 ∧
    rows kRef (uDr ppref) = 40960 ∧
    rows kRef (uR ppref) = 10 ∧
    rows kRef (uEmb ppref) = 20480 ∧
    rows kRef (uH ppref) = 10240 := by decide +kernel

/-- The units at `ppref`. These are 48·3 + 24·3 + 24·7 + 2 = 386 units with 3,076,080 rows. -/
theorem units_total : (units ppref).length = 386 ∧ off kRef (units ppref) 386 = 3076080 := by
  decide +kernel

/-- m_2 = 1,527,800; the plan has 188 calls of the first and 94 of the second kind -/
theorem plan_numbers :
    m2 kRef (units ppref) = 1527800 ∧
    n1 kRef hRef planRef = 188 ∧
    n2 kRef (units ppref) planRef = 94 := by decide +kernel

/-! ## A small layout, by enumeration (evaluation at every build; not a theorem)
Four units with all three kinds of coordinates, sizes that are not powers of two, and k = 3 column
bits: in these units a coordinate of kind low or high gets all its bits or none; every coordinate of
kind whole gets its bits. -/

def toyUnits : List UnitS :=
  [⟨[⟨6, .low⟩, ⟨4, .high⟩], 2⟩, ⟨[⟨5, .whole⟩, ⟨12, .high⟩], 4⟩,
    ⟨[⟨3, .whole⟩, ⟨2, .whole⟩, ⟨8, .low⟩], 2⟩, ⟨[⟨12, .high⟩, ⟨6, .low⟩], 2⟩]

/-- all index tuples of a unit -/
def allIdx : List Coord → List (List ℕ)
  | [] => [[]]
  | c :: cs => (List.range c.R).flatMap fun i => (allIdx cs).map fun is => i :: is

/-- all places of all bytes of all entries -/
def allPlaces (k : ℕ) (us : List UnitS) : List (ℕ × ℕ) :=
  us.zipIdx.flatMap fun p =>
    (List.range p.1.nU).flatMap fun jj => (allIdx p.1.coords).map fun i => place k us p.2 p.1 jj i

-- the map from a weight and a byte number to a place is injective
#guard (allPlaces 3 toyUnits).eraseDups.length == (allPlaces 3 toyUnits).length
-- there are as many places as bytes: 2·24 + 4·60 + 2·48 + 2·72
#guard (allPlaces 3 toyUnits).length == 528
-- every place is below the number of rows of all units, and in a column below 2^k
#guard (allPlaces 3 toyUnits).all fun p => p.1 < off 3 toyUnits 4 && p.2 < 2 ^ 3
-- every row of every unit is used
#guard ((allPlaces 3 toyUnits).map Prod.fst).eraseDups.length == off 3 toyUnits 4
-- the pairs of the plan are the pairs of rows of the layout, each once
#guard ((List.range (m2 3 toyUnits)).map (pair 3 toyUnits)).eraseDups.length == m2 3 toyUnits
#guard (toyUnits.zipIdx.filter fun p => p.1.nU = 2).all fun p => (allIdx p.1.coords).all fun i =>
  ((List.range (m2 3 toyUnits)).map (pair 3 toyUnits)).contains ((place 3 toyUnits p.2 p.1 0 i).1, (place 3 toyUnits p.2 p.1 1 i).1)
-- at `ppref`: the first and the last byte that the layout places
#guard place kRef (units ppref) 0 (uQK ppref) 0 [0, 0, 0] == (0, 0)
#guard (place kRef (units ppref) 385 (uH ppref) 1 [202047, 5119]).1 == 3076079

end Inst.Model.Layout.Sanity
