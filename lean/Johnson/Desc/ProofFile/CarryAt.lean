-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/CarryAt.lean: FOUR LETTERS OF THE CODE SWITCH's SENTENCE «carry»
(`K2Caller.carryK2 rowAt pAt door orc smp`) AS TERMS OFF THE WRITTEN PLAN: the three public files
and
the public part Z that `ProofFile.pubPlain` makes of them. Definitions with code; nothing is proved here.

The switch that closes «carry m» is the one INTO GROUP m + 1: at a link or the head, segment m + 1's
first block; behind the last segment, the finish's.
  `rowAtK2 pol lay KL m`: the switch's typed row (the structure `K2Caller.SwRow`): entry number m of
    `K2Caller.tableOf pol lay KL` (Johnson/Top/H0/K2Caller/Table.lean): that list holds one row for
    each group but the first, in order. IT READS THE THREE FILES, NOT Z: the lists of sendings
    (`Johnson.G.sendRowsOf`) are made of the files, and Z does not hold the layout file.
  `k2SpotsAt Z`: the places of the kind K2, each with its numbers, AS THE DESCRIPTION's OWN LOT LAYS
    THEM: `P1K2.pureSpots Z G₀` (Lot/K2.lean) at G₀ := `blankBy pureRoad.links Z`, the ground at
    which `baseOf` (OnlineDescriptionFromBlockTables.lean) asks every lot for its blocks.
  `pAtK2? Z m`, `pAtK2 Z m`: the numbers of the place whose switch opens group m + 1 (`P2.grp`);
    where there is none: `deadP2`, all zeros.
  `doorAtK2 Z m`: the way in of the block that is seated there, by the text of `P1K2.pureAt`: at a
    link the block IS the switch, at the head the switch comes first: the identity; at the finish
    `K2.finishPlace` runs `K2.finishFrontQ` in front: that step.
  `wholeAt Z`: the proof file's rounds' data, of the description's own declared rounds.
  `allAt Z`, `keyAt Z`: the first chain's frame's list of trees and its keys, at the letters at
  which
    the top statements lay that frame: `allOf (D.at frS.P.T.a)` and `(D.at frS.P.T.a).key₁`.
Limits. Definitions. That the row and the place's numbers fit (`K2Caller.p2AtB`) is a test, to be
run. The fifth letter, smp, is not here. No soundness is claimed.

-/
import Johnson.Desc.ProofFile.LinkAt
import Johnson.Desc.Plain.StartThreeAtPure
import Johnson.Top.H0.K2Caller.Table
import Johnson.Top.H0.K2Caller.P2At
import Johnson.Desc.Sound.Tiles
import Johnson.Desc.BlockSlot
import OnBytes.Slice.FullRecLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.First.K2Caller (SwRow tableOf)
open VerifiableInference.Desc.Sound (allOf)

/-- **The typed row of the switch that closes «carry m».** -/
def rowAtK2 (pol lay KL : ByteArray) (m : Nat) : Option SwRow :=
  (tableOf pol lay KL).toOption.bind fun t => t[m]?

/-- The places of the kind K2 with their numbers, as the description's own lot lays them. -/
def k2SpotsAt (Z : Pub) : List (Spot × P2) :=
  ((blankBy pureRoad.links Z).map (P1K2.pureSpots Z)).getD []

/-- The numbers of the place whose switch opens group m + 1. -/
def pAtK2? (Z : Pub) (m : Nat) : Option P2 :=
  ((k2SpotsAt Z).find? fun x => x.2.grp == m + 1).map (·.2)

/-- Numbers for where there is no such place. -/
def deadP2 : P2 :=
  { name := "", place := ⟨0, none, 0, .frame⟩, stands := .link, grp := 0, firstTree := 0,
    samples := 0, work₁ := 0, roots := 0, seeds := 0, nonZero := 0, work₂ := 0, answers := 0,
    positions := 0, logN := 0, sent := [], read := [] }

/-- **The place's numbers.** -/
def pAtK2 (Z : Pub) (m : Nat) : P2 := (pAtK2? Z m).getD deadP2

/-- **The way in of the block that is seated there.** -/
def doorAtK2 (Z : Pub) (m : Nat) (s : S) : Option S :=
  match (pAtK2 Z m).stands with
  | .finish => (VerifiableInference.Desc.First.K2.finishFrontQ s).toOption
  | _ => some s

/-- The proof file's rounds' data, of the description's own declared rounds. -/
def wholeAt (Z : Pub) : Option WholeD :=
  (H2U.placesOfMade Z.made).toOption.bind fun N =>
    (onlineFirstChainAt Z).toOption.bind fun c =>
      ((seatedAt emptySecondHashFunction Z N c).data "proof file").toOption

/-- **The first chain's frame's list of trees.** -/
def allAt (Z : Pub) : List LeftT := ((wholeAt Z).map fun D => allOf (D.at frS.P.T.a)).getD []

/-- **The first chain's frame's keys.** -/
def keyAt (Z : Pub) : Nat → Nat := ((wholeAt Z).map fun D => (D.at frS.P.T.a).key₁).getD id

end ProofFile
