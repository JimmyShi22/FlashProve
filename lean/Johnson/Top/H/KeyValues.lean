-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/KeyValues.lean: the stages of the four proximity tests of a key file's three chains
at full size, as written lists of numbers, and the tests on these numbers.

The lists are written out: fourteen code switches, the fourteen stages that are folded, the four
last stages. A stage is two codes (logarithm of the length, entries of a message, random entries),
the numbers of row variables of the mask rows and of the others, and the number of drawn
positions; beside it stands its radius. Definitions, and statements that are proved by evaluation
on natural numbers.
Main names:
  `keyCs`: the code switches, in the order of the chains: the proof of the ranges (3); the folded
    row (4) and Omega (3); the own test (4).
  `keyFolded`, `keyLast`: the stages that are folded, and the last stages, each with its radius.
  `keyCs_good`, `keyFolded_good`, `keyLast_good`: every place passes the tests of
    Johnson/Top/H/StageJ.lean and `CsPlace.good`.
  `cCsKey`, `hCsKey`: so the conditions of the code switch hold at all fourteen, and so does the
    statement. Nothing is asked.
  `keyFolds bC bZ`, `keyBases bC bZ`: the places of the folds and of the last steps, at counts
    that the caller gives as functions of stage and radius.
  `hFoldKey`, `hBaseKey`: the statements at these places, under `CFoldCounts` and `CBaseCounts`
    alone; of a fold in both forms: in the plan the eighth fold (the first of Omega's test) sends
    its own mask, the other thirteen do not.
  `keyFar`: at every one of the eighteen stages twice the radius is at least the stage's distance,
    and at least the repeated mask code's own distance.
Limits: that these numbers are those of a key file's plan is not proved here: they were read off a
print of the planner's calls at the example of full size, and the radii were reckoned outside
Lean, in exact integers, as the floor of n - sqrt (k n) (m + 1) / m at the code that rules. The
print was made by evaluating this library's port of the planner at the three public files of the
example set prover/examples/target_full_f2, held as constants by the program that printed (name,
size, sha256):
  policy.txt (2,629 bytes) ce9e126bb3ba7179319a31981a3fc36ca505d738348971f379dfc795f94a3fae
  layout.txt (224,975 bytes) a99b964bbd3648d6e3b4007fc9370b5c70c7e9668848daa039820bc9e03e8f80
  KL.bin (2,784 bytes) 1c3191164c5113fd04d5108a469d7b3d17f4ccb3256e8a676d15bdc94435b919
That program and the program that cut the numbers out of the print are not in this repository. That
each radius is `radiusOf` of its group is not shown. By `keyFar` no theorem of this library on
counts below half a distance applies at any of these stages.

-/
import Johnson.Top.H.CsValues
import Johnson.Top.H.FoldValues
import Johnson.Top.H.BaseValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb.Pv.Tower

/-- The fourteen code switches. -/
def keyCs : List CsPlace := [
  ⟨⟨⟨22, 262144, 49⟩, ⟨16, 4096, 49⟩, 4, 0, 49⟩,
    ⟨⟨19, 16384, 39⟩, ⟨17, 2048, 39⟩, 3, 1, 39⟩, 3131959, 431022⟩,
  ⟨⟨⟨19, 16384, 39⟩, ⟨17, 2048, 39⟩, 3, 1, 39⟩,
    ⟨⟨17, 2048, 33⟩, ⟨17, 1024, 33⟩, 3, 0, 33⟩, 431022, 114481⟩,
  ⟨⟨⟨17, 2048, 33⟩, ⟨17, 1024, 33⟩, 3, 0, 33⟩,
    ⟨⟨20, 2048, 25⟩, ⟨20, 4096, 25⟩, 0, 0, 25⟩, 114481, 982125⟩,
  ⟨⟨⟨24, 4194304, 97⟩, ⟨13, 64, 146⟩, 0, 7, 97⟩,
    ⟨⟨21, 131072, 52⟩, ⟨12, 256, 52⟩, 2, 3, 52⟩, 8342420, 1519572⟩,
  ⟨⟨⟨21, 131072, 52⟩, ⟨12, 256, 52⟩, 2, 3, 52⟩,
    ⟨⟨17, 8192, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩, 1519572, 95065⟩,
  ⟨⟨⟨17, 8192, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩,
    ⟨⟨13, 512, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩, 95065, 5944⟩,
  ⟨⟨⟨13, 512, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩,
    ⟨⟨14, 512, 49⟩, ⟨14, 1024, 49⟩, 0, 0, 49⟩, 5944, 12184⟩,
  ⟨⟨⟨22, 262144, 98⟩, ⟨13, 64, 146⟩, 0, 4, 49⟩,
    ⟨⟨18, 16384, 49⟩, ⟨14, 128, 49⟩, 3, 1, 49⟩, 3138896, 196275⟩,
  ⟨⟨⟨18, 16384, 49⟩, ⟨14, 128, 49⟩, 3, 1, 49⟩,
    ⟨⟨14, 1024, 49⟩, ⟨13, 64, 49⟩, 3, 1, 49⟩, 196275, 12184⟩,
  ⟨⟨⟨14, 1024, 49⟩, ⟨13, 64, 49⟩, 3, 1, 49⟩,
    ⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩, 12184, 26851⟩,
  ⟨⟨⟨22, 262144, 98⟩, ⟨13, 256, 49⟩, 1, 4, 49⟩,
    ⟨⟨18, 16384, 49⟩, ⟨15, 128, 49⟩, 3, 1, 49⟩, 3138896, 196275⟩,
  ⟨⟨⟨18, 16384, 49⟩, ⟨15, 128, 49⟩, 3, 1, 49⟩,
    ⟨⟨15, 2048, 49⟩, ⟨14, 64, 49⟩, 3, 0, 49⟩, 196275, 24460⟩,
  ⟨⟨⟨15, 2048, 49⟩, ⟨14, 64, 49⟩, 3, 0, 49⟩,
    ⟨⟨13, 256, 41⟩, ⟨13, 64, 41⟩, 3, 0, 41⟩, 24460, 6631⟩,
  ⟨⟨⟨13, 256, 41⟩, ⟨13, 64, 41⟩, 3, 0, 41⟩,
    ⟨⟨15, 256, 29⟩, ⟨15, 256, 29⟩, 0, 0, 29⟩, 6631, 29702⟩]

/-- The fourteen stages that are folded, each with its radius. -/
def keyFolded : List (Sg × ℕ) := [
  (⟨⟨22, 262144, 49⟩, ⟨16, 4096, 49⟩, 4, 0, 49⟩, 3131959),
  (⟨⟨19, 16384, 39⟩, ⟨17, 2048, 39⟩, 3, 1, 39⟩, 431022),
  (⟨⟨17, 2048, 33⟩, ⟨17, 1024, 33⟩, 3, 0, 33⟩, 114481),
  (⟨⟨24, 4194304, 97⟩, ⟨13, 64, 146⟩, 0, 7, 97⟩, 8342420),
  (⟨⟨21, 131072, 52⟩, ⟨12, 256, 52⟩, 2, 3, 52⟩, 1519572),
  (⟨⟨17, 8192, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩, 95065),
  (⟨⟨13, 512, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩, 5944),
  (⟨⟨22, 262144, 98⟩, ⟨13, 64, 146⟩, 0, 4, 49⟩, 3138896),
  (⟨⟨18, 16384, 49⟩, ⟨14, 128, 49⟩, 3, 1, 49⟩, 196275),
  (⟨⟨14, 1024, 49⟩, ⟨13, 64, 49⟩, 3, 1, 49⟩, 12184),
  (⟨⟨22, 262144, 98⟩, ⟨13, 256, 49⟩, 1, 4, 49⟩, 3138896),
  (⟨⟨18, 16384, 49⟩, ⟨15, 128, 49⟩, 3, 1, 49⟩, 196275),
  (⟨⟨15, 2048, 49⟩, ⟨14, 64, 49⟩, 3, 0, 49⟩, 24460),
  (⟨⟨13, 256, 41⟩, ⟨13, 64, 41⟩, 3, 0, 41⟩, 6631)]

/-- The four last stages, each with its radius. -/
def keyLast : List (Sg × ℕ) := [
  (⟨⟨20, 2048, 25⟩, ⟨20, 4096, 25⟩, 0, 0, 25⟩, 982125),
  (⟨⟨14, 512, 49⟩, ⟨14, 1024, 49⟩, 0, 0, 49⟩, 12184),
  (⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩, 26851),
  (⟨⟨15, 256, 29⟩, ⟨15, 256, 29⟩, 0, 0, 29⟩, 29702)]

theorem keyCs_good : ∀ x ∈ keyCs, x.good = true := by decide +kernel

theorem keyFolded_good : ∀ p ∈ keyFolded, (sizedB p.1 && inJB p.1 p.2) = true := by
  decide +kernel

theorem keyLast_good : ∀ p ∈ keyLast, (sizedB p.1 && inJB p.1 p.2) = true := by decide +kernel

/-- Twice the radius is at least the stage's distance and the repeated mask code's own. -/
theorem keyFar : ∀ p ∈ keyFolded ++ keyLast, p.1.d ≤ 2 * p.2 ∧ p.1.dZ ≤ 2 * p.2 := by
  decide +kernel

/-- The conditions of the code switch hold at all fourteen. -/
theorem cCsKey : CCs keyCs := cCs keyCs keyCs_good

theorem hCsKey : ∀ z ∈ sizesCs keyCs, z.H := hCs keyCs keyCs_good

theorem keyCs_all : (sizesCs keyCs).length = 14 := sizesCs_length keyCs keyCs_good

/-- The places of the folds, at given counts. -/
def keyFolds (bC bZ : Sg → ℕ → ℕ) : List FoldPlace :=
  keyFolded.map fun p => ⟨p.1, 0, p.2, bC p.1 p.2, bZ p.1 p.2⟩

/-- The places of the last steps, at given counts. -/
def keyBases (bC bZ : Sg → ℕ → ℕ) : List BasePlace :=
  keyLast.map fun p => ⟨p.1, p.2, bC p.1 p.2, bZ p.1 p.2⟩

theorem keyFolds_good (bC bZ : Sg → ℕ → ℕ) : ∀ x ∈ keyFolds bC bZ, x.good = true := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact keyFolded_good p hp

theorem keyBases_good (bC bZ : Sg → ℕ → ℕ) : ∀ x ∈ keyBases bC bZ, x.good = true := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact keyLast_good p hp

theorem hFoldKey (bC bZ : Sg → ℕ → ℕ) (hc : CFoldCounts (keyFolds bC bZ)) :
    ∀ z ∈ sizesFold (keyFolds bC bZ), z.HRide ∧ z.HOwn :=
  fun z hz => ⟨hFoldRide _ (keyFolds_good bC bZ) hc z hz, hFoldOwn _ (keyFolds_good bC bZ) hc z hz⟩

theorem hBaseKey (bC bZ : Sg → ℕ → ℕ) (hc : CBaseCounts (keyBases bC bZ)) :
    ∀ z ∈ sizesBase (keyBases bC bZ), z.H :=
  hBase _ (keyBases_good bC bZ) hc

end Johnson.Top.H

#print axioms Johnson.Top.H.cCsKey
#print axioms Johnson.Top.H.keyFar
#print axioms Johnson.Top.H.hFoldKey
#print axioms Johnson.Top.H.hBaseKey
