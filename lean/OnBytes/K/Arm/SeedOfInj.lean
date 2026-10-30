-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/SeedOfInj.lean: the typed form of a record's seeds (`seedOfC`,
OnBytes/TypedOracleCompiler/Slice/EntryConv.lean) determines the program's own seeds: it is one to one on the lists
that the program's `recordSeeds` (OnBytes/Entry/Table.lean) returns.

The two seeds' fields of the tie for the entry file (`EntryPart.seed0`, `EntryPart.seed1`,
OnBytes/K/Parts.lean) speak of a record whose seed is `toSeed` of the
program's own seeds, and Johnson/Top/TieSeedHoles.lean and TieSeedArm.lean
have `toSeed` as a letter of which nothing is asked. Johnson/Top/TieArmZ.lean
puts `seedOfC` there. On all lists `seedOfC` is not one to one: a missing seed
is read as the point 0 with the factor 1; seeds beyond the s-th and coordinates beyond the lg-th are
dropped; a short point is filled with 0; a factor that reads as 0 becomes 1; words that are not
below the prime are reduced. For proofs only; the program does not import this file.

Main definition: `SeedsShaped`.
Main theorems.
 `seedOf1C_inj`   one seed: among seeds in order (`SeedOK`, OnBytes/Slice/SeedWords.lean) with
                  points of lg coordinates.
 `seedOfC_inj`    `seedOfC lg s` is one to one on `SeedsShaped lg s`: s seeds, each in order, each
                  point of lg coordinates.
 `recordSeeds_shaped` what the program's `recordSeeds` returns in the second field is `SeedsShaped`.
 `seedOfC_recordSeeds` so if the typed forms of what it returns at two names are equal, the two
                  lists are equal.

What is not claimed. The field is the second. Nothing on seeds that stand in a file or in a key and
were not drawn. That different names give different seeds. How the seeds are distributed. Nothing on
any hash function; nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Slice.EntryConv
import OnBytes.Slice.SeedWords

set_option autoImplicit false

namespace OnBytes.K.Arm
open OnBytes.Slice (readE readE_inj SeedOK seedOK_recordSeeds)
open TypedOracleCompiler.Slice (seedOf1C seedOfC)

/-- **One seed.** Among seeds in order whose points have lg coordinates, the typed form tells seeds
apart. -/
theorem seedOf1C_inj (lg : ℕ) (y y' : List E × E) (h1 : y.1.length = lg) (h1' : y'.1.length = lg)
    (hy : SeedOK y) (hy' : SeedOK y') (h : seedOf1C lg y = seedOf1C lg y') : y = y' := by
  obtain ⟨p, q, -, n⟩ := hy
  obtain ⟨p', q', -, n'⟩ := hy'
  unfold seedOf1C at h
  rw [dif_neg n, dif_neg n'] at h
  refine Prod.ext (List.ext_getElem (h1.trans h1'.symm) fun c hc hc' => ?_)
    (readE_inj _ _ q q' (congrArg Subtype.val (congrArg Prod.snd h)))
  have e := congrFun (congrArg Prod.fst h) ⟨c, h1 ▸ hc⟩
  simp only [List.getD_eq_getElem _ _ hc, List.getD_eq_getElem _ _ hc'] at e
  exact readE_inj _ _ (p _ (List.getElem_mem hc)) (p' _ (List.getElem_mem hc')) e

/-- A list of seeds has the shape of a record's: s seeds, each in order, each point of lg
coordinates. -/
def SeedsShaped (lg s : ℕ) (l : List (List E × E)) : Prop :=
  l.length = s ∧ ∀ y ∈ l, y.1.length = lg ∧ SeedOK y

/-- **The typed form of a record's seeds is one to one on lists of that shape.** -/
theorem seedOfC_inj (lg s : ℕ) (l l' : List (List E × E)) (hl : SeedsShaped lg s l)
    (hl' : SeedsShaped lg s l') (h : seedOfC lg s l = seedOfC lg s l') : l = l' := by
  refine List.ext_getElem (hl.1.trans hl'.1.symm) fun i hi hi' => ?_
  have e := congrFun h ⟨i, hl.1 ▸ hi⟩
  unfold seedOfC at e
  simp only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at e
  exact seedOf1C_inj lg _ _ (hl.2 _ (List.getElem_mem hi)).1 (hl'.2 _ (List.getElem_mem hi')).1
    (hl.2 _ (List.getElem_mem hi)).2 (hl'.2 _ (List.getElem_mem hi')).2 e

/-- **What the program's `recordSeeds` returns, in the second field, has that shape.** -/
theorem recordSeeds_shaped (name : ByteArray) (bits count : ℕ) (l : List (List E × E))
    (hl : recordSeeds .two name bits count = some l) : SeedsShaped bits count l := by
  have ok := seedOK_recordSeeds name bits count l hl
  rw [← OnBytes.Slice.recordSeedsW_H, OnBytes.Slice.recordSeedsW_pure] at hl
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 hl
  rw [timesT_eq] at ok ⊢
  refine ⟨?_, fun y hy => ⟨?_, ok y hy⟩⟩
  · rw [List.length_map]
    exact OnBytes.Slice.times_length _ _ count 0
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
    rw [List.length_map]
    exact OnBytes.Slice.seed_points _ _ bits count 0 t ht

/-- **The typed seed determines the program's own draws**: if the typed forms of what the program's
`recordSeeds` returns at two names are equal, the two lists are equal. -/
theorem seedOfC_recordSeeds (name name' : ByteArray) (bits count : ℕ) (l l' : List (List E × E))
    (hl : recordSeeds .two name bits count = some l)
    (hl' : recordSeeds .two name' bits count = some l')
    (h : seedOfC bits count l = seedOfC bits count l') : l = l' :=
  seedOfC_inj bits count l l' (recordSeeds_shaped name bits count l hl)
    (recordSeeds_shaped name' bits count l' hl') h

end OnBytes.K.Arm
