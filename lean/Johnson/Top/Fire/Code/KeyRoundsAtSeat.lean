-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyRoundsAtSeat.lean: at the full size: THE NUMBERS OF DECLARED ROUNDS OF ALL 35 BLOCKS OF THE KEY FILE's DESCRIPTION, CHAIN BY CHAIN, AS WRITTEN NUMBERS, IN SCOPE, AT ANY DIGEST.
Main names.
  `roundsW₁` | `roundsW₂` | `roundsW₃`: the three written lists (19 · 12 · 4 numbers).
  `wantedFirst_full` | `wantedShared_full` | `wantedSecond_full`: the tables `wanted` (Johnson/Desc/Key/WantedFirst.lean | WantedLater.lean) at the written key's ranges and shape have these numbers [the kernel]; `wantedShared_no`: a test that such a comparison can fail.
  `rounds_in_scope`: under the description's tests on the plan and `wantedOk`: the blocks' numbers of declared rounds ARE the written lists: BY `desc_rounds` (Johnson/RunOne/Sound/KeyListsAtFK.lean) and `one_full` (KeyPublicAtSeat.lean): called.
  `lengths_in_scope`: so the three flat lists have 19 · 12 · 4 blocks.
OBJECT: `Key.descriptionFromSource X N P` as the maker makes it in scope · USER: KeyBasesAtSix.lean, Row117Nine.lean, Rows2SeedRound.lean and others (the test on bases: BasePinsTie.lean's three bounds; a row's stretch) · LETTERS: none.
Limits. PUBLIC NUMBERS ALONE. The full size alone. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyPublicAtSeat
import Johnson.RunOne.Sound.KeyListsAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.RunOne.KeyRows23 (Fk oneAt)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)

/-- The first chain's 19 blocks' numbers of declared rounds. -/
def roundsW₁ : List Nat := [2, 2, 0, 0, 9581, 0, 0, 0, 0, 0, 9220, 0, 0, 0, 0, 23, 20, 2, 1]

/-- The shared chain's 12. -/
def roundsW₂ : List Nat := [0, 1, 2, 0, 1, 2, 0, 1, 1, 35, 24, 1]

/-- The last chain's 4. -/
def roundsW₃ : List Nat := [0, 0, 30, 0]

theorem wantedFirst_full (one : OnBytes.Params.OneTime) (h1 : one.ranges = keyFull.ranges.x) (h2 : one.lin = keyFull.once.shape) :
    (wantedFirst one).map (·.2) = roundsW₁ := by
  unfold wantedFirst
  simp only [h1, h2]
  decide +kernel

theorem wantedShared_full : (wantedShared keyFull.once.shape).map (·.2) = roundsW₂ := by decide +kernel

theorem wantedSecond_full : (wantedSecond keyFull.once.shape).map (·.2) = roundsW₃ := by decide +kernel

/-- A test that such a comparison can fail. -/
theorem wantedShared_no : ¬ (wantedShared keyFull.once.shape).map (·.2) = [0, 1, 2, 0, 1, 2, 0, 1, 1, 35, 25, 1] := by decide +kernel

section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
  (hw : (Fk X N P).wantedOk = true)
include hZ hP hm hX hp hw

/-- **The blocks' numbers of declared rounds are the written lists.** -/
theorem rounds_in_scope : (Fk X N P).first.blocksInOrder.map (·.rounds.length) = roundsW₁ ∧ (Fk X N P).shared.blocksInOrder.map (·.rounds.length) = roundsW₂ ∧
    (Fk X N P).second.blocksInOrder.map (·.rounds.length) = roundsW₃ := by
  obtain ⟨e1, e2, e3⟩ := one_full hZ hP hm hX hp
  obtain ⟨h1, h2, h3⟩ := Johnson.RunOne.Sound.desc_rounds X N P hp hw
  exact ⟨h1.trans (wantedFirst_full _ e1 e2), h2.trans (by rw [e3]; exact wantedShared_full), h3.trans (by rw [e3]; exact wantedSecond_full)⟩

/-- **The three flat lists have 19 · 12 · 4 blocks.** -/
theorem lengths_in_scope : (Fk X N P).first.blocksInOrder.length = 19 ∧ (Fk X N P).shared.blocksInOrder.length = 12 ∧ (Fk X N P).second.blocksInOrder.length = 4 := by
  obtain ⟨h1, h2, h3⟩ := rounds_in_scope hZ hP hm hX hp hw
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg List.length h1
    rwa [List.length_map] at this
  · have := congrArg List.length h2
    rwa [List.length_map] at this
  · have := congrArg List.length h3
    rwa [List.length_map] at this

end

end LPFD

#print axioms LPFD.wantedFirst_full
#print axioms LPFD.wantedShared_full
#print axioms LPFD.wantedSecond_full
#print axioms LPFD.wantedShared_no
#print axioms LPFD.rounds_in_scope
#print axioms LPFD.lengths_in_scope
