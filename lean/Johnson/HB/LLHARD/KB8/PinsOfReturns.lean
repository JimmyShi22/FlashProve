-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/PinsOfReturns.lean: for public files in scope of the goals, from the returns
of `publicOfO`, `Key.madeAt` and `Key.sourceOf`: the source X of the key file's description holds
the typed sizes of a key of full size where the premises r8 and r8' of `IM.keyBack_of_rows`
(Johnson/IMR/KeyBackOfRows.lean) read it (`PinsX`, PinsOfEnds.lean in this folder). Calls, with
small steps in between.

The premises. hZ: the three public files are in scope of the goals (`VerifierAndGoals.InScope`, Ladder.lean).
hX: `publicOfO o` returns X₀; o may be any function: it stands in place of the second hash function
(`secondHashFunction`). hm: `Key.madeAt` returns m. r1: `Key.sourceOf m` returns X. h32: the digest has
32 bytes. No called theorem has `planOk = true` among its premises.
At which digest it is meant to be used: at `Key.fixedDigest`, the constant at which `Key.keyDataAndDecisionAtFixedDigest`
(Johnson/Desc/Key/Slot.lean) calls `Key.madeAt`. It has 32 bytes (`Key.fixedDigest_size`,
Johnson/Desc/Key/SlotIs.lean): the forms `…_at_fixed` take hZ, hX, hm and r1 alone. The two calls
that take h32 are shown at a digest of 32 bytes alone.

Main names.
  `pinsX_of_returns`: `PinsX X`. `pins_of_returns`: with the part on N and P, `Pins X N P`.
  `r8_of_returns`, `r8'_of_returns`: the statements of r8 and r8'.
  `pinsX_at_fixed`, `r8_at_fixed`, `r8'_at_fixed`: the same at the fixed digest.

The calls, in order.
  `IM.keyPins_at_made` (Johnson/IMR/KeyPinsAtMade.lean): `chainsOf` returned m's chains; the sized
    key is `keyFull`.
  `chainsOf_parts` (OnBytes/Model/Fit/PlannedParts.lean): so `configure` returned what was made, and
    `KeyChains.read` returned m's key's chains at the three strings that were made.
  `AtFull.KeyBack.four_at_scope` (Johnson/AtFull/KeyBack/BytesShort.lean): two of these strings
    have fewer than 2 ^ 24 bytes.
  `Johnson.KB9.items_at_made` (Johnson/HB/LLHARD/KB9/ItemsAtMade.lean): so the items that are read
    back are `keyFull`'s.
  `pubsOf_k` (Johnson/RunOne/KeyAtFkMore.lean), `sourceOf_parts`
    (Johnson/RunOne/Law/KeyInScope.lean): what X holds of m.
  `pinsX_of_ends`.

Limits. That `publicOfO`, `Key.madeAt` or `Key.sourceOf` returns at any files is not said. The part
on N and P (`PinsNP`) stays a premise. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB8.PinsOfEnds
import Johnson.HB.LLHARD.KB9.ItemsAtMade
import Johnson.IMR.KeyPinsAtMade
import Johnson.AtFull.KeyBack.BytesShort
import Johnson.RunOne.KeyAtFkMore
import OnBytes.Model.Fit.PlannedParts
import Johnson.Desc.Key.SlotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open VerifiableInference VerifiableInference.Desc
open Johnson.G (dryKeyFull writtenKFull)
open Johnson.G.OfPlan (Made writtenOf)
open OnBytes.Model.Verify (Public chainsOf chainsOf_parts)
open Lk6.AtPlan (keyFull)

section
variable {Z : VerifierAndGoals.PublicFiles} {o : ℕ → ByteArray → ByteArray} {X₀ : Public} {cfg : ByteArray} {m : Made}
  {X : Key.Source}

/-- **The part on X, from the returns.** -/
theorem pinsX_of_returns (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay cfg = .ok m) (h32 : cfg.size = 32) (r1 : Key.sourceOf m = .ok X) :
    PinsX X := by
  obtain ⟨-, hch, -, -, hz, -⟩ := IM.keyPins_at_made hZ hX hm
  obtain ⟨links, shapes, -, hcf, hread, -⟩ := chainsOf_parts hch
  obtain ⟨b1, b2, -⟩ := AtFull.KeyBack.four_at_scope hZ hX hm h32
  have hb₁ : m.p.chains.made.keyOneTime.size < 2 ^ 64 := Nat.lt_trans b1 (by norm_num)
  have hb₂ : m.p.chains.made.keyShared.size < 2 ^ 64 := Nat.lt_trans b2 (by norm_num)
  obtain ⟨i1, i2, -, -, i5, i6, -, i8⟩ := Johnson.KB9.items_at_made hcf h32 hb₁ hb₂ hread hz
  obtain ⟨hc, hk⟩ := Johnson.RunOne.KeyRows23.pubsOf_k m X r1
  exact pinsX_of_ends hc hk (Johnson.RunOne.Law.SourceIs.sourceOf_parts r1).1 hz i1 i2 i5 i6 i8

/-- With the part on N and P: the whole. -/
theorem pins_of_returns (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay cfg = .ok m) (h32 : cfg.size = 32) (r1 : Key.sourceOf m = .ok X)
    {N : H2U.PlaceNums} {P : Key.LaterPlaces} (hn : PinsNP N P) : Pins X N P :=
  pins_of_parts (pinsX_of_returns hZ hX hm h32 r1) hn

/-- **r8 from the returns**, and the part on N and P. -/
theorem r8_of_returns (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay cfg = .ok m) (h32 : cfg.size = 32) (r1 : Key.sourceOf m = .ok X)
    {N : H2U.PlaceNums} {P : Key.LaterPlaces} (hn : PinsNP N P) :
    writtenOf "key file" (Key.descriptionFromSource X N P).roundsDeclaredByBlocks = .ok dryKeyFull :=
  r8_of_parts (pinsX_of_returns hZ hX hm h32 r1) hn

/-- **r8' from the returns.** -/
theorem r8'_of_returns (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay cfg = .ok m) (h32 : cfg.size = 32) (r1 : Key.sourceOf m = .ok X)
    (N : H2U.PlaceNums) (P : Key.LaterPlaces) : (Key.descriptionFromSource X N P).tableDepth = 32 :=
  r8'_of_x (pinsX_of_returns hZ hX hm h32 r1) N P

/-! ## At the fixed digest -/

/-- The part on X, at the fixed digest. -/
theorem pinsX_at_fixed (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) (r1 : Key.sourceOf m = .ok X) : PinsX X :=
  pinsX_of_returns hZ hX hm Key.fixedDigest_size r1

/-- r8 at the fixed digest. -/
theorem r8_at_fixed (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) (r1 : Key.sourceOf m = .ok X)
    {N : H2U.PlaceNums} {P : Key.LaterPlaces} (hn : PinsNP N P) :
    writtenOf "key file" (Key.descriptionFromSource X N P).roundsDeclaredByBlocks = .ok dryKeyFull :=
  r8_of_returns hZ hX hm Key.fixedDigest_size r1 hn

/-- r8' at the fixed digest. -/
theorem r8'_at_fixed (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) (r1 : Key.sourceOf m = .ok X)
    (N : H2U.PlaceNums) (P : Key.LaterPlaces) : (Key.descriptionFromSource X N P).tableDepth = 32 :=
  r8'_of_returns hZ hX hm Key.fixedDigest_size r1 N P

end

end Johnson.KB8

#print axioms Johnson.KB8.pinsX_of_returns
#print axioms Johnson.KB8.pins_of_returns
#print axioms Johnson.KB8.r8_of_returns
#print axioms Johnson.KB8.r8'_of_returns
#print axioms Johnson.KB8.pinsX_at_fixed
#print axioms Johnson.KB8.r8_at_fixed
#print axioms Johnson.KB8.r8'_at_fixed
