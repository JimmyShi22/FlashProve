-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/KeyPinsOfReturns.lean: `keyPins_of_returns`: for public files in scope of the
goals, the eight equations of `KeyPins m` (Johnson/AtFull/KeyBack/Pins.lean) hold for the value m
that `Key.madeAt` returns where 32 bytes stand in the digest's place. Each equates a part of m (the
last: a list's length) with a closed constant of this library, made for the full-size example. From
`KeyPins m` alone the files of Johnson/AtFull/KeyBack/ derive what `Key.sourceOf`,
`Key.rangesNumbers` and `Key.laterPlaces` return: the three inputs of the IOP as written in Lean for
the key file (`Key.descriptionFromSource`, Johnson/Desc/Key/Desc.lean). The proofs call theorems of other files, with
small steps in between.

The premises. hZ: the three public files Z are in scope of the goals (`VerifierAndGoals.InScope`,
Ladder.lean). hX: `publicOfO o` returns X₀ on them; o may be any function: it stands in place of the
format's second hash function (`secondHashFunction`). hm: `Key.madeAt` returns m at X₀, Z's layout file and a
byte string cfg in the digest's place. h32: cfg has 32 bytes; only the last field, rangesLen, needs
it. `keyPins_at_fixed` is the case of the fixed digest, `Key.fixedDigest`: the constant of 32 bytes
at which `Key.keyDataAndDecisionAtFixedDigest` (Johnson/Desc/Key/Slot.lean) calls `Key.madeAt`. No called theorem has
`planOk = true` among its premises.

The fields of `KeyPins m`, each with the theorem that gives it.
  sends: `IM.keySends_at_made` (Johnson/IMR/KeySendsAtMade.lean); `keySendsFull` is the field's
    triple (keySends0, keySends1, keySends2) by its definition (Johnson/G/SendsWritten.lean).
  p₀, p₁, p₂, sizedSet, madeKey: `IM.keyPlans_at_made` (Johnson/IMR/KeyPlansAtMade.lean).
  sizedKey: the fifth conclusion of `IM.keyPins_at_made` (Johnson/IMR/KeyPinsAtMade.lean), whose
    conclusion, despite its name, is not `KeyPins m`.
  rangesLen: the item "ranges", read back from a key file's parameter bytes, equals
    `keyFull.ranges.x`: `Johnson.KB9.items_at_made` (Johnson/HB/LLHARD/KB9/ItemsAtMade.lean), whose
    premises come from `chainsOf_parts` (OnBytes/Model/Fit/PlannedParts.lean),
    `IM.keyPlans_at_made`'s last conclusion and `AtFull.KeyBack.four_at_scope`
    (Johnson/AtFull/KeyBack/BytesShort.lean).

Limits. Nothing here shows that hZ, hX and hm can hold together, that is, that there are files in
scope at which `publicOfO` and `Key.madeAt` return a value and not an error; if there were none,
both theorems would hold vacuously.
`KeyPins m` does not fix all of m: `Key.sourceOf` copies m's chains, whole (`m.p.chains`), and the
units of m's layout into its answer. Seven of the eight equations are about single fields of the
chains, not the whole; none speaks of the layout. Nothing on soundness.

-/
import Johnson.AtFull.KeyBack.Pins
import Johnson.IMR.KeySendsAtMade
import Johnson.HB.LLHARD.KB9.ItemsAtMade
import Johnson.AtFull.KeyBack.BytesShort
import OnBytes.Model.Fit.PlannedParts
import Johnson.Desc.Key.SlotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open VerifiableInference VerifiableInference.Desc
open Johnson.G.OfPlan (Made)
open OnBytes.Model.Verify (Public chainsOf_parts)

section
variable {Z : VerifierAndGoals.PublicFiles} {o : ℕ → ByteArray → ByteArray} {X₀ : Public} {cfg : ByteArray} {m : Made}

/-- **`KeyPins m`, from the returns of `publicOfO` and `Key.madeAt` and a digest of 32 bytes**, for
public files in scope of the goals. -/
theorem keyPins_of_returns (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay cfg = .ok m) (h32 : cfg.size = 32) :
    Johnson.AtFull.KeyBack.KeyPins m := by
  obtain ⟨-, hch, -, -, hz, -⟩ := IM.keyPins_at_made hZ hX hm
  obtain ⟨hset, hpl, q0, q1, q2, hread⟩ := IM.keyPlans_at_made hZ hX hm
  obtain ⟨links, shapes, -, hcf, -, -⟩ := chainsOf_parts hch
  obtain ⟨b1, b2, -⟩ := AtFull.KeyBack.four_at_scope hZ hX hm h32
  have hb₁ : m.p.chains.made.keyOneTime.size < 2 ^ 64 := Nat.lt_trans b1 (by norm_num)
  have hb₂ : m.p.chains.made.keyShared.size < 2 ^ 64 := Nat.lt_trans b2 (by norm_num)
  obtain ⟨-, i2, -⟩ := Johnson.KB9.items_at_made hcf h32 hb₁ hb₂ hread hz
  exact ⟨IM.keySends_at_made hZ hX hm, q0, q1, q2, hz, hset, hpl, by rw [i2]⟩

/-- The same at `Key.fixedDigest`, which has 32 bytes. -/
theorem keyPins_at_fixed (hZ : VerifierAndGoals.InScope Z = true)
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m) : Johnson.AtFull.KeyBack.KeyPins m :=
  keyPins_of_returns hZ hX hm Key.fixedDigest_size

end

end Johnson.KB8

#print axioms Johnson.KB8.keyPins_of_returns
#print axioms Johnson.KB8.keyPins_at_fixed
