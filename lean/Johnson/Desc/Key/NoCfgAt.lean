-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/NoCfgAt.lean: the key file's description as its makers return it, at two digests of
the public files: where `descAt X lay c` returns F, `descAt X lay c'` returns F with another test on
the file (`fileOk`), and nothing else of F turns. Johnson/Desc/Key/NoCfg.lean says this of `descriptionFromSource` at
a source that is carried to another digest; here the makers are followed: the planner's seven
chains by the library's `chainsOf_at` and `builtOf_at` (OnBytes/Tie/ChainsAtCfg.lean), the sendings,
the source, and the places' numbers by unfolding.

Main names.
  madeAtCfg m c: the planner's answer and the sendings with the digest c in the place of their own.
  madeAt_at: where `madeAt X lay c` returns m, `madeAt X lay c'` returns `madeAtCfg m c'`.
  sourceOf_atCfg, rangesNumbers_atCfg, placesK_atCfg: the three makers off m at the carried record.
  descOfMade_atCfg, descAt_at: the description.

Limits. Asked, as the library's theorem asks: both digests have 32 bytes, and the seven strings of
parameter bytes have fewer than 2 ^ 64 bytes each. Of `fileOk` nothing is shown. Of the decision on
three views alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.NoCfg
import Johnson.Desc.Key.SlotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Tie OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open Johnson.G.OfPlan (Made)

/-- The planner's answer and the sendings with another digest in the place of their own. -/
def madeAtCfg (m : Made) (c : ByteArray) : Made :=
  { m with p := { m.p with cfg := c, chains := chainsAtCfg m.p.chains c } }

theorem rangesNumbers_atCfg (m : Made) (c : ByteArray) :
    rangesNumbers (madeAtCfg m c) = rangesNumbers m := rfl

theorem placesK_atCfg (m : Made) (c : ByteArray) : laterPlaces (madeAtCfg m c) = laterPlaces m :=
  rfl

theorem sourceOf_atCfg (m : Made) (c : ByteArray) (X : Source) (h : sourceOf m = .ok X) :
    sourceOf (madeAtCfg m c) = .ok (X.atCfg c) := by
  unfold sourceOf at h ⊢
  obtain ⟨D, h1, h⟩ := exc_bind h
  obtain ⟨T, h2, h⟩ := exc_bind h
  have e1 : Johnson.G.OfPlan.declKOf (madeAtCfg m c) = .ok D := h1
  have e2 : toldOfMade (madeAtCfg m c) = .ok T := h2
  obtain rfl : _ = X := Except.ok.inj h
  exact (exc_step _ e1).trans (exc_step _ e2)

theorem descOfMade_atCfg (m : Made) (c : ByteArray) (F : FileDescription Xi) (h : descriptionFromPlan m = .ok F) :
    ∃ b, descriptionFromPlan (madeAtCfg m c) = .ok { F with fileOk := b } := by
  obtain ⟨X, N, P, hX, hN, hP, rfl⟩ := descOfMade_is m F h
  refine ⟨(descriptionFromSource (X.atCfg c) N P).fileOk, ?_⟩
  unfold descriptionFromPlan
  rw [sourceOf_atCfg m c X hX, rangesNumbers_atCfg, hN, placesK_atCfg, hP]
  exact congrArg Except.ok (desc_atCfg X N P c)

theorem madeAt_at {X : Public} {lay c c' : ByteArray} {m : Made} (hc : c.size = 32)
    (hc' : c'.size = 32) (hb : ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (h : madeAt X lay c = .ok m) : madeAt X lay c' = .ok (madeAtCfg m c') := by
  unfold madeAt at h
  obtain ⟨ch, h1, h⟩ := exc_bind h
  obtain ⟨b, h2, h⟩ := exc_bind h
  obtain ⟨l, h3, h⟩ := exc_bind h
  split at h
  · obtain rfl : _ = m := Except.ok.inj h
    unfold madeAt
    refine (exc_step _ (chainsOf_at hc hc' hb h1)).trans ?_
    refine (exc_step _ ((builtOf_at X ch c').trans h2)).trans ?_
    have h3' : Johnson.G.sendsFrom (chainsAtCfg ch c').made = .ok _ := h3
    exact (exc_step _ h3')
  · cases h

/-- **The description at two digests**: the same but for the test on the file. -/
theorem descAt_at {X : Public} {lay c c' : ByteArray} {F : FileDescription Xi} (hc : c.size = 32)
    (hc' : c'.size = 32)
    (hb : ∀ m, madeAt X lay c = .ok m → ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (h : descAt X lay c = .ok F) : ∃ b, descAt X lay c' = .ok { F with fileOk := b } := by
  obtain ⟨m, X', N, P, hm, -, -, -, -⟩ := descAt_is X lay c F h
  have hF : descriptionFromPlan m = .ok F := by
    unfold descAt at h
    rw [hm] at h
    exact h
  obtain ⟨b, hb'⟩ := descOfMade_atCfg m c' F hF
  refine ⟨b, ?_⟩
  unfold descAt
  rw [madeAt_at hc hc' (hb m hm) hm]
  exact hb'

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.rangesNumbers_atCfg
#print axioms VerifiableInference.Desc.Key.placesK_atCfg
#print axioms VerifiableInference.Desc.Key.sourceOf_atCfg
#print axioms VerifiableInference.Desc.Key.descOfMade_atCfg
#print axioms VerifiableInference.Desc.Key.madeAt_at
#print axioms VerifiableInference.Desc.Key.descAt_at
