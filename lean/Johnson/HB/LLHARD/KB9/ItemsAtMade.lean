-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/ItemsAtMade.lean: THE SEVEN ITEMS THAT ARE READ BACK FROM A KEY FILE's
PARAMETER BYTES, BESIDE THE PLANS, ARE THE PLANNER's SIZED VALUES; at the written sizes of a key of
full size: `keyFull`'s (Johnson/Goal/PlanValues/KeySizedReturns.lean).

Why. The tests on the key file's IOP as written in Lean read the one-time chain's index masks'
notice, ranges, binding tree, codes and test on the table, and the shared chain's codes and test on
the table, as `KeyChains.read` makes them of the parameter bytes. That these are the sized values
lay only under the very test that is to be shown (`planOk`). Here it follows from the reading alone.

  `oneTime_items`, `shared_items`: where a chain's reader returns and the items are known by name
    and value, each field is what its item's reader returns at that value. By the readers' texts
    (OnBytes/Params/Chains.lean).
  **`items_of_read`**: general in the sizes: where `configure` returns made, the digest has 32
    bytes, the two strings are shorter than 2 ^ 64 bytes, `KeyChains.read` returns k at made's three
    strings, and the sized values pass `itemsB` (Johnson/HB/LLHARD/KB9/ItemsOk.lean): the seven are
    made.sized.key's.
  **`items_at_made`**: the same at made.sized.key = `keyFull`, where the test's yes is a closed fact
    (`itemsB_full`, Johnson/HB/LLHARD/KB9/ItemsFull.lean). The binding tree's depth is 0. By:
    `configure_bytes`, `KeyChains.read_three`, `oneTimeItems_names`, `madeLinItems_names`
    (OnBytes/Model/ReadBackMade.lean); `Given.read_items` (OnBytes/Params/ReadBackLaws.lean); the
    five laws of Johnson/HB/LLHARD/KB9/ItemsBack.lean.

WHERE IT IS USED. The tests on the key file's source read X.Y.k; where `Key.sourceOf m` returns X,
that is m.p.chains.key by that routine's text (Johnson/Desc/Key/Desc.lean; as a law: `pubsOf_k`,
Johnson/RunOne/KeyAtFkMore.lean, which this file does not import), and made is m.p.chains.made.

AT WHICH DIGEST. At a digest of 32 bytes (h32): such is the constant in the digest's place, and the
format's hash of the three public files. At a free string in the digest's place the two bounds hb₁,
hb₂ can fail: at one of 2 ^ 64 bytes or more a chain's parameter bytes are as long (the theorem
`long_cfg`).

THE PREMISES, AND WHAT GIVES EACH. hc: that the planner returned. h32: the digest's length. hb₁,
hb₂: two of the seven bounds on the strings' lengths: `AtFull.KeyBack.four_at_scope`
(Johnson/AtFull/KeyBack/BytesShort.lean) has them in scope of the goals, from the returns of
`publicOfO` and `Key.madeAt` and h32. hread: that the reader returned. hz: the sized values are the
written ones. None passes through `planOk`.

Limits. Nothing says that `configure` or a reader returns. Nothing on the plans that are read back.
Nothing on soundness.
-/
import Johnson.HB.LLHARD.KB9.ItemsBack
import Johnson.HB.LLHARD.KB9.ItemsFull
import OnBytes.Model.ReadBackMade
import OnBytes.Params.ReadBackLaws
import OnBytes.Params.ReadBackAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params OnBytes.Plan
open Lk6.AtPlan (keyFull)

/-- The one-time chain's five fields, off its five items. -/
theorem oneTime_items {b : ByteArray} {q : OneTime} {m r t c l : ByteArray}
    (h : OneTime.read b = some q)
    (hi : q.given.items = [("index-mask message", m), ("ranges", r), ("binding tree", t),
      ("codes", c), ("the test on the table", l)]) :
    readNotice m = some q.indexMasks ∧ readRanges r = some q.ranges ∧
      readBinding t = some q.binding ∧ readCodes c = some q.codes ∧ readLin l = some q.lin := by
  unfold OneTime.read at h
  obtain ⟨g, _, h⟩ := opt_bind h
  split at h
  · rename_i m' r' t' c' l' he
    obtain ⟨a1, e1, h⟩ := opt_bind h
    obtain ⟨a2, e2, h⟩ := opt_bind h
    obtain ⟨a3, e3, h⟩ := opt_bind h
    obtain ⟨a4, e4, h⟩ := opt_bind h
    obtain ⟨a5, e5, h⟩ := opt_bind h
    cases h
    have e : [("index-mask message", m'), ("ranges", r'), ("binding tree", t'), ("codes", c'),
        ("the test on the table", l')] = [("index-mask message", m), ("ranges", r),
        ("binding tree", t), ("codes", c), ("the test on the table", l)] := he.symm.trans hi
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at e
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := e
    exact ⟨e1, e2, e3, e4, e5⟩
  · cases h

/-- The shared chain's two fields, off its two items. -/
theorem shared_items {b : ByteArray} {q : Shared} {c l : ByteArray} (h : Shared.read b = some q)
    (hi : q.given.items = [("codes", c), ("the test on the table", l)]) :
    readCodes c = some q.codes ∧ readLin l = some q.lin := by
  unfold Shared.read at h
  obtain ⟨g, _, h⟩ := opt_bind h
  split at h
  · rename_i c' l' he
    obtain ⟨a1, e1, h⟩ := opt_bind h
    obtain ⟨a2, e2, h⟩ := opt_bind h
    cases h
    have e : [("codes", c'), ("the test on the table", l')] =
        [("codes", c), ("the test on the table", l)] := he.symm.trans hi
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨e1, e2⟩
  · cases h

/-- **THE SEVEN ITEMS AS READ BACK ARE THE SIZED VALUES.** -/
theorem items_of_read {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hc : configure l x cfg bits = .ok made) (h32 : cfg.size = 32)
    (hb₁ : made.keyOneTime.size < 2 ^ 64) (hb₂ : made.keyShared.size < 2 ^ 64) {k : KeyChains}
    (hread : KeyChains.read made.keyOneTime made.keyShared made.keySecond = some k)
    (hok : itemsB made.sized.key = true) :
    k.oneTime.indexMasks = made.sized.key.once.input ∧
      k.oneTime.ranges = made.sized.key.ranges.x ∧
      k.oneTime.binding = made.sized.key.binding ∧ k.oneTime.codes = made.sized.key.codes ∧
      k.oneTime.lin = made.sized.key.once.shape ∧ k.shared.codes = made.sized.key.codes ∧
      k.shared.lin = made.sized.key.once.shape := by
  obtain ⟨P1, P2, P3, F, S2, S3, -, -, e1, e2, -⟩ := configure_bytes hc
  obtain ⟨r1, r2, -⟩ := KeyChains.read_three hread
  have g1 := OneTime.read_given r1
  rw [e1] at g1
  have i1 := Given.read_items (by rw [← e1]; exact hb₁) h32 (oneTimeItems_names _) g1
  have g2 := Shared.read_given r2
  rw [e2] at g2
  have i2 := Given.read_items (by rw [← e2]; exact hb₂) h32 (madeLinItems_names _ _) g2
  obtain ⟨a1, a2, a3, a4, a5⟩ := oneTime_items r1 i1
  obtain ⟨b1, b2⟩ := shared_items r2 i2
  simp only [itemsB, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨o1, o2⟩, o3⟩, o4⟩, o5⟩ := hok
  exact ⟨Option.some.inj (a1.symm.trans (readNotice_spell o1)),
    Option.some.inj (a2.symm.trans (readRanges_spell o2)),
    Option.some.inj (a3.symm.trans (readBinding_spell o3)),
    Option.some.inj (a4.symm.trans (readCodes_spell o4)),
    Option.some.inj (a5.symm.trans (readLin_spell o5)),
    Option.some.inj (b1.symm.trans (readCodes_spell o4)),
    Option.some.inj (b2.symm.trans (readLin_spell o5))⟩

/-- **AT THE WRITTEN SIZES OF A KEY OF FULL SIZE.** -/
theorem items_at_made {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hc : configure l x cfg bits = .ok made) (h32 : cfg.size = 32)
    (hb₁ : made.keyOneTime.size < 2 ^ 64) (hb₂ : made.keyShared.size < 2 ^ 64) {k : KeyChains}
    (hread : KeyChains.read made.keyOneTime made.keyShared made.keySecond = some k)
    (hz : made.sized.key = keyFull) :
    k.oneTime.indexMasks = keyFull.once.input ∧ k.oneTime.ranges = keyFull.ranges.x ∧
      k.oneTime.binding = keyFull.binding ∧ k.oneTime.binding.logLeaves = 0 ∧
      k.oneTime.codes = keyFull.codes ∧ k.oneTime.lin = keyFull.once.shape ∧
      k.shared.codes = keyFull.codes ∧ k.shared.lin = keyFull.once.shape := by
  have h := items_of_read hc h32 hb₁ hb₂ hread (by rw [hz]; exact itemsB_full)
  rw [hz] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, by rw [h3]; rfl, h4, h5, h6, h7⟩

end Johnson.KB9

#print axioms Johnson.KB9.oneTime_items
#print axioms Johnson.KB9.shared_items
#print axioms Johnson.KB9.items_of_read
#print axioms Johnson.KB9.items_at_made
