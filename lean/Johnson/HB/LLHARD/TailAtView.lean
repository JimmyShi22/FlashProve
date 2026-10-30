-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/TailAtView.lean: what `Meaning.labAt X k a` and `Meaning.sizesOf X k`
(Johnson/Goal/Meaning/HidPlan.lean) hold of the public data X stands in the view of their shape
(`xShapeOf`, Johnson/Desc/Ok/PlanWritten/XShape.lean), where attention is there and there are twelve
groups of layers.

Row or tool. General laws, at every X. No written value is named; nothing is evaluated. No test's
text is restated here.

What is here.
  `tl_same`: for k below 25, under the two conditions on X, the two readers of segment k's
    approximate range proof in the public data agree: `Meaning.tlAt X k` is `First.Look.tlAt X k`,
    or the empty one where that has none.
  `viewTail V k`, `viewEntry V k a`: segment k's tail in a view, the empty one where the view has
    none; its entry a: label, rows, columns.
  `viewTail_at`, `entry_of`, `viewEntry_at`: at `xShapeOf X` they are what `Meaning.tlAt X k` holds:
    the number of matrices; the label `labAt X k a`, and the rows and columns of `sizesOf X k`.
  `all_range_same`: a tool on `List.all` over a range.

Limits. Nothing on soundness.


-/
import Johnson.Goal.Meaning.HidPlan
import Johnson.Desc.Ok.PlanWritten.XShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Meaning
open OnBytes OnBytes.Model
open VerifiableInference.PlanWritten (XShape TailView tailView xShapeOf)

/-- **The two readers of a segment's tail agree.** -/
theorem tl_same {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {k : ℕ} (hk : k < 25) :
    tlAt X k = (VerifiableInference.Desc.First.Look.tlAt X k).getD {} := by
  unfold tlAt VerifiableInference.Desc.First.Look.tlAt
  simp only [h4, hN, if_true]
  rw [if_neg (by omega : ¬ 24 < k)]
  by_cases h24 : k = 24
  · subst h24
    simp
  · have e : (k == 2 * 12) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    rw [if_neg h24]
    simp only [e, Bool.false_eq_true, if_false]
    by_cases h2 : k % 2 = 0
    · simp [h2]
    · simp [h2]

/-- Segment k's tail in a view; the empty one where the view has none. -/
def viewTail (V : XShape) (k : ℕ) : TailView := ((V.1[k]?).getD none).getD (0, [], [])

/-- Its entry a: label, rows, columns. -/
def viewEntry (V : XShape) (k a : ℕ) : ℕ × ℕ × ℕ := (viewTail V k).2.1.getD a (0, 0, 0)

theorem viewTail_at {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {k : ℕ}
    (hk : k < 25) : viewTail (xShapeOf X) k = tailView (tlAt X k) := by
  rw [tl_same h4 hN hk]
  unfold viewTail xShapeOf
  simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
  cases VerifiableInference.Desc.First.Look.tlAt X k <;> rfl

theorem entry_of (t : HTailF2) (a : ℕ) :
    (tailView t).2.1.getD a (0, 0, 0) =
      ((t.mats.getD a {}).aId, (t.mats.getD a {}).m, (t.mats.getD a {}).k) := by
  show (t.mats.toList.map fun x => (x.aId, x.m, x.k)).getD a (0, 0, 0) = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases t.mats[a]? <;> rfl

theorem viewEntry_at {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {k : ℕ}
    (hk : k < 25) (a : ℕ) :
    viewEntry (xShapeOf X) k a = (labAt X k a, (sizesOf X k).m a, (sizesOf X k).k a) := by
  unfold viewEntry
  rw [viewTail_at h4 hN hk, entry_of]
  rfl

theorem all_range_same {n : ℕ} {f g : ℕ → Bool} (h : ∀ k < n, f k = g k) :
    (List.range n).all f = (List.range n).all g := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun H k hk => (h k (List.mem_range.1 hk)).symm.trans (H k hk),
    fun H k hk => (h k (List.mem_range.1 hk)).trans (H k hk)⟩

end Meaning

#print axioms Meaning.tl_same
#print axioms Meaning.viewTail_at
#print axioms Meaning.entry_of
#print axioms Meaning.viewEntry_at
#print axioms Meaning.all_range_same
