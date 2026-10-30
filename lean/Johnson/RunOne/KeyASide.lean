-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyASide.lean: THE KEY FILE's FIRST CHAIN: THE STATE's SIDE OF THE TABLES' PROMISE, AND ITS STEP AT A BLOCK's YES. ASide one at_ k s: the four parts of on₁ … k that read the chain's state ALONE and that KeyFillOn.lean's head lists as the premises T1 · T2 · T3 · T5 of on₁_of_tests: the book-keeping shape₁ … k · Placed at the open pins · Means.InOrder · MaskWith 1 2 (borders 2 … 15). FIVE OF THE NINETEEN STEPS ARE THEOREMS HERE, each from what the tables' paid rows already hold of that block's yes; for a block that keeps the book and the open pins there is the general aSide_step.
OBJECT: on₁'s state's side · USER: Johnson/Top/Fire/Code/KeyASideHist.lean (and, through it, two theorems that are not in this library) · LETTERS: one · at_.
  ASide · aSide_step (book kept; the open pins kept)
  aSide_call0 | aSide_call1 | aSide_rows | aSide_send0 | aSide_send1   PROVED: in the «yes» forms of the tables (CallerYes · RowsYes · Sent0 · Laid1)
NOT HERE: the steps at K3's blocks (4 | 10) · the layers (5 | 11) · the ranges' test (15) · the batching (16) · W's sending (17): not proved here.
EMPTY WHERE ASide k HOLDS OF NOTHING; that it holds along the honest walk is told by two records of this project.
Nothing on soundness.
-/
import Johnson.RunOne.KeyTenAt
import Johnson.RunOne.KeySendYes1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open OnBytes.Model (Fork)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain

/-- **The state's side of the promise at border k.** -/
def ASide (one : OneTime) (at_ : Where) (k : Nat) (s : FirstState) : Prop :=
  shape₁' one k s = true ∧ Placed (plan₁ one).orc (fun o => s.d.book.place[o]?) id at_ (pinned (open₁ 2 k)) ∧ Means.InOrder s.d.st ∧
    (2 ≤ k ∧ k ≤ 15 → MaskWith (fun o => s.d.book.place[o]?) 1 2)

variable (one : OneTime) (at_ : Where)

/-- Where the book and the open pins are kept. -/
theorem aSide_step (k : Nat) (s s' : FirstState) (hp : pinned (open₁ 2 (k + 1)) = pinned (open₁ 2 k)) (hk : 2 ≤ k + 1 ∧ k + 1 ≤ 15 → 2 ≤ k ∧ k ≤ 15)
    (hsh : shape₁' one k s = true → shape₁' one (k + 1) s' = true) (hb : s'.d.book = s.d.book) (ho : Means.InOrder s.d.st → Means.InOrder s'.d.st)
    (h : ASide one at_ k s) : ASide one at_ (k + 1) s' :=
  ⟨hsh h.1, by rw [hp, hb]; exact h.2.1, ho h.2.2.1, fun h2 => by rw [hb]; exact h.2.2.2 (hk h2)⟩

theorem aSide_call0 (s : FirstState) (d' : PlainState) (Fk : Fork) (hm : Array Slot) (H : CallGround s d') (Hf : ForkReady (slots₁ one 0) Fk hm)
    (h : ASide one at_ 3 s) : ASide one at_ 4 (withCall s d' Fk hm) :=
  aSide_step one at_ 3 s _ (by decide) (by omega) (sh_3_4 one s d' Fk hm H Hf) H.book (order_call s d' H) h

theorem aSide_call1 (s : FirstState) (d' : PlainState) (Fk : Fork) (hm : Array Slot) (H : CallGround s d') (Hf : ForkReady (slots₁ one 1) Fk hm)
    (h : ASide one at_ 9 s) : ASide one at_ 10 (withCall s d' Fk hm) :=
  aSide_step one at_ 9 s _ (by decide) (by omega) (sh_9_10 one s d' Fk hm H Hf) H.book (order_call s d' H) h

theorem aSide_rows (s : FirstState) (d' : PlainState) (H : RowsGround s d') (h2 : s.base.rows.length = 2) (h : ASide one at_ 14 s) : ASide one at_ 15 (withD s d') :=
  aSide_step one at_ 14 s _ (by decide) (by omega) (sh_14_15 one s d' H h2) H.book H.order h

theorem aSide_send0 (hat : at_ 0 = (0, 0)) (s s' : FirstState) (H : Sent0 s s') (h : ASide one at_ 0 s) : ASide one at_ 1 s' := by
  refine ⟨shape_send0 one s s' H h.1, fun k hk => ?_, H.order, fun h2 => absurd h2.1 (by decide)⟩
  rw [pinned_behind0] at hk
  obtain rfl : k = 0 := by simpa using hk
  exact ⟨0, (0, 0), rfl, H.place0, hat⟩

theorem aSide_send1 (hst : 1 ≤ one.ranges.stages.length) (hat : at_ 1 = (1, 0)) (s s' : FirstState) (H : Laid1 s s') (h : ASide one at_ 1 s) : ASide one at_ 2 s' := by
  refine ⟨shape_send1 one hst s s' H h.1, fun k hk => ?_, H.order, fun _ => ⟨1, 0, H.place1, H.place2⟩⟩
  rw [pinned_behind1] at hk
  rcases (by simpa using hk : k = 0 ∨ k = 1) with rfl | rfl
  · obtain ⟨o, t, ho, ht, ha⟩ := h.2.1 0 (by rw [pinned_behind0]; simp)
    obtain rfl : (0 : Nat) = o := Option.some.inj ho
    exact ⟨0, t, rfl, H.place0.trans ht, ha⟩
  · exact ⟨1, (1, 0), rfl, H.place1, hat⟩

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.aSide_step
#print axioms Johnson.RunOne.KeyRows1.aSide_call0
#print axioms Johnson.RunOne.KeyRows1.aSide_call1
#print axioms Johnson.RunOne.KeyRows1.aSide_rows
#print axioms Johnson.RunOne.KeyRows1.aSide_send0
#print axioms Johnson.RunOne.KeyRows1.aSide_send1
