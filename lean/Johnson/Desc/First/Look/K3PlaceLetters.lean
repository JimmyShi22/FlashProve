-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3PlaceLetters.lean: THE LETTERS OF THE LOOKUP ON A LINK's CALLS ARE THE
PLAN's, wherever Verify.publicOf returns: the shape that the kind's parameters fix, the number lm,
the first slot and the link's number of slots, at each of the three sorts of link. Statements and
proofs. Ties of texts: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: placeAt X i false (Johnson/Desc/First/Look/LookKind.lean) and lookAt X i false
  (Johnson/Desc/First/Look/LookAt.lean).
USER: Johnson/Desc/First/Look/K3LeftItem.lean (the item "what the lookup on the calls left" is
  worded at the kind's parameters; the callers' laws speak at the plan's letters).
LETTERS: pol, KL, layout, X, i: free,
  under publicOf's equation and the link's sort.
Compiled with the whole library.

Main names:
  `first_lay | first_att | first_head`: x.F.next = 0.
  `place_lay`: placeAt X i false = some p at a layers' link: there is the group's plan hp with
    p.shape = some X.y.fo, p.lm = X.y.h.lmb, p.first = 0, p.ns = hp.ns.
  `place_att`: at an attention link: a.fs, a.S.cf.lmb, 0, a.ns.
  `place_head`: at the head's link: X.HLy.fs, X.hS.lmbH, 0, X.H.ns.

The place's state and number of slots by unfolding: lookAt_lay_F | lookAt_att_F | lookAt_head_F
(Johnson/Desc/First/Look/K3CallerMasksLaw.lean).

Limits. On public numbers alone: NOTHING ON ANY RECORD: that the ledger in hand in front of the
lookup has its count at 0 is the promise's (k3OnIn: "G.next == p.first"), not this file's. One
direction: from publicOf's equation.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAtPlan
import Johnson.Desc.First.Look.K3CallerMasksLaw
import Johnson.Desc.First.Look.K3PlaceAt
import OnBytes.Tie.Pv.Lookup.Ends.FoNext0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} {i : ℕ} {x : Place}

/-- **The lookup on a layers' link's calls begins at slot 0.** -/
theorem first_lay (h : Verify.publicOf pol KL layout = .ok X) (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0) :
    x.F.next = 0 := by
  obtain ⟨hp, hg, -, eF, -⟩ := lookAt_lay_F e hn h0
  rw [eF]
  exact (_root_.Fo.Next0.planned_door0 h).1 _ hp hg

theorem first_att (h : Verify.publicOf pol KL layout = .ok X) (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) ≠ 0) :
    x.F.next = 0 := by
  obtain ⟨a, hg, -, eF, -⟩ := lookAt_att_F e hn h0
  rw [eF]
  exact (_root_.Fo.Next0.planned_door0 h).2 _ a hg

/-- At the head by unfolding: no premise on the record. -/
theorem first_head (e : lookAt X ((if X.p4 then 2 else 1) * X.NGr) false = some x) :
    x.F.next = 0 := by
  rw [(lookAt_head_F e).2.1]
  rfl

/-- **THE KIND's PARAMETERS AT A LAYERS' LINK HAVE THE PLAN's LETTERS.** -/
theorem place_lay {p : P} (h : Verify.publicOf pol KL layout = .ok X)
    (e : placeAt X i false = some p) (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : i % (if X.p4 then 2 else 1) = 0) :
    ∃ hp, X.G[i / (if X.p4 then 2 else 1)]? = some hp ∧ p.shape = some X.y.fo ∧
      p.lm = X.y.h.lmb ∧ p.first = 0 ∧ p.ns = hp.ns := by
  obtain ⟨x, ex, rfl⟩ := placeAt_iff.1 e
  obtain ⟨hp, hg, -, -, en⟩ := lookAt_lay_F ex hn h0
  obtain ⟨-, -, -, e1, e2, -⟩ := lookAt_lay ex hn h0
  refine ⟨hp, hg, ?_, e2, first_lay h ex hn h0, en⟩
  rw [lay_shape _ h ex hn h0, e1]

/-- **At an attention link.** -/
theorem place_att {p : P} (h : Verify.publicOf pol KL layout = .ok X)
    (e : placeAt X i false = some p) (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : i % (if X.p4 then 2 else 1) ≠ 0) :
    ∃ a, X.A[i / (if X.p4 then 2 else 1)]? = some a ∧ p.shape = some a.fs ∧
      p.lm = a.S.cf.lmb ∧ p.first = 0 ∧ p.ns = a.ns := by
  obtain ⟨x, ex, rfl⟩ := placeAt_iff.1 e
  obtain ⟨a, hg, -, -, en⟩ := lookAt_att_F ex hn h0
  obtain ⟨a', hg', -, e1, e2, -⟩ := lookAt_att ex hn h0
  obtain rfl : a' = a := Option.some.inj (hg'.symm.trans hg)
  refine ⟨a', hg, ?_, e2, first_att h ex hn h0, en⟩
  rw [att_shape _ h ex hn h0, e1]

/-- **At the head's link.** -/
theorem place_head {p : P} (h : Verify.publicOf pol KL layout = .ok X)
    (e : placeAt X ((if X.p4 then 2 else 1) * X.NGr) false = some p) :
    p.shape = some X.HLy.fs ∧ p.lm = X.hS.lmbH ∧ p.first = 0 ∧ p.ns = X.H.ns := by
  obtain ⟨x, ex, rfl⟩ := placeAt_iff.1 e
  obtain ⟨-, e1, e2, -⟩ := lookAt_head ex
  refine ⟨?_, e2, first_head ex, (lookAt_head_F ex).2.2⟩
  rw [head_shape _ h ex, e1]

end

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.place_lay
#print axioms VerifiableInference.Desc.First.Look.place_att
#print axioms VerifiableInference.Desc.First.Look.place_head
