-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerMasksLaw.lean: THE TEST «THE LOOKUP's MASK ENTRIES LIE IN THE MASK
ROW» (Johnson/Desc/First/Look/K3CallerCellsIn.lean: masksAtB) SAYS YES AT EVERY RECORD THAT
Verify.publicOf RETURNS, at the lookups on the calls of all three sorts of link: at the plans, and
at
the place that lookAt makes. Statements and proofs: the library's own theorems, put together. NO
SOUNDNESS IS CLAIMED.

Why. A closed caller reads a mask entry beyond the mask row as 0. The library shows of every such
record that the lookup's scalars are at most the plan's number of slots
(OnBytes/Tie/Pv/Lookup/Ends/FoBoxSlots.lean: public_elems), that the state from which the lookup is
called begins at slot 0 (FoNext0.lean: planned_door0), and that there are as many mask entries as
scalars (OnBytes/Tie/Pv/Lookup/Forest/FoLedger.lean: elems_eq).

Main names: `masksAtB_lay | masksAtB_att | masksAtB_head` (at the plans) · `lookAt_lay_F |
lookAt_att_F
| lookAt_head_F` (the place's state and number of slots, by unfolding) · `lay_masks | att_masks |
head_masks`: masksAtB x.fs x.F.next x.ns = true at the place.

Limits. One direction: from publicOf's equation. At the head the first slot is 0 by the record's
default, as lookAt lays it.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAtPlan
import OnBytes.Tie.Pv.Lookup.Ends.FoBoxSlots
import OnBytes.Tie.Pv.Lookup.Forest.FoLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- Arithmetic. -/
theorem masksAtB_of_nums {fs : Forest.Shape} {first ns : ℕ} (h0 : first = 0)
    (h1 : Forest.elems fs ≤ ns) : masksAtB fs first ns = true := by
  unfold masksAtB
  rw [decide_eq_true_eq, h0, _root_.FoLedger.elems_eq, Nat.zero_add]
  exact h1

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem masksAtB_lay (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) :
    masksAtB X.layers.y.fo (hp.Fp.fillL.slots hp.ns).next hp.ns = true :=
  masksAtB_of_nums ((_root_.Fo.Next0.planned_door0 h).1 g hp hg)
    ((_root_.Fo.Pub2.public_elems h).1 g hp hg)

theorem masksAtB_att (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) : masksAtB a.fs (a.seam.Fp.fillL.slots a.ns).next a.ns = true :=
  masksAtB_of_nums ((_root_.Fo.Next0.planned_door0 h).2 g a hg)
    ((_root_.Fo.Pub2.public_elems h).2.1 g a hg)

theorem masksAtB_head (h : Verify.publicOf pol KL layout = .ok X) :
    masksAtB X.HLy.fs ((({ trees := X.H.Fp.trees } : Fork).fillL).slots X.H.ns).next X.H.ns =
      true :=
  masksAtB_of_nums rfl (_root_.Fo.Pub2.public_elems h).2.2

end

section
variable {X : Verify.Public} {i : ℕ} {x : Place}

theorem lookAt_lay_F (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0) :
    ∃ hp, X.G[i / (if X.p4 then 2 else 1)]? = some hp ∧ x.fs = X.y.fo ∧
      x.F = hp.Fp.fillL.slots hp.ns ∧ x.ns = hp.ns := by
  unfold lookAt at e
  dsimp only at e
  rw [if_neg (by simpa using hn), if_pos (by simpa using h0)] at e
  cases hg : X.G[i / (if X.p4 then 2 else 1)]? with
  | none =>
    rw [hg] at e
    simp at e
  | some hp =>
    rw [hg] at e
    simp at e
    subst e
    exact ⟨hp, rfl, rfl, rfl, rfl⟩

theorem lookAt_att_F (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) ≠ 0) :
    ∃ a, X.A[i / (if X.p4 then 2 else 1)]? = some a ∧ x.fs = a.fs ∧
      x.F = a.seam.Fp.fillL.slots a.ns ∧ x.ns = a.ns := by
  unfold lookAt at e
  dsimp only at e
  rw [if_neg (by simpa using hn), if_neg (by simpa using h0)] at e
  cases hg : X.A[i / (if X.p4 then 2 else 1)]? with
  | none =>
    rw [hg] at e
    simp at e
  | some a =>
    rw [hg] at e
    simp at e
    subst e
    exact ⟨a, rfl, rfl, rfl, rfl⟩

theorem lookAt_head_F (e : lookAt X ((if X.p4 then 2 else 1) * X.NGr) false = some x) :
    x.fs = X.HLy.fs ∧ x.F = (({ trees := X.H.Fp.trees } : Fork).fillL).slots X.H.ns ∧
      x.ns = X.H.ns := by
  unfold lookAt at e
  dsimp only at e
  rw [if_pos (by simp)] at e
  simp at e
  subst e
  exact ⟨rfl, rfl, rfl⟩

end

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} {i : ℕ} {x : Place}

theorem lay_masks (h : Verify.publicOf pol KL layout = .ok X) (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0) :
    masksAtB x.fs x.F.next x.ns = true := by
  obtain ⟨hp, hg, e1, e2, e3⟩ := lookAt_lay_F e hn h0
  rw [e1, e2, e3]
  exact masksAtB_lay h _ hp hg

theorem att_masks (h : Verify.publicOf pol KL layout = .ok X) (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) ≠ 0) :
    masksAtB x.fs x.F.next x.ns = true := by
  obtain ⟨a, hg, e1, e2, e3⟩ := lookAt_att_F e hn h0
  rw [e1, e2, e3]
  exact masksAtB_att h _ a hg

theorem head_masks (h : Verify.publicOf pol KL layout = .ok X)
    (e : lookAt X ((if X.p4 then 2 else 1) * X.NGr) false = some x) :
    masksAtB x.fs x.F.next x.ns = true := by
  obtain ⟨e1, e2, e3⟩ := lookAt_head_F e
  rw [e1, e2, e3]
  exact masksAtB_head h

end

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.lay_masks
#print axioms VerifiableInference.Desc.First.Look.att_masks
#print axioms VerifiableInference.Desc.First.Look.head_masks
