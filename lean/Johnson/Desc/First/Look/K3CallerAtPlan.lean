-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerAtPlan.lean: AT THE PLACE THAT lookAt MAKES OF A RECORD THAT
Verify.publicOf RETURNS, at the lookup on the calls of each of the three sorts of link: the place's
record of the lookup is the plan's own; the kind's own parameters make that very record; the planes'
cells lie in the list's matrix. Statements and proofs. NO SOUNDNESS IS CLAIMED.

Why. The closed callers' premises on public data (AttOK | LayOK | HeadOK) begin with «shape»: the
kind's own parameters make the place's record. So far that was had by putting the made record in the
place's stead. Here it is a theorem at the place as it is.

Main names:
  `lookAt_lay | lookAt_att | lookAt_head`: what lookAt's place holds, by unfolding, with the plan's
    member and what tlAt returns there.
  `lay_shape | att_shape | head_shape`: (P.ofPlace set false x).shape = some x.fs.
  `lay_planes | att_planes | head_planes`: planesAtB at tlAt's record, the place's fs and lm, and
    the caller's number of the planes' matrix.

Limits. One direction: from publicOf's equation. Nothing on the mask entries; nothing on the cells
that the keys read; nothing on the other fields of AttOK | LayOK | HeadOK.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerCellsLaw
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

section
variable {X : Verify.Public} {i : ℕ} {x : Place}

/-- A layers' link's place, by unfolding. -/
theorem lookAt_lay (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0) :
    ∃ hp, X.G[i / (if X.p4 then 2 else 1)]? = some hp ∧ tlAt X i = some hp.tl ∧
      x.fs = X.y.fo ∧ x.lm = X.y.h.lmb ∧ x.calls = X.y.cl ∧ x.pub = X.y.fo.pub ∧
      x.lid = X.y.h.lidb := by
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
    refine ⟨hp, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tlAt
    dsimp only
    rw [if_neg (by simpa using hn), if_pos (by simpa using h0), hg]
    rfl

/-- An attention link's place. -/
theorem lookAt_att (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) ≠ 0) :
    ∃ a, X.A[i / (if X.p4 then 2 else 1)]? = some a ∧ tlAt X i = some a.seam.tl ∧
      x.fs = a.fs ∧ x.lm = a.S.cf.lmb ∧ x.calls = a.S.calls.map (·.call) ∧ x.pub = a.fs.pub ∧
      x.lid = a.lid := by
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
    refine ⟨a, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    unfold tlAt
    dsimp only
    rw [if_neg (by simpa using hn), if_neg (by simpa using h0), hg]
    rfl

/-- The head's link's place. -/
theorem lookAt_head (e : lookAt X ((if X.p4 then 2 else 1) * X.NGr) false = some x) :
    tlAt X ((if X.p4 then 2 else 1) * X.NGr) = some X.H.tl ∧ x.fs = X.HLy.fs ∧
      x.lm = X.hS.lmbH ∧ x.calls = X.HLy.cl ∧ x.pub = X.HLy.fs.pub ∧ x.lid = X.hS.LIDB := by
  unfold lookAt at e
  dsimp only at e
  rw [if_pos (by simp)] at e
  simp at e
  subst e
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  unfold tlAt
  dsimp only
  rw [if_pos (by simp)]

end

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} {i : ℕ} {x : Place}
  (set : Params.Setting)

theorem lay_shape (h : Verify.publicOf pol KL layout = .ok X) (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0) :
    (P.ofPlace set false x).shape = some x.fs := by
  obtain ⟨hp, hg, _, e1, _, e3, e4, e5⟩ := lookAt_lay e hn h0
  refine shape_of_made (p := P.ofPlace set false x) ?_
  show _root_.Fo.ShapeOf x.calls x.pub x.lid x.fs
  rw [e1, e3, e4, e5]
  exact made_lay h _ hp hg

theorem lay_planes (h : Verify.publicOf pol KL layout = .ok X) (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0) :
    ∃ tl, tlAt X i = some tl ∧ planesAtB tl x.fs x.lm (Layer.matIx X.y).iB = true := by
  obtain ⟨hp, hg, ht, e1, e2, _⟩ := lookAt_lay e hn h0
  refine ⟨hp.tl, ht, ?_⟩
  rw [e1, e2]
  exact planesAtB_lay h _ hp hg

theorem att_shape (h : Verify.publicOf pol KL layout = .ok X) (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) ≠ 0) :
    (P.ofPlace set false x).shape = some x.fs := by
  obtain ⟨a, hg, _, e1, _, e3, e4, e5⟩ := lookAt_att e hn h0
  refine shape_of_made (p := P.ofPlace set false x) ?_
  show _root_.Fo.ShapeOf x.calls x.pub x.lid x.fs
  rw [e1, e3, e4, e5]
  exact made_att h _ a hg

theorem att_planes (h : Verify.publicOf pol KL layout = .ok X) (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) ≠ 0) :
    ∃ a tl, X.A[i / (if X.p4 then 2 else 1)]? = some a ∧ tlAt X i = some tl ∧
      planesAtB tl x.fs x.lm (a.S.cf.NAs + 2) = true := by
  obtain ⟨a, hg, ht, e1, e2, _⟩ := lookAt_att e hn h0
  refine ⟨a, a.seam.tl, hg, ht, ?_⟩
  rw [e1, e2]
  exact planesAtB_att h _ a hg

theorem head_shape (h : Verify.publicOf pol KL layout = .ok X)
    (e : lookAt X ((if X.p4 then 2 else 1) * X.NGr) false = some x) :
    (P.ofPlace set false x).shape = some x.fs := by
  obtain ⟨_, e1, _, e3, e4, e5⟩ := lookAt_head e
  refine shape_of_made (p := P.ofPlace set false x) ?_
  show _root_.Fo.ShapeOf x.calls x.pub x.lid x.fs
  rw [e1, e3, e4, e5]
  exact made_head h

theorem head_planes (h : Verify.publicOf pol KL layout = .ok X)
    (e : lookAt X ((if X.p4 then 2 else 1) * X.NGr) false = some x) :
    tlAt X ((if X.p4 then 2 else 1) * X.NGr) = some X.H.tl ∧
      planesAtB X.H.tl x.fs x.lm (X.hS.NHf + 2) = true := by
  obtain ⟨ht, e1, e2, _⟩ := lookAt_head e
  refine ⟨ht, ?_⟩
  rw [e1, e2]
  exact planesAtB_head h

end

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.lay_shape
#print axioms VerifiableInference.Desc.First.Look.lay_planes
#print axioms VerifiableInference.Desc.First.Look.att_shape
#print axioms VerifiableInference.Desc.First.Look.att_planes
#print axioms VerifiableInference.Desc.First.Look.head_shape
#print axioms VerifiableInference.Desc.First.Look.head_planes
