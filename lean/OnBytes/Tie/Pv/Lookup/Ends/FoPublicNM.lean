-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPublicNM.lean.
The plans of a record that Verify.publicOf returns: the number of matrices in the record of a
smallness test is the length of its list of matrices.

The record of a smallness test (OnBytes.Model.HTailF2) keeps the number NM beside the list mats. The
sizes that the typed smallness test reads off such a record (OnBytes/Tie/Pv/Tail/SizeOf.lean) take
NM; tests on names of cells take the list's length. Here the two are one number at every plan that
the verifier makes.

States:
  planG_NM, seamShape_NM, planA_NM: at what Layer.planG, Attention.Seam.shape and Attention.plan
    return. seamPlan_NM: Attention.Seam.plan keeps the number and the list.
  public_G_NM, public_A_NM, public_H_NM: at the plans of the groups of layers, of attention and of
    the head of such a record: from Verify.publicOf's equation and, for the first two, the
    membership in X.G | X.A.
  ownerPlace_NM, ownerPlaces_NM, owners_NM: the owners' pass behind the attention plans
    (Verify.attentionOwners) keeps the number and the list.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicAMats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.PubNM
open OnBytes OnBytes.Model Fo.BatRows _root_.Fo

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (cases e; done)
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

/-- At a group's plan. -/
theorem planG_NM (P : Layer.Pub) (g : ℕ) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : hp.tl.NM = hp.tl.mats.size := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, hb, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨s1, s2⟩ := shape_mats _ _ _ _ _ _ _ hS
  obtain ⟨a1, a2⟩ := addTrees_keeps _ _ _ _ _ _ _ _ hA
  have k1 : tl1.NM = tl1.mats.size := by rw [a2, a1, s2, s1]
  have k2 : (tl1.ownerIs g).NM = (tl1.ownerIs g).mats.size := k1
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact k2
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      obtain ⟨b1, b2⟩ := borderMeans_mats hB
      rw [b2, b1]
      exact k2
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem seamShape_NM {g : Settings} {m : Array TMat} {tau col0F ktO aO : ℕ}
    {s : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s) :
    s.tl.NM = s.tl.mats.size := by
  unfold Attention.Seam.shape at e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨tl, h0, e⟩ := bindE_ok e
  cases e
  obtain ⟨s1, s2⟩ := shape_mats _ _ _ _ _ _ _ h0
  show tl.NM = tl.mats.size
  rw [s2, s1]

theorem seamPlan_NM {s r : Attention.Seam} {nU3 hb hbLine : ℕ}
    (e : s.plan nU3 hb hbLine = .ok r) : r.tl.NM = s.tl.NM ∧ r.tl.mats = s.tl.mats := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl, Fp, T⟩, h0, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨Tp, _, e⟩ := bindE_ok e
  cases e
  exact ⟨(addTrees_keeps _ _ _ _ _ _ _ _ h0).2, (addTrees_keeps _ _ _ _ _ _ _ _ h0).1⟩

/-- At an attention plan. -/
theorem planA_NM (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) :
    P.seam.tl.NM = P.seam.tl.mats.size := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings i cf P e
  obtain ⟨a, b⟩ := seamPlan_NM h1
  rw [a, b]
  exact seamShape_NM h0

/-! ### attentionOwners keeps the number and the list -/

/-- b has a's number of matrices and a's list. -/
def NKeep (a b : HTailF2) : Prop := b.NM = a.NM ∧ b.mats = a.mats

theorem ownerPlace_NM {g : ℕ} {O X X' : Verify.SubPlan}
    (h : Verify.attentionOwnerPlace g O X = .ok X') : NKeep X.tl X'.tl := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact ⟨(borderMeans_mats h1).2, (borderMeans_mats h1).1⟩

/-- What the loop keeps. -/
def NKept (A out : Array Verify.SubPlan) : Prop :=
  ∀ (i : ℕ) (s : Verify.SubPlan), out[i]? = some s → ∃ s0, A[i]? = some s0 ∧ NKeep s0.tl s.tl

theorem ownerPlaces_NM (G A : Array Verify.SubPlan) : ∀ (l : List ℕ)
    (out r : Array Verify.SubPlan), NKept A out →
    l.foldlM (fun (out : Array Verify.SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r → NKept A r
  | [], out, r, hk, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact hk
  | g :: l, out, r, hk, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    refine ownerPlaces_NM G A l out1 r ?_ h
    split at h1
    · rename_i O X hO hX
      obtain ⟨X', h2, h1⟩ := bindE_ok h1
      obtain rfl := Except.ok.inj h1
      intro i s hi
      by_cases hig : i = g
      · subst hig
        obtain ⟨s0, e0, a0⟩ := hk i X hX
        have hlt : i < out.size := by
          obtain ⟨hl, _⟩ := Array.getElem?_eq_some_iff.1 hX
          exact hl
        have e : (out.set! i X')[i]? = some X' := by
          simp [Array.set!, hlt]
        rw [e] at hi
        obtain rfl := Option.some.inj hi
        obtain ⟨b1, b2⟩ := ownerPlace_NM h2
        exact ⟨s0, e0, b1.trans a0.1, b2.trans a0.2⟩
      · have e : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [e] at hi
        exact hk i s hi
    · cases h1

theorem owners_NM {p4 : Bool} {NGr : ℕ} {G A r : Array Verify.SubPlan}
    (h : Verify.attentionOwners p4 NGr G A = .ok r) : NKept A r := by
  unfold Verify.attentionOwners at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact ownerPlaces_NM G A _ A r (fun i s hi => ⟨s, hi, rfl, rfl⟩) h
  · obtain rfl : A = r := Except.ok.inj h
    exact fun i s hi => ⟨s, hi, rfl, rfl⟩

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **At an attention plan.** -/
theorem public_A_NM (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) : a.seam.tl.NM = a.seam.tl.mats.size := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := Pub.publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_NM k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold Pub.seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := Pub.config_at k9
    obtain ⟨cf, m1, m2⟩ := Pub.group_plan (l2 g a0 e1)
    subst e3
    show s.tl.NM = s.tl.mats.size
    rw [f3] at f2
    rw [f2.1, f2.2]
    exact planA_NM _ _ _ a0 m2
  · simp at e1

/-- **At the plan of a group of layers.** -/
theorem public_G_NM (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : hp.tl.NM = hp.tl.mats.size :=
  planG_NM X.layers g _ hp (Pub.public_G h g hp hg)

/-- **At the head's plan.** -/
theorem public_H_NM (h : Verify.publicOf pol KL layout = .ok X) :
    X.H.tl.NM = X.H.tl.mats.size := by
  obtain ⟨_, _, _, hn⟩ := Pub.public_mats h
  exact hn

end

end Fo.PubNM
