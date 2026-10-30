-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPublicAPlFor.lean.
The attention plans of a record that Verify.publicOf returns: a member of X.A is what Attention.plan
returns, but for one field of the record of its smallness test.

Behind the plans Verify.attentionOwners (OnBytes/Model/VerifyCross.lean) fills, in each attention
plan, the record of where the matrix that another sub-proof owns lies: HTailF2.borderMeans writes
the field plFor and nothing else. So a statement on what Attention.plan returns carries over to the
member of X.A wherever it does not read plFor.

States:
  PlForOnly a b: b is a with the field plFor laid anew.
  borderMeans_plFor, ownerPlace_plFor, ownerPlaces_plFor, owners_plFor: the steps of the owners'
    pass.
  public_A_plFor: at a member a of X.A: Attention.plan, at the record's settings, at the written
    record of what the plan gets besides and at a's own configuration, returns a plan a0, and a is
    a0 with a's own plFor in the record of the smallness test. All other fields of the plan, of its
    seam (the arrays Fp, their list Tp, the lengths nU) and of that record are a0's.
  plFor_fields: six of these fields one by one: ix, blocks, nUF of the record; Fp, Tp, nU of the
    seam.
  public_A_seam: so the seam of a0 comes from Attention.Seam.plan (Fo.BatRows.planA_rows0), and a's
    seam is that seam but for plFor.
Under: in the three statements on a member of X.A: Verify.publicOf's equation and the membership;
nothing else.
Limits. The equation of Attention.Seam.plan is stated of a0's seam, not of a's: borderMeans sets an
owner that no plan sets. In public_A_plFor a0 is the value of Attention.plan's equation. In
public_A_seam the seam seam0 from which Attention.Seam.plan starts stands under "there is" with that
one equation: that it is what Attention.Seam.shape returns (Fo.BatRows.planA_rows0) is not carried
into the statement; public_A_seam_at (OnBytes/Tie/Pv/Lookup/Ends/FoPublicASeam.lean) carries it.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicAMats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.PubA
open OnBytes OnBytes.Model Fo.BatRows _root_.Fo

/-- b is a with the field plFor laid anew. -/
def PlForOnly (a b : HTailF2) : Prop := b = { a with plFor := b.plFor }

theorem PlForOnly.refl (a : HTailF2) : PlForOnly a a := rfl

theorem PlForOnly.trans {a b c : HTailF2} (h1 : PlForOnly a b) (h2 : PlForOnly b c) :
    PlForOnly a c := by
  unfold PlForOnly at h1 h2 ⊢
  rw [h1] at h2
  exact h2

theorem borderMeans_plFor {tl tl' : HTailF2} {iF o i : ℕ}
    (h : tl.borderMeans iF o i = .ok tl') : PlForOnly tl tl' := by
  unfold HTailF2.borderMeans at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      rfl

theorem ownerPlace_plFor {g : ℕ} {O X X' : Verify.SubPlan}
    (h : Verify.attentionOwnerPlace g O X = .ok X') : PlForOnly X.tl X'.tl := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact borderMeans_plFor h1

/-- What the loop keeps. -/
def PKept (A out : Array Verify.SubPlan) : Prop :=
  ∀ (i : ℕ) (s : Verify.SubPlan), out[i]? = some s →
    ∃ s0, A[i]? = some s0 ∧ PlForOnly s0.tl s.tl

theorem ownerPlaces_plFor (G A : Array Verify.SubPlan) : ∀ (l : List ℕ)
    (out r : Array Verify.SubPlan), PKept A out →
    l.foldlM (fun (out : Array Verify.SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r → PKept A r
  | [], out, r, hk, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact hk
  | g :: l, out, r, hk, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    refine ownerPlaces_plFor G A l out1 r ?_ h
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
        exact ⟨s0, e0, a0.trans (ownerPlace_plFor h2)⟩
      · have e : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [e] at hi
        exact hk i s hi
    · cases h1

theorem owners_plFor {p4 : Bool} {NGr : ℕ} {G A r : Array Verify.SubPlan}
    (h : Verify.attentionOwners p4 NGr G A = .ok r) : PKept A r := by
  unfold Verify.attentionOwners at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact ownerPlaces_plFor G A _ A r (fun i s hi => ⟨s, hi, PlForOnly.refl _⟩) h
  · obtain rfl : A = r := Except.ok.inj h
    exact fun i s hi => ⟨s, hi, PlForOnly.refl _⟩

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **A member of X.A is what Attention.plan returns, but for plFor.** -/
theorem public_A_plFor (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    ∃ a0, Attention.plan X.P.settings
        (Attention.inOf X.P.settings X.layers.y (Pub.midQ X.layers.y g) g) a.S.cf = .ok a0 ∧
      a = { a0 with seam := { a0.seam with
        tl := { a0.seam.tl with plFor := a.seam.tl.plFor } } } := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := Pub.publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_plFor k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold Pub.seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := Pub.config_at k9
    obtain ⟨cf, m1, m2⟩ := Pub.group_plan (l2 g a0 e1)
    obtain ⟨hS, _⟩ := Pub.planA_shapeHid _ _ cf a0 m2
    have hcf : a0.S.cf = cf := (Pub2.shapeOf_shapeHid hS).2
    subst e3
    refine ⟨a0, ?_, ?_⟩
    · show Attention.plan _ _ a0.S.cf = _
      rw [hcf]
      exact m2
    · rw [f3] at f2
      have f4 : s.tl = { a0.seam.tl with plFor := s.tl.plFor } := f2
      show ({ a0 with seam := { a0.seam with tl := s.tl } } : Attention.Plan) =
        { a0 with seam := { a0.seam with tl := { a0.seam.tl with plFor := s.tl.plFor } } }
      rw [← f4]
  · simp at e1

/-- Six fields, for whoever wants them one by one. -/
theorem plFor_fields {a a0 : Attention.Plan}
    (ha : a = { a0 with seam := { a0.seam with
      tl := { a0.seam.tl with plFor := a.seam.tl.plFor } } }) :
    a.seam.tl.ix = a0.seam.tl.ix ∧ a.seam.tl.blocks = a0.seam.tl.blocks ∧
      a.seam.tl.nUF = a0.seam.tl.nUF ∧ a.seam.Fp = a0.seam.Fp ∧ a.seam.Tp = a0.seam.Tp ∧
      a.seam.nU = a0.seam.nU := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> conv_lhs => rw [ha]

/-- **The seam's own plan equation, at a0; a's seam is that seam but for plFor.** -/
theorem public_A_seam (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    ∃ (seam0 s1 : Attention.Seam), seam0.plan a.nW (X.P.settings.hb - X.P.settings.pow)
        X.P.settings.hb = .ok s1 ∧
      a.seam = { s1 with tl := { s1.tl with plFor := a.seam.tl.plFor } } := by
  obtain ⟨a0, hp, ha⟩ := public_A_plFor h g a hg
  obtain ⟨seam0, _, h1, _⟩ := BatRows.planA_rows0 _ _ _ a0 hp
  have eW : a.nW = a0.nW := by rw [ha]
  refine ⟨seam0, a0.seam, ?_, ?_⟩
  · rw [eW]
    exact h1
  · conv_lhs => rw [ha]

end

end Fo.PubA
