-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPublicANm.lean.
In each attention plan of the verifier's record of public numbers (a member of X.A, where
Verify.publicOf returns X) the smallness test's record counts its own list of matrices.

A member of X.A is what Attention.plan returns but for the record of its smallness test, into which
Verify.attentionOwners has written (OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean). That file hands on
that the writing keeps the matrices and the number of combinations. This file adds the number of
matrices.

Main names:
  `ownerPlace_nm`, `ownerPlaces_nm`, `owners_nm`: attentionOwners keeps, in each plan, the field NM
    of the smallness test's record.
  `public_A_size`: Verify.publicOf pol KL layout = .ok X and X.A[g]? = some a give
    a.seam.tl.NM = a.seam.tl.mats.size: at X's own member, the premise hN of Fo.topOf_eq
    (OnBytes/Tie/Pv/Lookup/Ends/FoTopOf.lean), of Fo.a_door_rows
    (OnBytes/Tie/Pv/Lookup/Ends/FoRowsRun.lean) and of Fo.a_bat_rows
    (OnBytes/Tie/Pv/Lookup/Ends/FoBatRun.lean).
The induction over the loop follows that of OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA
import OnBytes.Tie.Pv.Lookup.Ends.FoPlanSize

set_option autoImplicit false

namespace Fo.Pub
open OnBytes OnBytes.Model Fo.BatRows

theorem ownerPlace_nm {g : Nat} {O X X' : Verify.SubPlan}
    (h : Verify.attentionOwnerPlace g O X = .ok X') : X'.tl.NM = X.tl.NM := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact (borderMeans_core h1).1

/-- What the loop keeps. -/
def NmKept (A out : Array Verify.SubPlan) : Prop :=
  ∀ (i : Nat) (s : Verify.SubPlan), out[i]? = some s → ∃ s0, A[i]? = some s0 ∧ s.tl.NM = s0.tl.NM

theorem ownerPlaces_nm (G A : Array Verify.SubPlan) : ∀ (l : List Nat)
    (out r : Array Verify.SubPlan), NmKept A out →
    l.foldlM (fun (out : Array Verify.SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r → NmKept A r
  | [], out, r, hk, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact hk
  | g :: l, out, r, hk, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    refine ownerPlaces_nm G A l out1 r ?_ h
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
        exact ⟨s0, e0, (ownerPlace_nm h2).trans a0⟩
      · have e : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [e] at hi
        exact hk i s hi
    · cases h1

theorem owners_nm {p4 : Bool} {NGr : Nat} {G A r : Array Verify.SubPlan}
    (h : Verify.attentionOwners p4 NGr G A = .ok r) : NmKept A r := by
  unfold Verify.attentionOwners at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact ownerPlaces_nm G A _ A r (fun i s hi => ⟨s, hi, rfl⟩) h
  · obtain rfl : A = r := Except.ok.inj h
    exact fun i s hi => ⟨s, hi, rfl⟩

theorem public_A_size {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (a : Attention.Plan)
    (hg : X.A[g]? = some a) : a.seam.tl.NM = a.seam.tl.mats.size := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_keeps k6 g s e2
  obtain ⟨s1, g1, g2⟩ := owners_nm k6 g s e2
  obtain rfl : s0 = s1 := Option.some.inj (f1.symm.trans g1)
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show s.tl.NM = s.tl.mats.size
    rw [g2, f2.1, f3]
    exact planA_size _ _ _ a0 m2
  · simp at e1

end Fo.Pub
