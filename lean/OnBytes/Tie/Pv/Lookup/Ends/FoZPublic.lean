-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoZPublic.lean.
The tests on public numbers of the lookup on the digits, at every smallness test of the byte-level
verifier's record of public numbers.

Where Verify.publicOf returns X, each member of X.G is what Layer.planG returns, X.H is what
Head.planH2 returns but for its state's weights, and a member of X.A is what Attention.plan returns
but for the record of its smallness test, into which Verify.attentionOwners has written
(OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean, OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean). So seven of
the ten clauses of Fo.ZTests hold at each of them
(Fo.ZPlan.ZMine, OnBytes/Tie/Pv/Lookup/Ends/FoZMade.lean).

Main names:
  `ownerPlace_sameP`, `ownerPlaces_sameP`, `owners_sameP`: attentionOwners keeps, in each plan, the
    fields that Fo.ZTests reads of the record (Fo.SameP).
  `public_G_zMine`, `public_A_zMine`, `public_H_zMine`: ZMine at X's own members.
  `Placed3 tl`: the three clauses that are left: tailTest, pieceTest, apartTest.
  `public_G_zTests`, `public_A_zTests`, `public_H_zTests`: Fo.ZTests at X's own members, under
    Placed3 of the member's record.
Under: Placed3 is a premise; it is not shown here of any record. tailTest alone is the six clauses
of OnBytes.DgP.TailOK (OnBytes/Tie/Pv/Lookup/Digits/PortLaws.lean).
The walk of the loop follows OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean's.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoZMade
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA

set_option autoImplicit false

namespace Fo.ZPlan
open OnBytes OnBytes.Model Fo.BatRows Fo.Pub

theorem ownerPlace_sameP {g : Nat} {O X X' : Verify.SubPlan}
    (h : Verify.attentionOwnerPlace g O X = .ok X') : SameP X.tl X'.tl := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact borderMeans_sameP h1

/-- What the loop keeps. -/
def SamePKept (A out : Array Verify.SubPlan) : Prop :=
  ∀ (i : Nat) (s : Verify.SubPlan), out[i]? = some s → ∃ s0, A[i]? = some s0 ∧ SameP s0.tl s.tl

theorem ownerPlaces_sameP (G A : Array Verify.SubPlan) : ∀ (l : List Nat)
    (out r : Array Verify.SubPlan), SamePKept A out →
    l.foldlM (fun (out : Array Verify.SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r → SamePKept A r
  | [], out, r, hk, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact hk
  | g :: l, out, r, hk, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    refine ownerPlaces_sameP G A l out1 r ?_ h
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
        exact ⟨s0, e0, a0.trans (ownerPlace_sameP h2)⟩
      · have e : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [e] at hi
        exact hk i s hi
    · cases h1

theorem owners_sameP {p4 : Bool} {NGr : Nat} {G A r : Array Verify.SubPlan}
    (h : Verify.attentionOwners p4 NGr G A = .ok r) : SamePKept A r := by
  unfold Verify.attentionOwners at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact ownerPlaces_sameP G A _ A r (fun i s hi => ⟨s, hi, SameP.refl _⟩) h
  · obtain rfl : A = r := Except.ok.inj h
    exact fun i s hi => ⟨s, hi, SameP.refl _⟩

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_zMine (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : ZMine hp.tl hp.Fp :=
  planG_zMine X.layers g _ hp (public_G h g hp hg)

theorem public_H_zMine (h : Verify.publicOf pol KL layout = .ok X) : ZMine X.H.tl X.H.Fp := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact planH2_zMine _ _ _ _ _ _ _ H0 h0 _ (frame_trimL H0.Fp)

theorem public_A_zMine (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : ZMine a.seam.tl a.seam.Fp := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_sameP k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show ZMine s.tl a0.seam.Fp
    rw [f3] at f2
    exact planA_zMine _ _ _ a0 m2 s.tl f2
  · simp at e1

/-- The three clauses of Fo.ZTests that are left. -/
structure Placed3 (tl : HTailF2) : Prop where
  t1 : OnBytes.DgP.tailTest tl = true
  t2 : ∀ q < 2, pieceTest tl q = true
  t3 : ∀ q < 2, apartTest tl q = true

theorem public_G_zTests (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) (T : Placed3 hp.tl) : ZTests hp.tl hp.tl hp.Fp :=
  zTests_of (public_G_zMine h g hp hg) T.t1 T.t2 T.t3

theorem public_A_zTests (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) (T : Placed3 a.seam.tl) :
    ZTests a.seam.tl a.seam.tl a.seam.Fp :=
  zTests_of (public_A_zMine h g a hg) T.t1 T.t2 T.t3

theorem public_H_zTests (h : Verify.publicOf pol KL layout = .ok X) (T : Placed3 X.H.tl) :
    ZTests X.H.tl X.H.tl X.H.Fp :=
  zTests_of (public_H_zMine h) T.t1 T.t2 T.t3

end

end Fo.ZPlan
