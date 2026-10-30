-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/FoShape.lean: the verifier's own tests give the premise FoNums.ok of the
lookup's statements.

The statements on the lookup of a sub-proof (HoleC₀, HoleCgl, forB_four_gl, forB_small_gl) ask
FoNums.ok h = true, one Bool on the forest's public numbers. (HoleC₀ also asks 2^d (2^32 - 1) < p;
forB_four_gl also a setting over the prime with degree 3, and that the planner does not refuse.)
Forest.pad (OnBytes/Model/Look.lean) makes its record of public numbers from the calls, the cap on a
tree's depth and the numbers of padding keys: it takes h₀ from Forest.shape, tests pub by
Forest.pubAsk, and goes on with { h₀ with pub := pub }. shape_ok: wherever both return a value,
FoNums.ok holds of that record. So, by this reading of Forest.pad's text, the premise holds at every
run of it that gets past its first two lines; no statement here is on Forest.pad itself.

How. The placing of the calls' trees (first, callOf) and the bounds that Forest.shape's refusals
leave are shape_prem and shape_adm (OnBytes/Tie/Pv/Lookup/Ends/ShapePrem.lean), proved on the
routine's body.
Added here: what callAsk leaves of each call (callAsk_ok), the fields that Forest.shape copies or
folds (shape_more, le_foldl_max, foldl_max_le), what pubAsk leaves (pubAsk_ok), the two clauses on
the padding by call (OnBytes/Tie/Pv/Lookup/Forest/FoPadSum.lean), and the way back from the clauses
to the Bool (ok_of_parts).

Main theorems: shape_ok, holeC_pad (HoleCgl's conclusion under the two successes).
Not claimed: that Forest.shape or Forest.pubAsk returns a value at any input.
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadSum
import OnBytes.Tie.Pv.Lookup.Forest.FoAt
import OnBytes.Tie.Pv.Lookup.Ends.ShapePrem

set_option autoImplicit false

namespace Cb.Fo
open OnBytes OnBytes.Model OnBytes.Ends

/-- What a call that callAsk takes has. -/
theorem callAsk_ok {c : Call} (h : Forest.callAsk c = .ok ()) : c.k ≤ 16 ∧ c.t0 < 2 ^ c.k := by
  unfold Forest.callAsk at h
  obtain ⟨c1, h⟩ := ok_of_jp h
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt, not_le, ge_iff_le, gt_iff_lt] at c1
  exact ⟨c1.1.1.1.1.2, c1.1.1.2⟩

theorem shape_more {calls : Array Call} {lid : ℕ} {fo : Forest.Shape}
    (h : Forest.shape calls lid = .ok fo) :
    fo.calls = calls ∧ fo.NC = calls.size ∧ fo.NC ≤ 2 ^ fo.cK ∧ fo.kT = calls.foldl
        (fun m c => max m c.k) 0 ∧
      ∀ c ∈ calls.toList, Forest.callAsk c = .ok () := by
  unfold Forest.shape at h
  obtain ⟨u, hfor, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r, -, h⟩ := ok_of_bind h
  obtain ⟨callOf, first, free⟩ := r
  obtain ⟨-, h⟩ := ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  refine ⟨rfl, rfl, le_two_pow_ceilLog2 _, rfl, ?_⟩
  rw [← Array.forIn_toList] at hfor
  exact forIn_keeps _ calls.toList (fun pre _ => ∀ c ∈ pre, Forest.callAsk c = .ok ())
    (fun pre a rest _ s s' hI hs => by
      obtain ⟨x, hx, hs⟩ := ok_of_bind hs
      refine ⟨_, (Except.ok.inj hs).symm, fun c hc => ?_⟩
      rcases List.mem_append.mp hc with hc | hc
      · exact hI c hc
      · have : c = a := by simpa using hc
        rw [this]
        exact hx)
    calls.toList [] _ _ rfl (fun c hc => by cases hc) hfor

theorem pubAsk_ok {h : Forest.Shape} {pub : Array ℕ} (hp : Forest.pubAsk h pub = .ok ()) :
    pub.size = h.NT ∧ h.calls.size = h.NC ∧ ∀ y, pub.getD y 0 ≤ 2 ^ h.dT := by
  unfold Forest.pubAsk at hp
  obtain ⟨c1, hp⟩ := ok_of_jp hp
  obtain ⟨c2, -⟩ := ok_of_jp hp
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at c1
  refine ⟨c1.1, c1.2, fun y => ?_⟩
  by_cases hy : y < pub.size
  · have e : pub.getD y 0 = pub[y] := by simp [Array.getD, hy]
    rw [e]
    by_contra hc
    exact c2 (Array.any_eq_true.2 ⟨y, hy, decide_eq_true (Nat.lt_of_not_le hc)⟩)
  · have e : pub.getD y 0 = 0 := by simp [Array.getD, hy]
    rw [e]
    exact Nat.zero_le _

theorem le_foldl_max (calls : Array Call) (c : ℕ) (hc : c < calls.size) :
    calls[c].k ≤ calls.foldl (fun m k => max m k.k) 0 := by
  have K := Array.foldl_induction (as := calls)
    (motive := fun i m => ∀ j (hj : j < calls.size), j < i → calls[j].k ≤ m)
    (init := 0) (f := fun m k => max m k.k)
    (fun j _ h => absurd h (Nat.not_lt_zero _))
    (fun i m ih j hj hlt => by
      by_cases e : j = i.1
      · subst e
        exact Nat.le_max_right _ _
      · exact Nat.le_trans (ih j hj (by omega)) (Nat.le_max_left _ _))
  exact K c hc hc

theorem foldl_max_le (calls : Array Call) (B : ℕ) (hB : ∀ c (hc : c < calls.size), calls[c].k ≤ B) :
    calls.foldl (fun m k => max m k.k) 0 ≤ B :=
  Array.foldl_induction (as := calls) (motive := fun _ m => m ≤ B) (init := 0)
      (f := fun m k => max m k.k)
    (Nat.zero_le _) (fun i _ ih => Nat.max_le.2 ⟨ih, hB i.1 i.2⟩)

/-- From the clauses back to the Bool. -/
theorem ok_of_parts {h : Sh}
    (a : 10 ≤ h.dT ∧ 1 ≤ h.NC ∧ h.NC ≤ 2 ^ h.cK ∧ h.NT ≤ 2 ^ h.rK ∧ h.v < 32 ∧ h.pub.size = h.NT ∧
        h.calls.size = h.NC)
    (b : ∀ y < h.NT, FoNums.co h y < h.NC ∧ FoNums.fst h (FoNums.co h y) ≤ y ∧ y < FoNums.fst h
        (FoNums.co h y) + 2 ^ FoNums.io h (FoNums.co h y))
    (c : ∀ c < h.NC, FoNums.t0Of h c < 2 ^ FoNums.kOf h c ∧ FoNums.kOf h c ≤ h.kT ∧ FoNums.nOf h c =
        FoNums.io h c + h.dT ∧
      ∀ b < 2 ^ FoNums.io h c, FoNums.fst h c + b < h.NT ∧ FoNums.co h (FoNums.fst h c + b) = c ∧
          (FoNums.fst h c + b) % 2 ^ FoNums.io h c = b)
    (d : ∀ e ∈ FoNums.pads h, e.1 < 2 ^ h.d) (e : ((FoNums.pads h).map Prod.snd).sum ≤ 2 ^ h.v)
    (f : h.kT ≤ 16 ∧ h.NC ≤ 16 ∧ 2 ^ (h.d + 32) < OnBytes.pW.toNat) : FoNums.ok h = true := by
  simp only [FoNums.ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      List.mem_range]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := a
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, fun y hy =>
      ⟨⟨(b y hy).1, (b y hy).2.1⟩, (b y hy).2.2⟩⟩,
    fun k hk => ⟨⟨⟨(c k hk).1, (c k hk).2.1⟩, (c k hk).2.2.1⟩, fun x hx =>
        ⟨⟨((c k hk).2.2.2 x hx).1, ((c k hk).2.2.2 x hx).2.1⟩, ((c k hk).2.2.2 x hx).2.2⟩⟩⟩, d⟩, e⟩,
        f.1⟩, f.2.1⟩, f.2.2⟩

/-- The verifier's own tests give the premise. -/
theorem shape_ok {calls : Array Call} {lid : ℕ} {h₀ : Forest.Shape} {pub : Array ℕ}
    (hs : Forest.shape calls lid = .ok h₀) (hp : Forest.pubAsk h₀ pub = .ok ()) :
    FoNums.ok { h₀ with pub := pub } = true := by
  obtain ⟨s1, s2, s3, _, s5, s6⟩ := shape_adm hs
  have P := shape_prem hs
  obtain ⟨m1, m2, m3, m4, m5⟩ := shape_more hs
  obtain ⟨p1, p2, p3⟩ := pubAsk_ok hp
  have hcall : ∀ c, (hc : c < h₀.NC) → ∃ k :
      Call, h₀.calls[c]? = some k ∧ k.k ≤ 16 ∧ k.t0 < 2 ^ k.k ∧ k.k ≤ h₀.kT := by
    intro c hc
    have hc' : c < calls.size := by rw [← m2]; exact hc
    refine ⟨calls[c], by rw [m1]; simp [hc'], (callAsk_ok (m5 _ (by simp))).1,
        (callAsk_ok (m5 _ (by simp))).2, ?_⟩
    rw [m4]
    exact le_foldl_max calls c hc'
  have hb : ∀ y < h₀.NT, FoNums.co h₀ y < h₀.NC ∧ FoNums.fst h₀ (FoNums.co h₀ y) ≤ y ∧
      y < FoNums.fst h₀ (FoNums.co h₀ y) + 2 ^ FoNums.io h₀ (FoNums.co h₀ y) := by
    intro y hy
    obtain ⟨c, hc, lo, hi⟩ := P.cover y hy
    have e : FoNums.co h₀ y = c := by
      have := P.own c hc (y - firstN h₀ c) (by omega)
      rwa [Nat.add_sub_cancel' lo] at this
    rw [e]
    exact ⟨hc, lo, hi⟩
  have hk16 : h₀.kT ≤ 16 := by
    rw [m4]
    exact foldl_max_le calls 16 fun c hc => (callAsk_ok (m5 _ (by simp))).1
  refine ok_of_parts ⟨s3, s5, m3, P.nt, s1, p1, p2⟩ hb (fun c hc => ?_) (fun e he => ?_) ?_
      ⟨hk16, s6, s2⟩
  · obtain ⟨k, hk, _, k2, k3⟩ := hcall c hc
    have e1 : FoNums.t0Of h₀ c = k.t0 := by simp [FoNums.t0Of, hk]
    have e2 : FoNums.kOf h₀ c = k.k := by simp [FoNums.kOf, hk]
    refine ⟨?_, ?_, ?_, fun b hb' => ⟨?_, P.own c hc b hb', ?_⟩⟩
    · show FoNums.t0Of h₀ c < 2 ^ FoNums.kOf h₀ c
      rw [e1, e2]
      exact k2
    · show FoNums.kOf h₀ c ≤ h₀.kT
      rw [e2]
      exact k3
    · exact (P.n c hc).trans (Nat.add_comm _ _)
    · have := P.inNT c hc
      show firstN h₀ c + b < h₀.NT
      have hb'' : b < 2 ^ iotaN h₀ c := hb'
      omega
    · show (firstN h₀ c + b) % 2 ^ iotaN h₀ c = b
      have hb'' : b < 2 ^ iotaN h₀ c := hb'
      rw [Nat.add_mod, P.dvd c hc, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hb'']
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
    have hc' : c < h₀.NC := List.mem_range.1 hc
    obtain ⟨k, hk, _, k2, k3⟩ := hcall c hc'
    have e1 : FoNums.t0Of h₀ c = k.t0 := by simp [FoNums.t0Of, hk]
    show c + 2 ^ h₀.cK * FoNums.t0Of h₀ c < 2 ^ (h₀.kT + h₀.cK)
    rw [e1, Nat.pow_add, Nat.mul_comm (2 ^ h₀.kT)]
    have h1 : k.t0 + 1 ≤ 2 ^ h₀.kT := Nat.le_trans k2 (Nat.pow_le_pow_right (by norm_num) k3)
    have h2 : 2 ^ h₀.cK * (k.t0 + 1) ≤ 2 ^ h₀.cK * 2 ^ h₀.kT := Nat.mul_le_mul_left _ h1
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  · have e := pads_sum_of (h := { h₀ with pub := pub }) s5 p1 fun y hy => (hb y hy).1
    unfold Cb.Lkp.padNum at e
    rw [e]
    exact padding_le (h := { h₀ with pub := pub }) P.nt p1 p3

open Iop IOR in
/-- Knowledge soundness of the lookup at the record of public numbers with which Forest.pad goes on.
-/
theorem holeC_pad {calls : Array Call} {lid : ℕ} {h₀ : Forest.Shape} {pub : Array ℕ}
    (hs : Forest.shape calls lid = .ok h₀) (hp : Forest.pubAsk h₀ pub = .ok ())
    (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (L : Lay Cb.Gl.E St₀ J₀) (Ex : ExtSpec)
        (Kc M Wp : Type)
    (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → Cb.Gl.E) :
    TWhole.KnowAt (forB Cb.Gl.E { h₀ with pub := pub } L TWhole.V₀ TWhole.V₀C (Ex := Ex)).R
      (forIn Cb.Gl.E { h₀ with pub := pub } L R0 msg₀)
          (forOut Cb.Gl.E { h₀ with pub := pub } L R0 msg₀)
      (fun _ _ _ wp => wp)
          (forB Cb.Gl.E { h₀ with pub := pub } L TWhole.V₀ TWhole.V₀C (Ex := Ex)).e :=
  holeCgl St₀ J₀ _ L Ex Kc M Wp R0 msg₀ (shape_ok hs hp)

end Cb.Fo
