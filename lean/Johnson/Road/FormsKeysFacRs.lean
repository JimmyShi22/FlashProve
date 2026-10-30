-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysFacRs.lean: what the factors of the verifier's weight claims weigh an index
with.

A weight claim has one factor for each index group of its unit (OnBytes/Model/Weights.lean). The
list of weight claims of a layer sub-proof (OnBytes/Model/LayerPanels.lean) makes these factors in
four ways. This file says, for two of them, what the factor weighs an index with, in the sense of
facAt (Johnson/Road/FormsKeysPan.lean):
 - facRs, from a stretch of the coordinates of the batched sumcheck's place: the equality weight of
   the whole stretch at the index (facRs_at), also in the library's way of writing (facRs_lib);
 - facEw, from the columns of a lookup segment: facEw_at of Johnson/Road/FormsKeysPan.lean says it
   under three hypotheses on the segment's columns; here these are concluded for a segment whose
   columns lie in aligned blocks (facEw_aligned).

What is compared with what: the verifier's facRs and facEw with eqR, a way of writing the library's
equality kernel (Johnson/Road/FormsKeysEnd.lean), and with the weights of the lookup's join.

What is not claimed: that facAt is what the verifier's settling of a claim on the matrix of weights
comes to (Johnson/Road/FormsKeysFac.lean); the factors on the heads and on the rotary pairs. The
program does not import this file.
-/
import Johnson.Road.FormsKeysEnd

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading eqTab eqLow WsGrp WsFac Seg CallD)
open OnBytes.Model.Layer (ClaimEnv Env)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The factor that is made from the coordinates lo0 to lo0 + wtot - 1 of the batched sumcheck's
place weighs every index v of its group with the equality weight of all these wtot coordinates at v.
Asked: the group has class 'E', and v is below o 2^z, the number of its indices. Nothing is asked of
that number: it need not be a power of two. -/
theorem facRs_at (c : ClaimEnv) (G : WsGrp) (lo0 wtot : ℕ) (hE : (G.cls == 'E') = true)
    {X : WsFac} (h : c.facRs G lo0 wtot = some X) (v : ℕ) (hv : v < G.o * 2 ^ G.z) :
    facAt ρ X G v = eqR ρ c.rs lo0 (lo0 + wtot) v := by
  have h' : (do
      if G.z > wtot || lo0 + wtot > c.rs.size then none
      let HV ← (Array.range G.o).mapM fun hi => (eqLow c.rs (lo0 + G.z) (lo0 + wtot))[hi]?
      pure ({ pt := (Array.range G.z).map fun i => c.rs.getD (lo0 + G.z - 1 - i) zeroE,
              HV := HV } : WsFac)) = some X := h
  have hc : ¬ (G.z > wtot || lo0 + wtot > c.rs.size) = true := by
    intro hc
    simp only [hc, ↓reduceIte] at h'
    cases h'
  simp only [hc] at h'
  have hz : G.z ≤ wtot := by
    by_contra hh
    exact hc (by simp; omega)
  have hsz : lo0 + wtot ≤ c.rs.size := by
    by_contra hh
    exact hc (by simp; omega)
  obtain ⟨_, _, h2⟩ := bind_some h'
  obtain ⟨HV, hm, h3⟩ := bind_some h2
  cases h3
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at hm
  obtain ⟨l, hl, hHV⟩ := map_some hm
  subst hHV
  have hpos : 0 < 2 ^ G.z := by positivity
  have hhi : v / 2 ^ G.z < G.o := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    exact hv
  have hr : v % 2 ^ G.z < 2 ^ G.z := Nat.mod_lt _ hpos
  have hsplit : v = v / 2 ^ G.z * 2 ^ G.z + v % 2 ^ G.z := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod v (2 ^ G.z)).symm
  obtain ⟨b, hb, hf⟩ := (list_mapM_some _ _ l hl).2 (v / 2 ^ G.z) (v / 2 ^ G.z) (by simp [hhi])
  have hHVb : (l.toArray).getD (v / 2 ^ G.z) zeroE = b := getD_of_some (by simpa using hb) zeroE
  have hbe := getD_of_some hf zeroE
  have hlt : v / 2 ^ G.z < 2 ^ (lo0 + wtot - (lo0 + G.z)) := by
    have h1 : v / 2 ^ G.z < (eqLow c.rs (lo0 + G.z) (lo0 + wtot)).size := by
      by_contra hh
      rw [Array.getElem?_eq_none (by omega)] at hf
      cases hf
    unfold eqLow at h1
    rw [eqTab_size, rev_size c.rs hsz] at h1
    exact h1
  have e1 : lo0 + G.z - lo0 = G.z := by omega
  have hmid := eqR_split ρ c.rs (lo := lo0) (mid := lo0 + G.z) (hi := lo0 + wtot) (by omega)
    (by omega) (v / 2 ^ G.z) (c' := v % 2 ^ G.z) (by rw [e1]; exact hr)
  rw [e1, ← hsplit] at hmid
  rw [hmid]
  unfold facAt
  rw [if_pos hE, hHVb, ← hbe, eqLow_value ρ c.rs hsz hlt]
  congr 1
  unfold eqR
  rw [e1]
  refine eqN_congr' _ _ (fun j hj => ?_) _
  unfold pt
  rw [Nat.zero_add, getD_map_lt _ _ (by simpa using hj) zeroE 0]
  simp [Array.getD, hj]

/-- The same in the library's way of writing: one point for all lam coordinates of the place, the
top bit's coordinate first. -/
theorem facRs_lib (c : ClaimEnv) (G : WsGrp) (lo0 wtot lam : ℕ) (hE : (G.cls == 'E') = true)
    (hlam : lo0 + wtot ≤ lam) {X : WsFac} (h : c.facRs G lo0 wtot = some X) (v : ℕ)
    (hv : v < G.o * 2 ^ G.z) :
    facAt ρ X G v = Blocks.eqN wtot (lam - (lo0 + wtot))
      (fun t => ρ.val (c.rs.getD (lam - 1 - t) zeroE)) v := by
  rw [facRs_at ρ c G lo0 wtot hE h v hv, eqR_lib ρ c.rs hlam v]
  have e : lo0 + wtot - lo0 = wtot := by omega
  rw [e]

/-- The factor that is made from the columns of segment sn, from its entry x0 on, for a segment
whose columns are aligned on blocks of 2^z entries, where z is the group's number of low bits: it
weighs the index idx with the weight that the lookup's join gives to entry x0 + idx of the segment.
Asked beside: 2^z divides x0; the stretch from x0 on, of o 2^z entries, lies within the segment; the
call's point is long enough. -/
theorem facEw_aligned (c : ClaimEnv) (G : WsGrp) (sn : String) (x0 q : ℕ) (cd : CallD) (s : Seg)
    (hcall : c.v.callOf sn = some (q, cd, s)) (hE : (G.cls == 'E') = true)
    (hsz : c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size) (A : Aligned s G.z cd.lJ)
    (hx0 : 2 ^ G.z ∣ x0) (hn : x0 + G.o * 2 ^ G.z ≤ s.n)
    {X : WsFac} (h : c.facEw G sn x0 = some X) (idx : ℕ) (hidx : idx < G.o * 2 ^ G.z) :
    facAt ρ X G idx = ρ.val ((Env.ewFrom (eqTab (c.v.zj q cd.lJ)) s).getD (x0 + idx) zeroE) := by
  obtain ⟨a, ha⟩ := hx0
  have hpos : 0 < 2 ^ G.z := by positivity
  have blk : ∀ xh, xh < G.o → x0 + xh * 2 ^ G.z = 2 ^ G.z * (a + xh) ∧ a + xh < s.n / 2 ^ G.z := by
    intro xh hxh
    have e : x0 + xh * 2 ^ G.z = 2 ^ G.z * (a + xh) := by
      rw [ha]
      ring
    refine ⟨e, ?_⟩
    rw [Nat.lt_div_iff_mul_lt hpos]
    have h1 : (xh + 1) * 2 ^ G.z ≤ G.o * 2 ^ G.z := Nat.mul_le_mul_right _ hxh
    have h2 : (xh + 1) * 2 ^ G.z = xh * 2 ^ G.z + 2 ^ G.z := by ring
    have h3 : (a + xh) * 2 ^ G.z = x0 + xh * 2 ^ G.z := by
      rw [e]
      ring
    omega
  refine facEw_at ρ c G sn x0 q cd s hcall hE hsz ?_ ?_ ?_ h idx hidx
  · intro xh r hxh hr
    obtain ⟨e, hlt⟩ := blk xh hxh
    rw [e]
    exact A.run _ _ hlt hr
  · intro xh hxh
    obtain ⟨e, hlt⟩ := blk xh hxh
    rw [e]
    exact A.start _ hlt
  · intro x hx
    have hxn : x < s.n := by omega
    exact ⟨by rw [A.size]; exact hxn, A.inside x hxn⟩

#print axioms facRs_at
#print axioms facRs_lib
#print axioms facEw_aligned

end OnBytes.Road
