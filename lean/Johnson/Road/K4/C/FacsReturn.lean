-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/FacsReturn.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: the verifier's two
functions that make a claim's factor on a group of indices (facRs, facEw,
OnBytes/Model/LayerPanels.lean) RETURN, and what they return has the sizes that the group asks
(WsFac.fits, OnBytes/Model/Weights.lean). Both: where the group's number of indices is R = o 2^z
(hR). facRs: where besides there is at least one index (h0), the indices are at most two to the bits
that it is given, and these bits lie in the batched sumcheck's place. facEw: where besides some call
holds the segment, the group's low bits z are at most the call's column bits (hzl), the segment has
an entry for each index, its columns lie in the call, and the call's point has its column
coordinates. Statements and proofs. General in the sizes.

  `grp_bits`       a group with R = o 2^z indices, at least one and at most 2^w: its low bits and
                   its other part.
  `range_get_some` reading the first n members of an array.
  **`facRs_some`**, **`facEw_some`**   the two factors.

Not shown here. That the hypotheses hold at any plan or layout of the weights: no example is shown
here. Groups of the class 'E' alone. Public data alone: whether a factor IS THERE and how long its
parts are; nothing on its elements.
No property is claimed.
-/
import Johnson.Road.K4.C.ReadersReturn
import Johnson.Road.FormsKeysEq
import OnBytes.Desc.First.K4.StackPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv)
open OnBytes.Desc.First.K4.Total (amapM_all)

/-- A group with R = o 2^z indices, at least one and at most 2^w: it has at most w low bits, and its
other part is at most 2^(w - z). -/
theorem grp_bits {R o z w : ℕ} (hR : R = o * 2 ^ z) (h0 : 0 < R) (hle : R ≤ 2 ^ w) :
    z ≤ w ∧ o ≤ 2 ^ (w - z) := by
  have ho : 0 < o := by
    rcases Nat.eq_zero_or_pos o with e | e
    · rw [e, Nat.zero_mul] at hR
      omega
    · exact e
  have hz : z ≤ w := by
    have h1 : 2 ^ z ≤ 2 ^ w := by
      calc 2 ^ z = 1 * 2 ^ z := (Nat.one_mul _).symm
        _ ≤ o * 2 ^ z := Nat.mul_le_mul_right _ ho
        _ = R := hR.symm
        _ ≤ 2 ^ w := hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  refine ⟨hz, ?_⟩
  have h2 : o * 2 ^ z ≤ 2 ^ (w - z) * 2 ^ z := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hz, ← hR]
    exact hle
  exact Nat.le_of_mul_le_mul_right h2 (Nat.two_pow_pos z)

/-- Reading the first n members of an array that has them returns n members. -/
theorem range_get_some {α : Type} (e : Array α) {n : ℕ} (h : n ≤ e.size) :
    ∃ a, ((Array.range n).mapM fun i => e[i]?) = some a ∧ a.size = n := by
  obtain ⟨a, ha⟩ : ∃ a, ((Array.range n).mapM fun i => e[i]?) = some a := by
    apply some_of
    rw [amapM_all, List.all_eq_true]
    intro i hi
    have hi' : i < n := by simpa using hi
    rw [Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le hi' h)]
    rfl
  exact ⟨a, ha, OnBytes.Desc.First.K4.mapM_size ha⟩

/-- **The factor on the bits of the batched sumcheck's place is there, and fits its group.** -/
theorem facRs_some {c : ClaimEnv} {G : WsGrp} {lo0 wtot : ℕ} (hE : G.cls = 'E')
    (hR : G.R = G.o * 2 ^ G.z) (h0 : 0 < G.R) (hle : G.R ≤ 2 ^ wtot)
    (hrs : lo0 + wtot ≤ c.rs.size) :
    ∃ f, c.facRs G lo0 wtot = some f ∧ f.fits G = true := by
  obtain ⟨hz, ho⟩ := grp_bits hR h0 hle
  have hsz : (eqLow c.rs (lo0 + G.z) (lo0 + wtot)).size = 2 ^ (wtot - G.z) := by
    unfold eqLow
    rw [eqTab_size, Array.size_reverse, Array.size_extract, Nat.min_eq_left hrs]
    congr 1
    omega
  obtain ⟨HV, hHV, hs⟩ := range_get_some (eqLow c.rs (lo0 + G.z) (lo0 + wtot))
    (n := G.o) (by rw [hsz]; exact ho)
  have hc : (decide (G.z > wtot) || decide (lo0 + wtot > c.rs.size)) = false := by
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    exact ⟨by omega, by omega⟩
  refine ⟨{ pt := (Array.range G.z).map fun i => c.rs.getD (lo0 + G.z - 1 - i) zeroE, HV := HV },
    ?_, ?_⟩
  · unfold ClaimEnv.facRs
    rw [hc]
    dsimp only
    show (do
      let HV ← (Array.range G.o).mapM fun hi => (eqLow c.rs (lo0 + G.z) (lo0 + wtot))[hi]?
      pure ({ pt := (Array.range G.z).map fun i => c.rs.getD (lo0 + G.z - 1 - i) zeroE,
              HV := HV } : WsFac)) = _
    rw [hHV]
    rfl
  · unfold WsFac.fits
    rw [hE]
    show ((HV.size == G.o && ((Array.range G.z).map fun i =>
      c.rs.getD (lo0 + G.z - 1 - i) zeroE).size == G.z) && (#[] : Array E).isEmpty) = true
    rw [hs, Array.size_map, Array.size_range]
    simp

/-- **The factor on a segment's entries is there, and fits its group.** -/
theorem facEw_some {c : ClaimEnv} {G : WsGrp} {sn : String} {x0 q : ℕ} {cd : CallD} {s : Seg}
    (hc : c.v.callOf sn = some (q, cd, s)) (hE : G.cls = 'E') (hR : G.R = G.o * 2 ^ G.z)
    (hzl : G.z ≤ cd.lJ) (hx : x0 + G.R ≤ s.pos.size) (hJ : ∀ j ∈ s.pos.toList, j < 2 ^ cd.lJ)
    (hzk : (c.v.zj q cd.lJ).size = cd.lJ) :
    ∃ f, c.facEw G sn x0 = some f ∧ f.fits G = true := by
  have hsz : (eqTab ((c.v.zj q cd.lJ).extract 0 (cd.lJ - G.z))).size = 2 ^ (cd.lJ - G.z) := by
    rw [eqTab_size, Array.size_extract, hzk, Nat.min_eq_left (Nat.sub_le _ _), Nat.sub_zero]
  obtain ⟨HV, hHV⟩ : ∃ HV, ((Array.range G.o).mapM fun xh => do
      (eqTab ((c.v.zj q cd.lJ).extract 0 (cd.lJ - G.z)))[
        (← s.pos[x0 + xh * 2 ^ G.z]?) / 2 ^ G.z]?) = some HV := by
    apply some_of
    rw [amapM_all, List.all_eq_true]
    intro xh hxh
    have hxh' : xh < G.o := by simpa using hxh
    have hi : x0 + xh * 2 ^ G.z < s.pos.size := by
      have h1 : (xh + 1) * 2 ^ G.z ≤ G.o * 2 ^ G.z := Nat.mul_le_mul_right _ hxh'
      have h2 := Nat.two_pow_pos G.z
      rw [Nat.succ_mul] at h1
      omega
    have hp : s.pos[x0 + xh * 2 ^ G.z] < 2 ^ cd.lJ := hJ _ (by simp)
    have hd : s.pos[x0 + xh * 2 ^ G.z] / 2 ^ G.z < 2 ^ (cd.lJ - G.z) := by
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add, Nat.add_sub_cancel' hzl]
      exact hp
    rw [Array.getElem?_eq_getElem hi]
    show ((eqTab ((c.v.zj q cd.lJ).extract 0 (cd.lJ - G.z)))[
      s.pos[x0 + xh * 2 ^ G.z] / 2 ^ G.z]?).isSome = true
    rw [Array.getElem?_eq_getElem (by rw [hsz]; exact hd)]
    rfl
  have hs : HV.size = G.o := OnBytes.Desc.First.K4.mapM_size hHV
  have hcz : ¬ G.z > cd.lJ := by omega
  refine ⟨{ pt := (Array.range G.z).map fun i =>
      (c.v.zj q cd.lJ).getD (cd.lJ - G.z + i) zeroE, HV := HV }, ?_, ?_⟩
  · unfold ClaimEnv.facEw
    rw [hc]
    dsimp only
    show (if G.z > cd.lJ then none else do
      let HV ← (Array.range G.o).mapM fun xh => do
        (eqTab ((c.v.zj q cd.lJ).extract 0 (cd.lJ - G.z)))[
          (← s.pos[x0 + xh * 2 ^ G.z]?) / 2 ^ G.z]?
      pure ({ pt := (Array.range G.z).map fun i =>
                (c.v.zj q cd.lJ).getD (cd.lJ - G.z + i) zeroE, HV := HV } : WsFac)) = _
    rw [if_neg hcz, hHV]
    rfl
  · unfold WsFac.fits
    rw [hE]
    show ((HV.size == G.o && ((Array.range G.z).map fun i =>
      (c.v.zj q cd.lJ).getD (cd.lJ - G.z + i) zeroE).size == G.z) &&
      (#[] : Array E).isEmpty) = true
    rw [hs, Array.size_map, Array.size_range]
    simp

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.grp_bits
#print axioms OnBytes.Road.K4.C.range_get_some
#print axioms OnBytes.Road.K4.C.facRs_some
#print axioms OnBytes.Road.K4.C.facEw_some
