-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoSlEntry.lean.
An entry of the head's long table of the matrix hf, under the law of the reads.

The matrix hf holds, in NHf parts of equal size, one cell for each feature and position. Its long
table at the merged point has one entry for each block of S2 neighbouring features: the block's
cells under the weights "equality weight of the feature's place in the block times equality weight
of the position" (longPhi, OnBytes/Model/Tensors.lean).

Defines:
  HfFacts R: facts on public numbers: each part of hf has the layout's rows and columns in the
    plan's list; a part's rows are whole blocks of 2^la rows; la = ls + lt; the merged point has la
    coordinates.
States:
  flat_get, blockRows_get: the weights of a block's rows, row by row.
  partStart_const: where a part of a table begins, if all parts have one size.
  hfZ_entry: entry number e of the table is the sum over the places c2 in the block and the
    positions t of weight times the cell of feature S2 e + c2 at position t (OnBytes.Ends.H.hfC).
    Premises: HfFacts; the records of the table's NHf parts, from entry p0 on, are in the list of
    the head's tables; the law of the reads; e lies below the table's length.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLineKit

set_option autoImplicit false

namespace Fo
open TwV Finset OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Ends OnBytes.Ends.H

theorem flat_get {α β : Type} (g : α → List β) (T : ℕ) :
    ∀ (A : List α), (∀ a ∈ A, (g a).length = T) → ∀ i t, t < T →
      (A.flatMap g)[T * i + t]? = (A[i]?).bind fun a => (g a)[t]?
  | [], _, i, t, _ => by simp
  | a :: A, h, 0, t, ht => by
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add,
      List.getElem?_append_left (by rw [h a List.mem_cons_self]; exact ht)]
    rfl
  | a :: A, h, i + 1, t, ht => by
    have hl : (g a).length = T := h a List.mem_cons_self
    rw [List.flatMap_cons, List.getElem?_append_right (by rw [hl, Nat.mul_succ]; omega), hl,
      show T * (i + 1) + t - T = T * i + t by rw [Nat.mul_succ]; omega,
      flat_get g T A (fun b hb => h b (List.mem_cons_of_mem _ hb)) i t ht]
    rfl

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The weight of the row (c2, t) of a block. -/
theorem blockRows_get (low tok : Array E) (c2 t : ℕ) (hc : c2 < low.size) (ht : t < tok.size) :
    ρ.val ((blockRows low tok).getD (tok.size * c2 + t) zeroE) =
      ρ.val (low.getD c2 zeroE) * ρ.val (tok.getD t zeroE) := by
  have e : (blockRows low tok)[tok.size * c2 + t]? = some (mulE low[c2] tok[t]) := by
    unfold blockRows
    rw [← Array.getElem?_toList, Array.toList_flatMap,
      flat_get (fun a => (tok.map fun b => mulE a b).toList) tok.size low.toList
        (fun a _ => by simp) c2 t ht, Array.getElem?_toList, Array.getElem?_eq_getElem hc]
    show (tok.map fun b => mulE low[c2] b).toList[t]? = _
    rw [Array.getElem?_toList, Array.getElem?_map, Array.getElem?_eq_getElem ht]
    rfl
  rw [Array.getD_eq_getD_getElem?, e, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]
  exact ρ.mul _ _

end

theorem partStart_const (mats : Array TMat) (M0 Lf p0 n : ℕ) :
    ∀ p, (∀ i < p, partLen mats Lf (M0 + i) = n) → partStart mats M0 Lf p0 p = p0 + p * n
  | 0, _ => by simp [partStart]
  | p + 1, h => by
    rw [partStart, partStart_const mats M0 Lf p0 n p fun i hi => h i (Nat.lt_succ_of_lt hi),
      h p (Nat.lt_succ_self p), Nat.succ_mul, Nat.add_assoc]

/-- The table of equality weights at a point of n coordinates has 2^n entries. -/
theorem eqTab_size (z : Array E) : (eqTab z).size = 2 ^ z.size := by
  have h := eqTab_val Reading.gl z
  have h1 := congrArg List.length h
  rw [rdL_length, eqTabK_len, rdL_length] at h1
  exact h1

/-- Facts on public numbers at the matrix hf, and the length of the merged point. -/
structure HfFacts (R : Head.Run) : Prop where
  m : ∀ p < R.h.NHf, (R.hp.tl.mats.getD p {}).m = R.L.m
  k : ∀ p < R.h.NHf, (R.hp.tl.mats.getD p {}).k = R.L.k
  blocks : R.L.m = R.L.m / 2 ^ R.h.la * 2 ^ R.h.la
  la : R.h.la = R.h.ls + R.h.lt
  zl : R.x.Zl.size = R.h.la

/-- The index arithmetic between a feature's cell and an entry's block. -/
theorem hf_index (S2 T nsg k e c2 t : ℕ) (hS : 0 < S2) (hc : c2 < S2) :
    (S2 * e + c2) / (k * (S2 * nsg)) = e / (k * nsg) ∧
      (S2 * e + c2) % (S2 * nsg) * T + t = e % (k * nsg) % nsg * (T * S2) + (T * c2 + t) ∧
      (S2 * e + c2) / (S2 * nsg) % k = e % (k * nsg) / nsg := by
  have d1 : (S2 * e + c2) / S2 = e := by
    rw [Nat.mul_add_div hS, Nat.div_eq_of_lt hc, Nat.add_zero]
  have d2 : (S2 * e + c2) / (S2 * nsg) = e / nsg := by rw [← Nat.div_div_eq_div_mul, d1]
  have d3 : (S2 * e + c2) % (S2 * nsg) = S2 * (e % nsg) + c2 := by
    have h1 := Nat.div_add_mod (S2 * e + c2) (S2 * nsg)
    have h2 := Nat.div_add_mod e nsg
    rw [d2] at h1
    have h3 : S2 * e = S2 * (nsg * (e / nsg)) + S2 * (e % nsg) := by
      rw [← Nat.mul_add, h2]
    have h4 : S2 * nsg * (e / nsg) = S2 * (nsg * (e / nsg)) := Nat.mul_assoc _ _ _
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [show k * (S2 * nsg) = S2 * nsg * k by ring, ← Nat.div_div_eq_div_mul, d2,
      Nat.div_div_eq_div_mul, Nat.mul_comm nsg k]
  · rw [d3, Nat.mod_mul_left_mod]
    ring
  · rw [d2, Nat.mod_mul_left_div_self]

/-- **An entry of the long table of hf at the merged point.** -/
theorem hfZ_entry (R : Head.Run) (lay : WsLay) (hF : HfFacts R) (p0 : ℕ)
    (ht : ∀ p < R.h.NHf, partRec R.hp.tl.mats 0 (2 ^ R.h.la) p0
      (longPhi R.x.Zl R.h.ls R.h.lt) p ∈ R.t.funs.toList)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (K3 : ℕ) (cell : NameH → Cb.Gl.E)
    (hU : ReadsAll Reading.gl R.hp.tl.mats (funsH R) entry R.iU3 K3
      (fun m r c => cell (.cell m r c)))
    (e : ℕ) (he : e < R.h.NHf * (R.L.k * (R.L.m / 2 ^ R.h.la))) :
    u3Val entry R.iU3 K3 (p0 + e) =
      ∑ c2 ∈ range R.h.S2, ∑ t ∈ range R.h.T,
        Reading.gl.val ((eqTab (R.x.Zl.extract 0 R.h.ls)).getD c2 zeroE) *
          Reading.gl.val ((eqTab (R.x.Zl.extract R.h.ls (R.h.ls + R.h.lt))).getD t zeroE) *
          hfC (pubH R lay) cell (R.h.S2 * e + c2) t := by
  obtain ⟨n, hn⟩ : ∃ n, n = R.L.k * (R.L.m / 2 ^ R.h.la) := ⟨_, rfl⟩
  rw [← hn] at he
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, Nat.mul_zero] at he
      exact absurd he (Nat.not_lt_zero e)
    · exact h0
  have hp : e / n < R.h.NHf := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hlen : ∀ i < R.h.NHf, partLen R.hp.tl.mats (2 ^ R.h.la) (0 + i) = n := by
    intro i hi
    unfold partLen
    rw [Nat.zero_add, hF.m i hi, hF.k i hi, hn]
  have hst := partStart_const R.hp.tl.mats 0 (2 ^ R.h.la) p0 n (e / n)
    fun i hi => hlen i (Nat.lt_trans hi hp)
  have hread := read_part Reading.gl R entry K3 (fun m r c => cell (.cell m r c)) hU 0
    (2 ^ R.h.la) p0 (longPhi R.x.Zl R.h.ls R.h.lt) (e / n) (ht _ hp) (by omega) (e % n)
    (by rw [hlen _ hp]; exact Nat.mod_lt _ hn0)
  rw [hst, Nat.add_assoc, Nat.mul_comm (e / n) n, Nat.div_add_mod, Nat.zero_add,
    hF.m _ hp] at hread
  rw [hread]
  -- the block's rows, in two indices
  have hS2 : R.h.S2 = 2 ^ R.h.ls := rfl
  have hT : R.h.T = 2 ^ R.h.lt := rfl
  have hLa : 2 ^ R.h.la = R.h.T * R.h.S2 := by rw [hF.la, hS2, hT, pow_add, Nat.mul_comm]
  have hlow : (eqTab (R.x.Zl.extract 0 R.h.ls)).size = R.h.S2 := by
    rw [eqTab_size, Array.size_extract, hF.zl, hS2]
    congr 1
    have := hF.la
    omega
  have htok : (eqTab (R.x.Zl.extract R.h.ls (R.h.ls + R.h.lt))).size = R.h.T := by
    rw [eqTab_size, Array.size_extract, hF.zl, hT]
    congr 1
    have := hF.la
    omega
  have hu : R.L.m / R.h.T = R.h.S2 * (R.L.m / (R.h.T * R.h.S2)) := by
    have hTpos : 0 < R.h.T := by rw [hT]; exact Nat.pow_pos (by decide)
    conv_lhs => rw [hF.blocks, hLa]
    rw [show R.L.m / (R.h.T * R.h.S2) * (R.h.T * R.h.S2) =
      R.h.T * (R.h.S2 * (R.L.m / (R.h.T * R.h.S2))) by ring, Nat.mul_div_cancel_left _ hTpos]
  rw [hLa, sum_mul]
  refine Finset.sum_congr rfl fun c2 hc2 => Finset.sum_congr rfl fun t ht' => ?_
  have hc2' : c2 < R.h.S2 := mem_range.mp hc2
  have ht'' : t < R.h.T := mem_range.mp ht'
  have hphi := blockRows_get Reading.gl (eqTab (R.x.Zl.extract 0 R.h.ls))
    (eqTab (R.x.Zl.extract R.h.ls (R.h.ls + R.h.lt))) c2 t (by rw [hlow]; exact hc2')
    (by rw [htok]; exact ht'')
  rw [htok] at hphi
  show Reading.gl.val ((blockRows _ _).getD (R.h.T * c2 + t) zeroE) * _ = _
  rw [hphi]
  congr 1
  show _ = cell (cellAt 0 R.L.m R.L.k R.h.T (R.h.S2 * e + c2) t)
  unfold cellAt
  obtain ⟨i1, i2, i3⟩ := hf_index R.h.S2 R.h.T (R.L.m / (R.h.T * R.h.S2)) R.L.k e c2 t
    (by rw [hS2]; exact Nat.pow_pos (by decide)) hc2'
  rw [hLa] at hn
  rw [hu, i1, i2, i3, Nat.zero_add, hn]

end Fo
