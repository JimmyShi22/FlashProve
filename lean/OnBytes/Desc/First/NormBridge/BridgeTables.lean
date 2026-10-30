-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/NormBridge/BridgeTables.lean: THE PER-POSITION BRIDGE OF A NORM: THE TWO SUMCHECKS'
TABLES,
made of the committed data (BridgeCore.lean: Data), and what their sums are. Algebra over a
field; no
text of a verifier. Definitions, statements and proofs.

  Data.batch: the limbs' batch under the powers of gam.
  Data.sqTab: THE SQUARES' TABLE over lNI + lPd + lt bits: at the index (i 2^lPd + j) 2^lt + t the
  batch
    of norm i, feature j, position t; 0 where i is no norm or j no feature (the padding).
  ext_sqTab: the extension of its square, at a point whose middle lPd coordinates are all h with
    1 - h = h, is h^lPd times the right side of BridgeCore.lean's premise Squares.
  Data.field: THE PRODUCTS' TABLES over lt bits: table 4 i + q is field q of norm i's row
    (q = 0..3: a, b, Rlo, Rhi: the library's sa, sb, Rlo, Rhi on the position's digits).
  prTerms: the 7 NI terms of the products' summand: om^m, and the numbers of its two tables.
  sumTerms_pr, field_prod, ext_field: the summand on the tables is the batch of the rows' products;
  a
    table's extension is the field of the digits' extensions.
  nat_apply, eqN_congr_pt, ext_congr_pt: an extension reads its point at its own coordinates alone.
LIBRARY LEMMAS TAKEN: LedgerForms.lean ext_sa, ext_sb, ext_Rlo, ext_Rhi, prodsOf; Blocks/Ext.lean
ext_congr, ext_zero_of_forall, ext_sum.
ALSO TAKEN: Term, sumTerms (PscProducts.lean).

-/
import OnBytes.Desc.First.NormBridge.BridgeCore
import OnBytes.Desc.First.NormBridge.ExtSplit
import OnBytes.Desc.First.P1.PscProducts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Bridge
open Finset
open Blocks (ext eqN nat)
open Inst.Model.Ledger (sa sb Rlo Rhi prods)
open OnBytes.Desc.First.P1 (Term sumTerms)

variable {K : Type} [Field K]

/-! ## Points -/

theorem nat_apply (n : ℕ) (u : ℕ → K) {t : ℕ} (ht : t < n) :
    nat (fun v : Fin n => u v) t = u t := by
  unfold Blocks.nat
  rw [dif_pos ht]

theorem eqN_congr_pt (m off : ℕ) {a b : ℕ → K} (h : ∀ t < m, a (off + t) = b (off + t)) (z : ℕ) :
    eqN m off a z = eqN m off b z := by
  unfold Blocks.eqN
  exact prod_congr rfl fun t ht => by rw [h t (mem_range.mp ht)]

theorem ext_congr_pt (g : ℕ) (v : ℕ → K) {a b : ℕ → K} (h : ∀ t < g, a t = b t) :
    ext g v a = ext g v b := by
  unfold Blocks.ext
  exact sum_congr rfl fun X _ => by
    rw [eqN_congr_pt g 0 (a := a) (b := b) (fun t ht => by rw [Nat.zero_add]; exact h t ht) X]

/-! ## The squares' table -/

namespace Data
variable (c : Data K)

/-- The limbs' batch. -/
def batch (gam : K) (i j t : ℕ) : K := ∑ l ∈ range 5, gam ^ l * c.limb i l j t

/-- The squares' table. -/
def sqTab (lPd : ℕ) (gam : K) (X : ℕ) : K :=
  if X / 2 ^ c.lt / 2 ^ lPd < c.NI ∧ X / 2 ^ c.lt % 2 ^ lPd < c.d then
    c.batch gam (X / 2 ^ c.lt / 2 ^ lPd) (X / 2 ^ c.lt % 2 ^ lPd) (X % 2 ^ c.lt)
  else 0

theorem sqTab_at (lPd : ℕ) (gam : K) (i j t : ℕ) (hj : j < 2 ^ lPd) (ht : t < 2 ^ c.lt) :
    c.sqTab lPd gam ((i * 2 ^ lPd + j) * 2 ^ c.lt + t) =
      if i < c.NI ∧ j < c.d then c.batch gam i j t else 0 := by
  unfold sqTab
  rw [div_of_lt _ ht, mod_of_lt _ ht, div_of_lt _ hj, mod_of_lt _ hj]

/-- The extension over the positions of the table's square, at the place J of norm and feature. -/
def sqF (lPd : ℕ) (gam : K) (u : ℕ → K) (J : ℕ) : K :=
  ext c.lt (fun t => c.sqTab lPd gam (J * 2 ^ c.lt + t) * c.sqTab lPd gam (J * 2 ^ c.lt + t)) u

/-- The extension over the positions of norm i's sum of squares of batches. -/
def sqZ (gam : K) (u : ℕ → K) (i : ℕ) : K :=
  ext c.lt (fun t => ∑ j ∈ range c.d, (c.batch gam i j t) ^ 2) u

theorem sqF_at (lPd : ℕ) (gam : K) (u : ℕ → K) (i j : ℕ) (hj : j < 2 ^ lPd) :
    c.sqF lPd gam u (i * 2 ^ lPd + j) =
      if i < c.NI ∧ j < c.d then ext c.lt (fun t => (c.batch gam i j t) ^ 2) u else 0 := by
  unfold sqF
  by_cases hc : i < c.NI ∧ j < c.d
  · rw [if_pos hc]
    exact Blocks.ext_congr
      (fun t ht => by rw [c.sqTab_at lPd gam i j t hj ht, if_pos hc, sq]) u
  · rw [if_neg hc]
    exact Blocks.ext_zero_of_forall
      (fun t ht => by rw [c.sqTab_at lPd gam i j t hj ht, if_neg hc, mul_zero]) u

theorem sum_sqF (lPd : ℕ) (hd : c.d ≤ 2 ^ lPd) (gam h : K) (hh : 1 - h = h) (a u : ℕ → K)
    (ha : ∀ t < lPd, a (c.lNI + t) = h) (i : ℕ) :
    ∑ j ∈ range (2 ^ lPd), eqN lPd c.lNI a j * c.sqF lPd gam u (i * 2 ^ lPd + j) =
      if i < c.NI then h ^ lPd * c.sqZ gam u i else 0 := by
  have e1 : ∑ j ∈ range (2 ^ lPd), eqN lPd c.lNI a j * c.sqF lPd gam u (i * 2 ^ lPd + j) =
      ∑ j ∈ range (2 ^ lPd), h ^ lPd *
        (if i < c.NI ∧ j < c.d then ext c.lt (fun t => (c.batch gam i j t) ^ 2) u else 0) :=
    sum_congr rfl fun j hj => by
      rw [eqN_const lPd c.lNI a h hh ha j, c.sqF_at lPd gam u i j (mem_range.mp hj)]
  rw [e1, ← mul_sum]
  by_cases hi : i < c.NI
  · rw [if_pos hi, sum_range_trunc hd _ fun j hj => if_neg (by omega)]
    congr 1
    unfold sqZ
    rw [Blocks.ext_sum]
    exact sum_congr rfl fun j hj => if_pos ⟨hi, mem_range.mp hj⟩
  · rw [if_neg hi, sum_eq_zero fun j _ => if_neg fun hc => hi hc.1, mul_zero]

/-- **What the squares' table sums to.** -/
theorem ext_sqTab (lPd : ℕ) (hd : c.d ≤ 2 ^ lPd) (hN : c.NI ≤ 2 ^ c.lNI) (gam h : K)
    (hh : 1 - h = h) (a : ℕ → K) (ha : ∀ t < lPd, a (c.lNI + t) = h) :
    ext (c.lNI + lPd + c.lt) (fun X => c.sqTab lPd gam X * c.sqTab lPd gam X) a =
      h ^ lPd * ∑ i ∈ range c.NI,
        eqN c.lNI 0 a i * c.sqZ gam (fun t => a (c.lNI + lPd + t)) i := by
  have e0 : ext (c.lNI + lPd + c.lt) (fun X => c.sqTab lPd gam X * c.sqTab lPd gam X) a =
      ∑ J ∈ range (2 ^ (c.lNI + lPd)), eqN (c.lNI + lPd) 0 a J *
        c.sqF lPd gam (fun t => a (c.lNI + lPd + t)) J :=
    ext_split (c.lNI + lPd) c.lt _ a
  have e2 : ∑ i ∈ range (2 ^ c.lNI), eqN c.lNI 0 a i *
        ∑ j ∈ range (2 ^ lPd), eqN lPd c.lNI a j *
          c.sqF lPd gam (fun t => a (c.lNI + lPd + t)) (i * 2 ^ lPd + j) =
      ∑ i ∈ range (2 ^ c.lNI), eqN c.lNI 0 a i *
        (if i < c.NI then h ^ lPd * c.sqZ gam (fun t => a (c.lNI + lPd + t)) i else 0) :=
    sum_congr rfl fun i _ => by rw [c.sum_sqF lPd hd gam h hh a _ ha i]
  rw [e0, sum_eqN_split c.lNI lPd _ a, e2,
    sum_range_trunc hN _ fun i hi => by rw [if_neg (by omega), mul_zero], mul_sum]
  exact sum_congr rfl fun i hi => by
    rw [if_pos (mem_range.mp hi)]
    ring

/-! ## The products' tables -/

/-- Table 4 i + q: field q of norm i's row at position t. -/
def field (e t : ℕ) : K :=
  if e % 4 = 0 then sa (fun m => c.dig (e / 4) m t)
  else if e % 4 = 1 then sb (fun m => c.dig (e / 4) m t)
  else if e % 4 = 2 then Rlo (fun m => c.dig (e / 4) m t)
  else Rhi (fun m => c.dig (e / 4) m t)

theorem field0 (i t : ℕ) : c.field (4 * i + 0) t = sa (fun m => c.dig i m t) := by
  unfold field
  rw [if_pos (by omega), show (4 * i + 0) / 4 = i by omega]

theorem field1 (i t : ℕ) : c.field (4 * i + 1) t = sb (fun m => c.dig i m t) := by
  unfold field
  rw [if_neg (by omega), if_pos (by omega), show (4 * i + 1) / 4 = i by omega]

theorem field2 (i t : ℕ) : c.field (4 * i + 2) t = Rlo (fun m => c.dig i m t) := by
  unfold field
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (4 * i + 2) / 4 = i by omega]

theorem field3 (i t : ℕ) : c.field (4 * i + 3) t = Rhi (fun m => c.dig i m t) := by
  unfold field
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (4 * i + 3) / 4 = i by omega]

theorem ext_field0 (u : ℕ → K) (i : ℕ) : ext c.lt (c.field (4 * i + 0)) u = sa (c.digAt u i) := by
  rw [show c.field (4 * i + 0) = fun t => sa (fun m => c.dig i m t) from funext (c.field0 i)]
  exact Inst.Model.Ledger.ext_sa c.lt (c.dig i) u

theorem ext_field1 (u : ℕ → K) (i : ℕ) : ext c.lt (c.field (4 * i + 1)) u = sb (c.digAt u i) := by
  rw [show c.field (4 * i + 1) = fun t => sb (fun m => c.dig i m t) from funext (c.field1 i)]
  exact Inst.Model.Ledger.ext_sb c.lt (c.dig i) u

theorem ext_field2 (u : ℕ → K) (i : ℕ) : ext c.lt (c.field (4 * i + 2)) u = Rlo (c.digAt u i) := by
  rw [show c.field (4 * i + 2) = fun t => Rlo (fun m => c.dig i m t) from funext (c.field2 i)]
  exact Inst.Model.Ledger.ext_Rlo c.lt (c.dig i) u

theorem ext_field3 (u : ℕ → K) (i : ℕ) : ext c.lt (c.field (4 * i + 3)) u = Rhi (c.digAt u i) := by
  rw [show c.field (4 * i + 3) = fun t => Rhi (fun m => c.dig i m t) from funext (c.field3 i)]
  exact Inst.Model.Ledger.ext_Rhi c.lt (c.dig i) u

end Data

/-- The first and the second factor of row product number n, by their places 0..3 among
a, b, Rlo, Rhi: a a, a b, b b, Rlo a, Rlo b, Rhi a, Rhi b. -/
def pairA (n : ℕ) : ℕ := if n ≤ 1 then 0 else if n = 2 then 1 else if n ≤ 4 then 2 else 3
def pairB (n : ℕ) : ℕ := if n = 0 ∨ n = 3 ∨ n = 5 then 0 else 1

theorem pairA_lt (n : ℕ) : pairA n < 4 := by
  unfold pairA
  split_ifs <;> omega

theorem pairB_lt (n : ℕ) : pairB n < 4 := by
  unfold pairB
  split_ifs <;> omega

/-- The terms of the products' summand. -/
def prTerms (NI : ℕ) (om : K) : List (Term K) :=
  (List.range (7 * NI)).map fun m =>
    (om ^ m, 4 * (m / 7) + pairA (m % 7), 4 * (m / 7) + pairB (m % 7))

theorem sumTerms_pr (NI : ℕ) (om : K) (v : ℕ → K) :
    sumTerms (prTerms NI om) v = ∑ m ∈ range (7 * NI),
      om ^ m * (v (4 * (m / 7) + pairA (m % 7)) * v (4 * (m / 7) + pairB (m % 7))) := by
  unfold OnBytes.Desc.First.P1.sumTerms prTerms
  rw [List.map_map]
  exact list_sum_range (7 * NI) _

/-- The two tables of a term multiply to the row's product. -/
theorem field_prod (c : Data K) (i n t : ℕ) (hn : n < 7) :
    c.field (4 * i + pairA n) t * c.field (4 * i + pairB n) t = c.prodR i n t := by
  have hc : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show c.field (4 * i + 0) t * c.field (4 * i + 0) t = (sa fun m => c.dig i m t) ^ 2
    rw [c.field0, sq]
  · show c.field (4 * i + 0) t * c.field (4 * i + 1) t =
      (sa fun m => c.dig i m t) * sb fun m => c.dig i m t
    rw [c.field0, c.field1]
  · show c.field (4 * i + 1) t * c.field (4 * i + 1) t = (sb fun m => c.dig i m t) ^ 2
    rw [c.field1, sq]
  · show c.field (4 * i + 2) t * c.field (4 * i + 0) t =
      (Rlo fun m => c.dig i m t) * sa fun m => c.dig i m t
    rw [c.field2, c.field0]
  · show c.field (4 * i + 2) t * c.field (4 * i + 1) t =
      (Rlo fun m => c.dig i m t) * sb fun m => c.dig i m t
    rw [c.field2, c.field1]
  · show c.field (4 * i + 3) t * c.field (4 * i + 0) t =
      (Rhi fun m => c.dig i m t) * sa fun m => c.dig i m t
    rw [c.field3, c.field0]
  · show c.field (4 * i + 3) t * c.field (4 * i + 1) t =
      (Rhi fun m => c.dig i m t) * sb fun m => c.dig i m t
    rw [c.field3, c.field1]

/-- The summand on the tables is the batch of the rows' products. -/
theorem sumTerms_field (c : Data K) (om : K) (t : ℕ) :
    sumTerms (prTerms c.NI om) (fun e => c.field e t) =
      ∑ m ∈ range (7 * c.NI), om ^ m * c.prodR (m / 7) (m % 7) t := by
  rw [sumTerms_pr]
  exact sum_congr rfl fun m _ => by rw [field_prod c (m / 7) (m % 7) t (Nat.mod_lt _ (by omega))]

end D6.Bridge

#print axioms D6.Bridge.Data.ext_sqTab
#print axioms D6.Bridge.sumTerms_field
