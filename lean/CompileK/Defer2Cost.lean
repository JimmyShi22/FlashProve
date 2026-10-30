-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Cost.lean: an upper bound in closed form for `costU2` at full batches, the bound of
`Spec.hopU2` (CompileK/Defer2Door.lean) on the distance of two experiments. The sharper price of the
door (CompileK/Defer2Door.lean: `costU2`), at full batches, is at most hashTerms2 W p t n := t ·
muB2 + hashSqBG2: the hash term `hashTermsBGTot` (Compile/Batch/HopTot.lean) with xTree / 2^(2 λ)
for xTree / 2^λ in the maximum, xTree² / 2^(2 λ) for xTree² / 2^λ and one of the three xReq² / 2^λ
at 2^(2 λ) in the squares.

Definitions (`bitsU2`, `muB2`, `hashSqB2`, `hashSqBG2`, `hashTerms2`) and theorems. Nothing assumed
beyond the hypotheses of the statements, in the random-oracle model, on Lean's three axioms. xTree,
xFb, xReq (Compile/Batch/Counts.lean) bound from above, for a setup and n batches, the honest side's
evaluations of a tree oracle (leaf; likewise node), of the three Fiat-Shamir oracles together, and
of g (likewise of a request tree's oracle).

Main names:
  `sumB2`, `supBG2`, `ghost_le2`, `sumSqBG2`: the analogues of `sumB`
    (Compile/Batch/DisciplineSum.lean) and of `supBG`, `ghost_le`, `sumSqBG`
    (Compile/Batch/TotalG.lean).
  `hopDoor_terms2`: under `hN`, at full batches (B := L.maxBatchSize), the inequality at the door
    (CompileK/Defer2Main.lean: `HopDoor`) holds at hashTerms2.

Why, coarse on purpose: in the maximum the request trees' vertices are left under xReq / 2^λ (they
stand at 2^(2 λ): weakened, to keep four entries). xTree bounds leaves and vertices alike, as in
`hashTermsBGTot`.

Limits: if sMT ≥ 2 λ, the maximum is the chains': xFb / 2^min(sFS, λ), or xReq / 2^λ; unless its
second entry, xTree / 2^(2 λ), which does not read sMT, is above both. At sMT = λ nothing is gained
in the maximum: its first entry xTree / 2^sMT is then the very number that has left the second place
(by a reading). Not evaluated here.
-/
import CompileK.Defer2Main
import Compile.Batch.TotalG
import Compile.Batch.HopTot

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open Disc Disc.Sum
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the lengths:  2 λ at the two vertex oracles, the rules' bits elsewhere -/
abbrev bitsU2 (W : QueryLayout lam L) (p : Params) : OracleName → ℕ :=
  bits2 (rulesT W.K L lam p (maxMoreB W)) Jt (ellT lam)

/-- muB with xTree / 2^(2 λ) for xTree / 2^λ (the request trees' vertices: the head, Why) -/
def muB2 (W : QueryLayout lam L) (p : Params) (n : ℕ) : ℝ≥0∞ :=
  max ((xTree W p n : ℝ≥0∞) / 2 ^ p.sMT)
    (max ((xTree W p n : ℝ≥0∞) / 2 ^ (2 * lam))
      (max ((xFb (L := L) p n : ℝ≥0∞) / 2 ^ (min p.sFS lam)) ((xReq L n : ℝ≥0∞) / 2 ^ lam)))

def hashSqB2 (W : QueryLayout lam L) (p : Params) (n : ℕ) : ℝ≥0∞ :=
  (xTree W p n : ℝ≥0∞) * (0 + xTree W p n : ℕ) / 2 ^ p.sMT +
    (xTree W p n : ℝ≥0∞) * (0 + xTree W p n : ℕ) / 2 ^ (2 * lam) +
    (xFb (L := L) p n : ℝ≥0∞) * (0 + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam) +
    (2 * ((xReq L n : ℝ≥0∞) * (0 + xReq L n : ℕ) / 2 ^ lam) +
      (xReq L n : ℝ≥0∞) * (0 + xReq L n : ℕ) / 2 ^ (2 * lam))

/-- hashSqBG with the vertices at 2 λ -/
def hashSqBG2 (W : QueryLayout lam L) (p : Params) (n : ℕ) : ℝ≥0∞ :=
  (xTree W p n : ℝ≥0∞) * (0 + xTree W p n : ℕ) / 2 ^ p.sMT +
    (xTree W p n : ℝ≥0∞) * (0 + xTree W p n : ℕ) / 2 ^ (2 * lam) +
    ((xFb (L := L) p n : ℝ≥0∞) * (0 + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam) +
      (xGr W p n : ℝ≥0∞) * (xFbG W p n : ℕ) / 2 ^ (min p.sFS lam)) +
    (2 * ((xReq L n : ℝ≥0∞) * (0 + xReq L n : ℕ) / 2 ^ lam) +
      (xReq L n : ℝ≥0∞) * (0 + xReq L n : ℕ) / 2 ^ (2 * lam))

/-- `hashTermsBGTot` (the bound on the passage, for one budget) with the vertices at 2 λ. What it
bounds, and under what: `hopDoor_terms2`. -/
def hashTerms2 (W : QueryLayout lam L) (p : Params) (t n : ℕ) : ℝ≥0∞ :=
  (t : ℝ≥0∞) * muB2 W p n + hashSqBG2 W p n

theorem term_zero2 {M a : ℕ} (k : ℕ) (hM : M = 0) : (M : ℝ≥0∞) * (a : ℕ) / 2 ^ k = 0 := by
  rw [hM, Nat.cast_zero, zero_mul, ENNReal.zero_div]

theorem sumB2 (W : QueryLayout lam L) (p : Params) (n : ℕ) (t : OracleName → ℕ) (T : ℕ) (ht : ∀ o, t o ≤ T) :
    ∑ o ∈ osB,
        (mAllB W p n o : ℝ≥0∞) * (t o + eAllB W p n o + mAllB W p n o : ℕ) / 2 ^ bitsU2 W p o ≤
      (xTree W p n : ℝ≥0∞) * (T + xTree W p n : ℕ) / 2 ^ p.sMT +
        (xTree W p n : ℝ≥0∞) * (T + xTree W p n : ℕ) / 2 ^ (2 * lam) +
        (xFb (L := L) p n : ℝ≥0∞) * (T + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam) +
        (2 * ((xReq L n : ℝ≥0∞) * (T + xReq L n : ℕ) / 2 ^ lam) +
          (xReq L n : ℝ≥0∞) * (T + xReq L n : ℕ) / 2 ^ (2 * lam)) := by
  have hsum : ∑ o ∈ osB,
        (mAllB W p n o : ℝ≥0∞) * (t o + eAllB W p n o + mAllB W p n o : ℕ) / 2 ^ bitsU2 W p o =
      (mAllB W p n OracleName.leaf : ℝ≥0∞) *
          (t OracleName.leaf + eAllB W p n OracleName.leaf + mAllB W p n OracleName.leaf : ℕ) / 2 ^ p.sMT +
        ((mAllB W p n OracleName.node : ℝ≥0∞) *
            (t OracleName.node + eAllB W p n OracleName.node + mAllB W p n OracleName.node : ℕ) / 2 ^ (2 * lam) +
          ((mAllB W p n OracleName.rleaf : ℝ≥0∞) *
              (t OracleName.rleaf + eAllB W p n OracleName.rleaf + mAllB W p n OracleName.rleaf : ℕ) / 2 ^ lam +
            ((mAllB W p n OracleName.rnode : ℝ≥0∞) *
                (t OracleName.rnode + eAllB W p n OracleName.rnode + mAllB W p n OracleName.rnode : ℕ) / 2 ^ (2 * lam) +
              ((mAllB W p n (OracleName.fb Tag.test) : ℝ≥0∞) *
                  (t (OracleName.fb Tag.test) + eAllB W p n (OracleName.fb Tag.test) +
                    mAllB W p n (OracleName.fb Tag.test) : ℕ) /
                  2 ^ (min p.sFS lam) +
                ((mAllB W p n (OracleName.fb Tag.link) : ℝ≥0∞) *
                    (t (OracleName.fb Tag.link) + eAllB W p n (OracleName.fb Tag.link) +
                      mAllB W p n (OracleName.fb Tag.link) : ℕ) /
                    2 ^ (min p.sFS lam) +
                  ((mAllB W p n (OracleName.fb Tag.onl) : ℝ≥0∞) *
                      (t (OracleName.fb Tag.onl) + eAllB W p n (OracleName.fb Tag.onl) +
                        mAllB W p n (OracleName.fb Tag.onl) : ℕ) /
                      2 ^ (min p.sFS lam) +
                    ((mAllB W p n (OracleName.g Tag.test) : ℝ≥0∞) *
                        (t (OracleName.g Tag.test) + eAllB W p n (OracleName.g Tag.test) +
                          mAllB W p n (OracleName.g Tag.test) : ℕ) / 2 ^ lam +
                      ((mAllB W p n (OracleName.g Tag.link) : ℝ≥0∞) *
                          (t (OracleName.g Tag.link) + eAllB W p n (OracleName.g Tag.link) +
                            mAllB W p n (OracleName.g Tag.link) : ℕ) / 2 ^ lam +
                        (mAllB W p n (OracleName.g Tag.onl) : ℝ≥0∞) *
                          (t (OracleName.g Tag.onl) + eAllB W p n (OracleName.g Tag.onl) +
                            mAllB W p n (OracleName.g Tag.onl) : ℕ) /
                          2 ^ lam)))))))) := by
    unfold osB
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    rfl
  rw [hsum, term_zero2 lam (g_test_eq W p n), term_zero2 lam (g_link_eq W p n)]
  have hleaf := SumU.term_le (M := mAllB W p n OracleName.leaf)
    (a := t OracleName.leaf + eAllB W p n OracleName.leaf + mAllB W p n OracleName.leaf) (B := xTree W p n)
    (b := T + xTree W p n) p.sMT (by have := leaf_eq W p n; omega)
    (by have := leaf_eq W p n; have := ht OracleName.leaf; omega)
  have hnode := SumU.term_le (M := mAllB W p n OracleName.node)
    (a := t OracleName.node + eAllB W p n OracleName.node + mAllB W p n OracleName.node) (B := xTree W p n)
    (b := T + xTree W p n) (2 * lam) (by have := node_eq W p n; omega)
    (by have := node_eq W p n; have := ht OracleName.node; omega)
  have hrl := SumU.term_le (M := mAllB W p n OracleName.rleaf)
    (a := t OracleName.rleaf + eAllB W p n OracleName.rleaf + mAllB W p n OracleName.rleaf) (B := xReq L n)
    (b := T + xReq L n) lam (rleaf_le W p n).1
    (by have := rleaf_le W p n; have := ht OracleName.rleaf; omega)
  have hrn := SumU.term_le (M := mAllB W p n OracleName.rnode)
    (a := t OracleName.rnode + eAllB W p n OracleName.rnode + mAllB W p n OracleName.rnode) (B := xReq L n)
    (b := T + xReq L n) (2 * lam) (rnode_le W p n).1
    (by have := rnode_le W p n; have := ht OracleName.rnode; omega)
  have hg := SumU.term_le (M := mAllB W p n (OracleName.g Tag.onl))
    (a := t (OracleName.g Tag.onl) + eAllB W p n (OracleName.g Tag.onl) + mAllB W p n (OracleName.g Tag.onl))
    (B := xReq L n) (b := T + xReq L n) lam (g_onl_le W p n).1
    (by have := g_onl_le W p n; have := ht (OracleName.g Tag.onl); omega)
  have hfs := fb_sum W p n
  have step : ∀ tg : Tag, (mAllB W p n (OracleName.fb tg) : ℝ≥0∞) *
        (t (OracleName.fb tg) + eAllB W p n (OracleName.fb tg) + mAllB W p n (OracleName.fb tg) : ℕ) / 2 ^ (min p.sFS lam) ≤
      (mAllB W p n (OracleName.fb tg) : ℝ≥0∞) * (T + xFb (L := L) p n : ℕ) /
        2 ^ (min p.sFS lam) := fun tg =>
    SumU.term_le _ le_rfl (by
      have h1 := ht (OracleName.fb tg)
      have h2 := fb_e W p n tg
      have h3 : mAllB W p n (OracleName.fb tg) ≤ xFb (L := L) p n := by cases tg <;> omega
      omega)
  have hfb : (mAllB W p n (OracleName.fb Tag.test) : ℝ≥0∞) *
          (T + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam) +
        ((mAllB W p n (OracleName.fb Tag.link) : ℝ≥0∞) * (T + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam) +
          (mAllB W p n (OracleName.fb Tag.onl) : ℝ≥0∞) * (T + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam)) =
      (xFb (L := L) p n : ℝ≥0∞) * (T + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam) := by
    have hf' : (mAllB W p n (OracleName.fb Tag.test) : ℝ≥0∞) +
          ((mAllB W p n (OracleName.fb Tag.link) : ℝ≥0∞) + (mAllB W p n (OracleName.fb Tag.onl) : ℝ≥0∞)) =
        (xFb (L := L) p n : ℝ≥0∞) := by
      rw [← hfs]
      push_cast
      ring
    rw [← hf']
    simp only [div_eq_mul_inv]
    ring
  refine le_trans
    (add_le_add hleaf
      (add_le_add hnode
        (add_le_add hrl
          (add_le_add hrn
            (add_le_add (step Tag.test)
              (add_le_add (step Tag.link)
                (add_le_add (step Tag.onl) (add_le_add le_rfl (add_le_add le_rfl hg)))))))))
    (le_of_eq ?_)
  rw [← hfb]
  ring


theorem supBG2 (W : QueryLayout lam L) (p : Params) (n : ℕ) :
    (osBG (maxMoreB W)).sup (fun o => (mAllB W p n o : ℝ≥0∞) / 2 ^ bitsU2 W p o) ≤ muB2 W p n := by
  have l1 : ∀ x : ℝ≥0∞, x ≤ (xTree W p n : ℝ≥0∞) / 2 ^ p.sMT → x ≤ muB2 W p n := fun x h =>
    h.trans (le_max_left _ _)
  have l2 : ∀ x : ℝ≥0∞, x ≤ (xTree W p n : ℝ≥0∞) / 2 ^ (2 * lam) → x ≤ muB2 W p n := fun x h =>
    h.trans ((le_max_left _ _).trans (le_max_right _ _))
  have l3 : ∀ x : ℝ≥0∞, x ≤ (xFb (L := L) p n : ℝ≥0∞) / 2 ^ (min p.sFS lam) → x ≤ muB2 W p n :=
    fun x h => h.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have l4 : ∀ x : ℝ≥0∞, x ≤ (xReq L n : ℝ≥0∞) / 2 ^ lam → x ≤ muB2 W p n := fun x h =>
    h.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hw : ∀ tg k,
      (mAllB W p n (OracleName.fbw tg k) : ℝ≥0∞) / 2 ^ bitsU2 W p (OracleName.fbw tg k) ≤ muB2 W p n :=
    fun tg k => l3 _ (fracG_le (min p.sFS lam) (fbw_le_xFb W p n tg k))
  refine Finset.sup_le fun o ho => ?_
  rcases Finset.mem_union.1 ho with ho | ho
  · simp only [osB, Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact l1 _ (fracG_le p.sMT (by have := leaf_eq W p n; omega))
    · exact l2 _ (fracG_le (2 * lam) (by have := node_eq W p n; omega))
    · exact l4 _ (fracG_le lam (rleaf_le W p n).1)
    · exact l4 _
        ((fracG_le (2 * lam) (rnode_le W p n).1).trans
          (ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by omega)) _))
    · exact l3 _ (fracG_le (min p.sFS lam) (fb_le_xFb W p n _))
    · exact l3 _ (fracG_le (min p.sFS lam) (fb_le_xFb W p n _))
    · exact l3 _ (fracG_le (min p.sFS lam) (fb_le_xFb W p n _))
    · exact l4 _ (fracG_le lam (by rw [g_test_eq W p n]; exact Nat.zero_le _))
    · exact l4 _ (fracG_le lam (by rw [g_link_eq W p n]; exact Nat.zero_le _))
    · exact l4 _ (fracG_le lam (g_onl_le W p n).1)
  · rcases Finset.mem_union.1 ho with ho | ho
    · rcases Finset.mem_union.1 ho with ho | ho
        <;> obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 ho <;> exact hw _ k
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 ho
      exact hw _ k


/-- The sum of squares over the ghost names of one tag is at most xGr times their sum, both over
2^min(sFS, λ). -/
theorem ghost_le2 (W : QueryLayout lam L) (p : Params) (n m : ℕ) (tg : Tag) :
    ∑ o ∈ (Finset.range m).image (OracleName.fbw tg),
        (mAllB W p n o : ℝ≥0∞) * (eAllB W p n o + mAllB W p n o : ℕ) / 2 ^ bitsU2 W p o ≤
      (xGr W p n : ℝ≥0∞) * ((∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw tg k) : ℕ) : ℝ≥0∞) /
        2 ^ (min p.sFS lam) := by
  rw [Finset.sum_image fun a _ b _ h => (OracleName.fbw.inj h).2, Nat.cast_sum, Finset.mul_sum,
    div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  show (mAllB W p n (OracleName.fbw tg k) : ℝ≥0∞) *
      (eAllB W p n (OracleName.fbw tg k) + mAllB W p n (OracleName.fbw tg k) : ℕ) / 2 ^ (min p.sFS lam) ≤ _
  rw [fbw_e, Nat.zero_add, div_eq_mul_inv]
  have : (mAllB W p n (OracleName.fbw tg k) : ℝ≥0∞) ≤ (xGr W p n : ℝ≥0∞) :=
    Nat.cast_le.2 (fbw_le_xGr W p n tg k)
  gcongr

theorem sumSqBG2 (W : QueryLayout lam L) (p : Params) (n : ℕ) :
    ∑ o ∈ osBG (maxMoreB W),
        (mAllB W p n o : ℝ≥0∞) * (eAllB W p n o + mAllB W p n o : ℕ) / 2 ^ bitsU2 W p o ≤
      hashSqBG2 W p n := by
  set m := maxMoreB W
  set f : OracleName → ℝ≥0∞ := fun o =>
    (mAllB W p n o : ℝ≥0∞) * (eAllB W p n o + mAllB W p n o : ℕ) / 2 ^ bitsU2 W p o
  have h0 : ∑ o ∈ osB, f o ≤ hashSqB2 W p n := by
    have h := sumB2 W p n (fun _ => 0) 0 fun _ => le_rfl
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun o _ => ?_)) h
    show _ = (mAllB W p n o : ℝ≥0∞) * (0 + eAllB W p n o + mAllB W p n o : ℕ) / _
    rw [Nat.zero_add]
  have hf := fam_le W p n m
  have hg : ∑ o ∈ (Finset.range m).image (OracleName.fbw Tag.test) ∪ (Finset.range m).image
            (OracleName.fbw Tag.link) ∪ (Finset.range m).image (OracleName.fbw Tag.onl),
          f o ≤
      (xGr W p n : ℝ≥0∞) * (xFbG W p n : ℕ) / 2 ^ (min p.sFS lam) := by
    refine le_trans (le_trans (sum_union_le' _ _ f) (add_le_add (sum_union_le' _ _ f) le_rfl)) ?_
    refine le_trans
      (add_le_add (add_le_add (ghost_le2 W p n m Tag.test) (ghost_le2 W p n m Tag.link))
        (ghost_le2 W p n m Tag.onl)) ?_
    have hs : ((∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.test k) : ℕ) : ℝ≥0∞) +
          ((∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.link k) : ℕ) : ℝ≥0∞) +
          ((∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.onl k) : ℕ) : ℝ≥0∞) ≤
        (xFbG W p n : ℕ) := by
      exact_mod_cast (by
        omega : ∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.test k) +
            ∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.link k) +
            ∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.onl k) ≤ xFbG W p n)
    simp only [div_eq_mul_inv]
    rw [← add_mul, ← add_mul, ← mul_add, ← mul_add]
    gcongr
  refine le_trans (sum_union_le' _ _ f) (le_trans (add_le_add h0 hg) (le_of_eq ?_))
  unfold hashSqB2 hashSqBG2
  ring


/-- The sharper price (`costU2`) at full batches is at most hashTerms2. -/
theorem costU2_le (W : QueryLayout lam L) (p : Params) (t n : ℕ) :
    costU2 W p L.maxBatchSize t n ≤ hashTerms2 W p t n := by
  unfold costU2 hashTerms2
  rw [mAllU_N]
  refine add_le_add ?_ (sumSqBG2 W p n)
  gcongr
  exact supBG2 W p n

theorem div_two_lam_le (a : ℝ≥0∞) (lam : ℕ) : a / 2 ^ (2 * lam) ≤ a / 2 ^ lam :=
  ENNReal.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by omega)) _

theorem muB2_le (W : QueryLayout lam L) (p : Params) (n : ℕ) : muB2 W p n ≤ muB W p n :=
  max_le_max le_rfl (max_le_max (div_two_lam_le _ lam) le_rfl)

theorem hashSqBG2_le (W : QueryLayout lam L) (p : Params) (n : ℕ) : hashSqBG2 W p n ≤ hashSqBG W p n := by
  unfold hashSqBG2 hashSqBG
  refine add_le_add (add_le_add (add_le_add le_rfl (div_two_lam_le _ lam)) le_rfl) ?_
  calc
    2 * ((xReq L n : ℝ≥0∞) * (0 + xReq L n : ℕ) / 2 ^ lam) +
          (xReq L n : ℝ≥0∞) * (0 + xReq L n : ℕ) / 2 ^ (2 * lam) ≤
        2 * ((xReq L n : ℝ≥0∞) * (0 + xReq L n : ℕ) / 2 ^ lam) +
          (xReq L n : ℝ≥0∞) * (0 + xReq L n : ℕ) / 2 ^ lam :=
      add_le_add le_rfl (div_two_lam_le _ lam)
    _ = 3 * ((xReq L n : ℝ≥0∞) * (0 + xReq L n : ℕ) / 2 ^ lam) := by ring

/-- Guard: `hashTerms2` is never above `hashTermsBGTot`. -/
theorem hashTerms2_le (W : QueryLayout lam L) (p : Params) (t n : ℕ) :
    hashTerms2 W p t n ≤ hashTermsBGTot W p t n :=
  add_le_add (mul_le_mul' le_rfl (muB2_le W p n)) (hashSqBG2_le W p n)

theorem HopDoor.mono {W : QueryLayout lam L} {WP : WireBP L} {p : Params} {B : ℕ} {h h' : ℕ → ℕ → ℝ≥0∞}
    (hh : HopDoor W WP p B h) (hle : ∀ t n, h t n ≤ h' t n) : HopDoor W WP p B h' :=
  fun V pw i ok hok α A t n hT hA => (hh V pw i ok hok α A t n hT hA).trans (hle t n)

/-- The inequality at the door (`HopDoor`), at hashTerms2. -/
theorem hopDoor_terms2 (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (hN : L.maxBatchSize = 2 ^ W.depthReq) :
    HopDoor W WP p L.maxBatchSize (hashTerms2 W p) :=
  (hopDoor2 W WP p L.maxBatchSize hN).mono (costU2_le W p)

end Compile.Batch
