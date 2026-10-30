-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysEq.lean: the verifier's table of equality weights is the library's kernel eq;
and, for a segment whose columns are aligned on blocks, the weights that the lookup's join gives to
the segment's entries and to its blocks are one set.

The verifier computes the values eq(z, c) for all c at once (eqTab in OnBytes/Model/Frame.lean). The
library writes eq(a, c) as a product over the coordinates (Blocks.eqN in Blocks/Basic.lean). In both
the first coordinate belongs to the top bit of c.

Main definition: Aligned. Main theorems: eqTab_size, eqTab_value, blocked_of_aligned, blocked_join.

That the verifier's rule for placing segments gives aligned columns is shown in
Johnson/Road/FormsKeysPlace.lean, not here.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. The program does not import this file.

-/
import Johnson.Road.FormsKeysKit

set_option autoImplicit false

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading eqTab eqTabStep Seg)
open OnBytes.Model.Layer (Env)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## One more coordinate, on lists -/

/-- One more coordinate: every entry a becomes the two entries a (1 - zv) and a zv. -/
def stepL (tab : List E) (zv : E) : List E :=
  tab.flatMap fun a => [subE a (mulE a zv), mulE a zv]

/-- The verifier's step, as a list. -/
theorem eqTabStep_toList (t : Array E) (zv : E) : (eqTabStep t zv).toList = stepL t.toList zv := by
  have key : ∀ (l : List E) (acc : Array E),
      (l.foldl (fun n a => (n.push (subE a (mulE a zv))).push (mulE a zv)) acc).toList =
        acc.toList ++ stepL l zv := by
    intro l
    induction l with
    | nil => intro acc; simp [stepL]
    | cons a l ih => intro acc; rw [List.foldl_cons, ih]; simp [stepL]
  unfold eqTabStep
  rw [← Array.foldl_toList]
  exact (key t.toList _).trans (by simp)

/-- The verifier's table, as a list. -/
theorem eqTab_toList (z : Array E) : (eqTab z).toList = z.toList.foldl stepL [oneE] := by
  have key : ∀ (l : List E) (acc : Array E),
      (l.foldl eqTabStep acc).toList = l.foldl stepL acc.toList := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons a l ih => intro acc; rw [List.foldl_cons, List.foldl_cons, ih, eqTabStep_toList]
  unfold eqTab
  rw [← Array.foldl_toList]
  exact key z.toList _

/-- A step doubles the length. -/
theorem stepL_length (zv : E) : ∀ tab : List E, (stepL tab zv).length = 2 * tab.length
  | [] => rfl
  | a :: l => by
    have e : stepL (a :: l) zv = subE a (mulE a zv) :: mulE a zv :: stepL l zv := by simp [stepL]
    rw [e, List.length_cons, List.length_cons, stepL_length zv l, List.length_cons]
    ring

/-- The two entries that come from entry c. -/
theorem stepL_getD (zv : E) : ∀ (tab : List E) (c : ℕ), c < tab.length →
    (stepL tab zv).getD (2 * c) zeroE = subE (tab.getD c zeroE) (mulE (tab.getD c zeroE) zv) ∧
    (stepL tab zv).getD (2 * c + 1) zeroE = mulE (tab.getD c zeroE) zv
  | [], c, h => by simp at h
  | a :: l, 0, _ => by
    have e : stepL (a :: l) zv = subE a (mulE a zv) :: mulE a zv :: stepL l zv := by simp [stepL]
    rw [e]
    exact ⟨rfl, rfl⟩
  | a :: l, c + 1, h => by
    have e : stepL (a :: l) zv = subE a (mulE a zv) :: mulE a zv :: stepL l zv := by simp [stepL]
    have hc : c < l.length := by simpa using h
    have ih := stepL_getD zv l c hc
    have i0 : 2 * (c + 1) = 2 * c + 1 + 1 := by ring
    rw [e, i0]
    simpa using ih

/-! ## The kernel, one coordinate more -/

/-- The library's kernel with one more coordinate, at an even and at an odd index. -/
theorem eqN_succ (m : ℕ) (a : ℕ → K) (c : ℕ) :
    Blocks.eqN (m + 1) 0 a (2 * c) = Blocks.eqN m 0 a c * (1 - a m) ∧
    Blocks.eqN (m + 1) 0 a (2 * c + 1) = Blocks.eqN m 0 a c * a m := by
  have h0 := Blocks.eqN_append m 1 0 a c (z' := 0) (by norm_num)
  have h1 := Blocks.eqN_append m 1 0 a c (z' := 1) (by norm_num)
  have e0 : Blocks.eqN 1 (0 + m) a 0 = 1 - a m := by simp [Blocks.eqN]
  have e1 : Blocks.eqN 1 (0 + m) a 1 = a m := by simp [Blocks.eqN]
  rw [e0] at h0
  rw [e1] at h1
  simpa using And.intro h0 h1

/-! ## The table -/

/-- The fold over the coordinates zs, from a table that is the kernel on the first m coordinates. -/
theorem foldStepL (a : ℕ → K) : ∀ (zs tab : List E) (m : ℕ), tab.length = 2 ^ m →
    (∀ c, c < 2 ^ m → ρ.val (tab.getD c zeroE) = Blocks.eqN m 0 a c) →
    (∀ j, j < zs.length → a (m + j) = ρ.val (zs.getD j zeroE)) →
    (zs.foldl stepL tab).length = 2 ^ (m + zs.length) ∧
      ∀ c, c < 2 ^ (m + zs.length) →
        ρ.val ((zs.foldl stepL tab).getD c zeroE) = Blocks.eqN (m + zs.length) 0 a c
  | [], tab, m, hl, ht, _ => ⟨by simpa using hl, by simpa using ht⟩
  | zv :: zs, tab, m, hl, ht, ha => by
    have hz : a m = ρ.val zv := by simpa using ha 0 (by simp)
    have hl' : (stepL tab zv).length = 2 ^ (m + 1) := by rw [stepL_length, hl]; ring
    have ht' : ∀ c, c < 2 ^ (m + 1) →
        ρ.val ((stepL tab zv).getD c zeroE) = Blocks.eqN (m + 1) 0 a c := by
      intro c hc
      have hc2 : c / 2 < 2 ^ m := by
        rw [pow_succ] at hc
        omega
      obtain ⟨g0, g1⟩ := stepL_getD zv tab (c / 2) (by rw [hl]; exact hc2)
      obtain ⟨k0, k1⟩ := eqN_succ m a (c / 2)
      rcases Nat.mod_two_eq_zero_or_one c with hm | hm
      · have e : c = 2 * (c / 2) := by omega
        rw [e, g0, k0, ρ.sub, ρ.mul, ht _ hc2, hz]
        ring
      · have e : c = 2 * (c / 2) + 1 := by omega
        rw [e, g1, k1, ρ.mul, ht _ hc2, hz]
    have ha' : ∀ j, j < zs.length → a (m + 1 + j) = ρ.val (zs.getD j zeroE) := by
      intro j hj
      have := ha (j + 1) (by simpa using hj)
      have e : m + 1 + j = m + (j + 1) := by ring
      rw [e, this]
      rfl
    have r := foldStepL a zs (stepL tab zv) (m + 1) hl' ht' ha'
    have e : m + (zv :: zs).length = m + 1 + zs.length := by rw [List.length_cons]; ring
    rw [List.foldl_cons, e]
    exact r

/-- A point of the verifier, read in K as the library writes a point: a function on the natural
numbers, 0 past the end. -/
def pt (z : Array E) : ℕ → K := fun j => ρ.val (z.getD j zeroE)

/-- Each coordinate doubles the length. -/
theorem foldStepL_length : ∀ (zs tab : List E),
    (zs.foldl stepL tab).length = 2 ^ zs.length * tab.length
  | [], tab => by simp
  | zv :: zs, tab => by
    rw [List.foldl_cons, foldStepL_length zs, stepL_length, List.length_cons]
    ring

omit [Field K] in
/-- The table has one entry for each index. -/
theorem eqTab_size (z : Array E) : (eqTab z).size = 2 ^ z.size := by
  have r := foldStepL_length z.toList [oneE]
  rw [← eqTab_toList] at r
  simpa using r

/-- Entry c of the verifier's table of equality weights reads as the library's eq at c. -/
theorem eqTab_value (z : Array E) (c : ℕ) (hc : c < 2 ^ z.size) :
    ρ.val ((eqTab z).getD c zeroE) = Blocks.eqN z.size 0 (pt ρ z) c := by
  have r := (foldStepL ρ (pt ρ z) z.toList [oneE] 0 rfl
    (by intro c hc; have h0 : c = 0 := by simpa using hc
        subst h0; simp [Blocks.eqN, ρ.one])
    (by intro j _; simp [pt])).2 c (by simpa using hc)
  rw [← eqTab_toList] at r
  simpa using r

/-! ## The weights of a segment's entries and of its blocks -/

/-- An entry of the image of an array. -/
theorem getD_map_lt {α β : Type} (a : Array α) (f : α → β) {i : ℕ} (h : i < a.size) (d : β)
    (d' : α) : (a.map f).getD i d = f (a.getD i d') := by
  simp [Array.getD, h]

/-- Past an array's end the default is read. -/
theorem getD_ge {α : Type} (a : Array α) {i : ℕ} (h : a.size ≤ i) (d : α) : a.getD i d = d := by
  simp [Array.getD, Nat.not_lt.mpr h]

/-- The kernel reads only its own coordinates. -/
theorem eqN_congr' (m off : ℕ) {a a' : ℕ → K} (h : ∀ j, j < m → a (off + j) = a' (off + j))
    (z : ℕ) : Blocks.eqN m off a z = Blocks.eqN m off a' z := by
  unfold Blocks.eqN
  exact prod_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

/-- The kernel from an offset on is the kernel of the shifted point. -/
theorem eqN_shift' (m off : ℕ) (a : ℕ → K) (z : ℕ) :
    Blocks.eqN m 0 (fun j => a (off + j)) z = Blocks.eqN m off a z := by
  unfold Blocks.eqN
  exact prod_congr rfl fun j _ => by rw [Nat.zero_add]

/-- The columns of a segment are aligned on blocks of 2^ls entries in a call with 2^lJ columns: the
segment is a whole number of blocks, a block's entries lie in neighbouring columns, and a block's
first column is a multiple of 2^ls. -/
structure Aligned (s : Seg) (ls lJ : ℕ) : Prop where
  /-- one column for each entry -/
  size : s.pos.size = s.n
  /-- a whole number of blocks -/
  whole : ∃ q, s.n = q * 2 ^ ls
  /-- neighbouring columns -/
  run : ∀ xh r, xh < s.n / 2 ^ ls → r < 2 ^ ls →
    s.pos.getD (2 ^ ls * xh + r) 0 = s.pos.getD (2 ^ ls * xh) 0 + r
  /-- the first column of a block -/
  start : ∀ xh, xh < s.n / 2 ^ ls → 2 ^ ls ∣ s.pos.getD (2 ^ ls * xh) 0
  /-- every column is one of the call's -/
  inside : ∀ x, x < s.n → s.pos.getD x 0 < 2 ^ lJ

/-- For an aligned segment the weights of the entries (equality weights of the column's point z at
the entries' columns) and the weights of the blocks (those of the point without its last ls
coordinates at the blocks' numbers) are one set of weights. zh: the point without these
coordinates. -/
theorem blocked_of_aligned {ls lJ : ℕ} (z zh : Array E) (hz : z.size = lJ) (hls : ls ≤ lJ)
    (hzh : zh.size = lJ - ls) (hpre : ∀ j, j < lJ - ls → zh.getD j zeroE = z.getD j zeroE)
    (s : Seg) (A : Aligned s ls lJ) :
    Blocked ρ (Env.ewFrom (eqTab z) s) (Env.ewhFrom (2 ^ ls) (eqTab zh) s) ls
      (fun j => pt ρ z (lJ - ls + j)) := by
  intro xh r hr
  obtain ⟨q, hq⟩ := A.whole
  have hpos : 0 < 2 ^ ls := by positivity
  have hdiv : s.n / 2 ^ ls = q := by rw [hq, Nat.mul_div_cancel _ hpos]
  unfold Env.ewFrom Env.ewhFrom
  by_cases hx : xh < s.n / 2 ^ ls
  · have hxq : xh < q := hdiv ▸ hx
    have hlt : xh * 2 ^ ls + r < s.n := by
      rw [hq]
      calc xh * 2 ^ ls + r < xh * 2 ^ ls + 2 ^ ls := by omega
        _ = (xh + 1) * 2 ^ ls := by ring
        _ ≤ q * 2 ^ ls := Nat.mul_le_mul_right _ hxq
    have hcomm : xh * 2 ^ ls + r = 2 ^ ls * xh + r := by ring
    obtain ⟨Q, hQ⟩ := A.start xh hx
    have hin := A.inside _ hlt
    rw [hcomm, A.run xh r hx hr, hQ] at hin
    have hsplit : lJ = lJ - ls + ls := by omega
    have hQlt : Q < 2 ^ (lJ - ls) := by
      rw [hsplit, pow_add] at hin
      by_contra hc
      have h1 : 2 ^ (lJ - ls) ≤ Q := Nat.le_of_not_lt hc
      have h2 : 2 ^ ls * 2 ^ (lJ - ls) ≤ 2 ^ ls * Q := Nat.mul_le_mul_left _ h1
      have h3 : 2 ^ (lJ - ls) * 2 ^ ls = 2 ^ ls * 2 ^ (lJ - ls) := by ring
      omega
    rw [getD_map_lt _ _ (by rw [A.size]; exact hlt) zeroE 0,
      getD_map_lt _ _ (by simpa using hx) zeroE 0, hcomm, A.run xh r hx hr]
    have hr0 : (Array.range (s.n / 2 ^ ls)).getD xh 0 = xh := by simp [Array.getD, hx]
    rw [hr0, hQ, Nat.mul_div_cancel_left Q hpos,
      eqTab_value ρ z _ (by rw [hz]; rw [← hQ, ← A.run xh r hx hr, ← hcomm]; exact A.inside _ hlt),
      eqTab_value ρ zh _ (by rw [hzh]; exact hQlt), hz, hzh, eqN_shift']
    have e := Blocks.eqN_append (lJ - ls) ls 0 (pt ρ z) Q hr
    rw [← hsplit, Nat.zero_add] at e
    rw [e]
    congr 1
    refine eqN_congr' _ _ (fun j hj => ?_) Q
    unfold pt
    rw [Nat.zero_add, hpre j hj]
  · have hge : s.n ≤ xh * 2 ^ ls + r := by
      have h1 : q ≤ xh := by rw [← hdiv]; exact Nat.le_of_not_lt hx
      have h2 : q * 2 ^ ls ≤ xh * 2 ^ ls := Nat.mul_le_mul_right _ h1
      omega
    rw [getD_ge _ (by simpa [A.size] using hge), getD_ge _ (by simpa using Nat.le_of_not_lt hx),
      ρ.zero, zero_mul]

/-- The same for the two tables that the lookup's join makes for call q, which has 2^lJ columns: its
point has the ll coordinates of the layer, then the lJ of the column. The join passes the size S2 of
a block where 2^ls stands here; the two are equal in a layout. -/
theorem blocked_join (v : Env) (q lJ : ℕ) (hsz : v.y.h.ll + lJ ≤ (v.zk.getD q #[]).size)
    (hls : v.y.ls ≤ lJ) (s : Seg) (A : Aligned s v.y.ls lJ) :
    Blocked ρ (Env.ewFrom (eqTab (v.zj q lJ)) s)
      (Env.ewhFrom (2 ^ v.y.ls) (eqTab (v.zj q (lJ - v.y.ls))) s) v.y.ls
      (fun j => pt ρ (v.zj q lJ) (lJ - v.y.ls + j)) := by
  have s1 : (v.zj q lJ).size = lJ := by
    unfold Env.zj
    rw [Array.size_extract]
    omega
  have s2 : (v.zj q (lJ - v.y.ls)).size = lJ - v.y.ls := by
    unfold Env.zj
    rw [Array.size_extract]
    omega
  refine blocked_of_aligned ρ _ _ s1 hls s2 (fun j hj => ?_) s A
  have h1 : j < (v.zj q (lJ - v.y.ls)).size := by rw [s2]; exact hj
  have h2 : j < (v.zj q lJ).size := by rw [s1]; omega
  unfold Env.zj at h1 h2 ⊢
  simp [Array.getD, Array.size_extract] at h1 h2 ⊢
  simp [h1, h2]

#print axioms blocked_join
#print axioms eqTab_size
#print axioms eqTab_value

end OnBytes.Road
