-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/FromLookup.lean: THE LAW OF WHAT COMES IN FROM THE LOOKUP, PROVED:
FromLookupStatement of HeadInLaw.lean.
In order: 1. outputs of the field's operations are canonical; 2. entry i of eqAll z is eq z i, as
records; 3. arrays made over a range, their sums, the sums of beginnings; 4. a call's columns: a
block of S2 entries of a key whose length is a multiple of S2 takes S2 neighbouring columns from a
multiple of S2 on; 5. the equality weight at a point in two parts; 6. the parts of a key point that
passes the test; 7. one key's weights; 8. fromLookup's letters are these; 9. the law.
Read in the field through Law/Base.lean and Law/Corner.lean (rd, wt, rd_eq), back to records
by eq_of_rd (Law/Lemma2a.lean). wt_app is Law/Mle.lean's wt_append, and pos_S2, sum_cut are
Law/Closed.lean's S2_pos, sum_range_ite_lt, typed again here: the first so that this file stands on
Lemma 2a's imports alone, the others because theirs ask for classes that this law has not.
-/
import Mathlib
import Johnson.Desc.Kinds.HeadInLaw
import Johnson.Desc.Kinds.Law.Lemma2a

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E okE addE subE mulE)
open Norm (lt ls d S2)

/-! ## 1. Canonical outputs -/

theorem okE_mul (a b : E) : okE (a * b) = true := by
  show okE (mulE a b) = true
  rw [OnBytes.okE_triple, OnBytes.mulE_triple]
  unfold Fmt.Fld.okE Fmt.Fld.mulE
  simp [Fmt.Fld.ok_add]

theorem okE_sub (a b : E) : okE (a - b) = true := by
  show okE (subE a b) = true
  rw [OnBytes.okE_triple, OnBytes.subE_triple]
  unfold Fmt.Fld.okE Fmt.Fld.subE
  simp [Fmt.Fld.ok_sub]

theorem okE_one : okE (1 : E) = true := by decide

/-! ## 2. eqAll -/

/-- The fold of HeadParts.lean's eq, from a on. -/
def walk (i : Nat) (l : List E) (a : E) : E :=
  (l.foldl (fun (s : E × Nat) x =>
    (if i.testBit (s.2 - 1) then s.1 * x else s.1 - s.1 * x, s.2 - 1)) (a, l.length)).1

theorem walk_cons (i : Nat) (x : E) (xs : List E) (a : E) :
    walk i (x :: xs) a = walk i xs (if i.testBit xs.length then a * x else a - a * x) := by
  unfold walk
  simp only [List.foldl_cons, List.length_cons, Nat.add_sub_cancel]

theorem eq_walk (z : Point) (i : Nat) :
    eq z i = if i < 2 ^ z.size then walk i z.toList 1 else 0 := by
  unfold eq walk
  rw [Array.length_toList, Array.foldl_toList]

theorem okE_walk (i : Nat) : ∀ (l : List E) (a : E), okE a = true → okE (walk i l a) = true
  | [], _, h => h
  | x :: xs, a, _ => by
    rw [walk_cons]
    apply okE_walk i xs
    split
    · exact okE_mul _ _
    · exact okE_sub _ _

theorem okE_eq (z : Point) (i : Nat) : okE (eq z i) = true := by
  rw [eq_walk]
  split
  · exact okE_walk i _ _ okE_one
  · exact okE_zero

/-- What one coordinate makes of one weight. -/
def two (x a : E) : List E := [a - a * x, a * x]

theorem two_get (x : E) : ∀ (l : List E) (k : Nat),
    (l.flatMap (two x))[k]? = l[k / 2]?.map fun a => if k % 2 = 1 then a * x else a - a * x
  | [], k => by simp
  | a :: l, 0 => by simp [two]
  | a :: l, 1 => by simp [two]
  | a :: l, k + 2 => by
    have e1 : (k + 2) / 2 = k / 2 + 1 := by omega
    have e2 : (k + 2) % 2 = k % 2 := by omega
    rw [e1, e2, List.getElem?_cons_succ, ← two_get x l k]
    simp [List.flatMap_cons, two]

theorem spread_get : ∀ (l acc : List E) (i : Nat),
    (l.foldl (fun t x => t.flatMap (two x)) acc)[i]? = acc[i / 2 ^ l.length]?.map (walk i l)
  | [], acc, i => by
    have h : walk i [] = id := funext fun _ => rfl
    simp [h]
  | x :: xs, acc, i => by
    have e1 : i / 2 ^ xs.length / 2 = i / 2 ^ (xs.length + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    rw [List.foldl_cons, spread_get xs, two_get, List.length_cons, Option.map_map, e1]
    congr 1
    funext a
    simp only [Function.comp, walk_cons]
    have e2 : (i / 2 ^ xs.length % 2 = 1) ↔ i.testBit xs.length = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp
    by_cases h : i.testBit xs.length = true
    · rw [if_pos (e2.2 h), if_pos h]
    · rw [if_neg (fun h' => h (e2.1 h')), if_neg h]

theorem push_two (x : E) : ∀ (l : List E) (n : Array E),
    (l.foldl (fun n a => (n.push (a - a * x)).push (a * x)) n).toList
      = n.toList ++ l.flatMap (two x)
  | [], n => by simp
  | a :: l, n => by
    rw [List.foldl_cons, push_two x l, List.flatMap_cons]
    simp [two]

theorem eqAll_toList (z : Point) :
    (eqAll z).toList = z.toList.foldl (fun t x => t.flatMap (two x)) [1] := by
  have h : ∀ (l : List E) (t : Array E),
      (l.foldl (fun t x => t.foldl (fun n a => (n.push (a - a * x)).push (a * x)) #[]) t).toList
        = l.foldl (fun t x => t.flatMap (two x)) t.toList := by
    intro l
    induction l with
    | nil => intro t; rfl
    | cons x xs ih =>
      intro t
      rw [List.foldl_cons, List.foldl_cons, ih, ← Array.foldl_toList, push_two]
      simp
  unfold eqAll
  rw [← Array.foldl_toList]
  exact h z.toList #[1]

theorem getD_list (a : Array E) (i : Nat) (v : E) : a.getD i v = a.toList[i]?.getD v := by
  first
    | simp
    | rw [Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- **Entry i of eqAll z is eq z i.** -/
theorem eqAll_getD (z : Point) (i : Nat) : (eqAll z).getD i 0 = eq z i := by
  rw [getD_list, eqAll_toList, spread_get, Array.length_toList, eq_walk]
  by_cases hi : i < 2 ^ z.size
  · rw [if_pos hi, Nat.div_eq_of_lt hi]
    rfl
  · rw [if_neg hi]
    have h1 : 0 < i / 2 ^ z.size := Nat.div_pos (Nat.le_of_not_lt hi) (by positivity)
    obtain ⟨m, hm⟩ : ∃ m, i / 2 ^ z.size = m + 1 := ⟨i / 2 ^ z.size - 1, by omega⟩
    rw [hm]
    rfl

/-! ## 3. Arrays over a range, and sums -/

theorem getD_mapRange (n : Nat) (f : Nat → E) (x : Nat) :
    ((Array.range n).map f).getD x 0 = if x < n then f x else 0 := by
  rw [getD_list, Array.toList_map, Array.toList_range, List.getElem?_map]
  by_cases h : x < n
  · rw [List.getElem?_range h, if_pos h]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_range]; omega), if_neg h]
    rfl

theorem sumTo_succ (n : Nat) (f : Nat → E) : sumTo (n + 1) f = sumTo n f + f n := by
  unfold sumTo
  rw [List.range_succ, List.foldl_append]
  rfl

theorem sumTo_congr {f g : Nat → E} (n : Nat) (h : ∀ i, i < n → f i = g i) :
    sumTo n f = sumTo n g := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo_succ, sumTo_succ, ih fun i hi => h i (Nat.lt_succ_of_lt hi),
      h n (Nat.lt_succ_self n)]

theorem foldl_mapRange (n : Nat) (f : Nat → E) :
    ((Array.range n).map f).foldl (· + ·) 0 = sumTo n f := by
  unfold sumTo
  rw [← Array.foldl_toList, Array.toList_map, Array.toList_range, List.foldl_map]

theorem toList_extract (a : Array E) (i j : Nat) :
    (a.extract i j).toList = (a.toList.drop i).take (j - i) := by
  rw [Array.toList_extract, List.extract_eq_take_drop]

theorem foldl_extract_mapRange (n m : Nat) (f : Nat → E) :
    (((Array.range n).map f).extract 0 m).foldl (· + ·) 0 = sumTo (min m n) f := by
  unfold sumTo
  rw [← Array.foldl_toList, toList_extract, List.drop_zero, Nat.sub_zero, Array.toList_map,
    Array.toList_range, ← List.map_take, List.take_range, List.foldl_map]

theorem sum_cut {M : Type} [AddCommMonoid M] {a b : Nat} (h : a ≤ b) (f : Nat → M) :
    (Finset.range b).sum (fun x => if x < a then f x else 0) = (Finset.range a).sum f := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- A sum over a beginning is the sum over all with 0 elsewhere. -/
theorem sumTo_cut (n m : Nat) (f : Nat → E) (c : Nat → Prop) [DecidablePred c]
    (hc : ∀ x, x < n → (c x ↔ x < m)) :
    sumTo (min m n) f = sumTo n fun x => if c x then f x else 0 := by
  apply eq_of_rd (okE_sumTo _ _) (okE_sumTo _ _)
  rw [rd_sumTo, rd_sumTo, ← sum_cut (Nat.min_le_right m n) fun x => rd (f x)]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.mem_range.mp hx
  by_cases h : c x
  · rw [if_pos h, if_pos (lt_min_iff.2 ⟨(hc x hx').1 h, hx'⟩)]
  · rw [if_neg h, if_neg (fun h' => h ((hc x hx').2 (lt_min_iff.1 h').1)), rd_zero]

/-- The sums of the beginnings, as fromLookup makes them. -/
def run (f : Nat → E) (n : Nat) : Array E × E :=
  (List.range n).foldl (fun (a : Array E × E) v =>
    let s := a.2 + f v
    (a.1.push s, s)) (#[0], 0)

theorem run_succ (f : Nat → E) (n : Nat) :
    run f (n + 1) = ((run f n).1.push ((run f n).2 + f n), (run f n).2 + f n) := by
  unfold run
  rw [List.range_succ, List.foldl_append]
  rfl

theorem run_spec (f : Nat → E) : ∀ n : Nat, (run f n).2 = sumTo n f ∧ (run f n).1.size = n + 1 ∧
    ∀ v, v ≤ n → (run f n).1.getD v 0 = sumTo v f
  | 0 => ⟨rfl, rfl, fun v hv => by
      have h0 : v = 0 := by omega
      subst h0
      rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := run_spec f n
    rw [run_succ]
    refine ⟨by rw [sumTo_succ, h1], by simp [h2], fun v hv => ?_⟩
    show ((run f n).1.push ((run f n).2 + f n)).getD v 0 = _
    rw [getD_list, Array.toList_push]
    by_cases hv' : v ≤ n
    · rw [List.getElem?_append_left (by rw [Array.length_toList, h2]; omega), ← getD_list,
        h3 v hv']
    · have h0 : v = n + 1 := by omega
      subst h0
      rw [List.getElem?_append_right (by rw [Array.length_toList, h2]), Array.length_toList, h2,
        Nat.sub_self, sumTo_succ, h1]
      rfl

/-! ## 4. A call's columns -/

/-- The piece of entry x in a key of length n: its exponent. -/
def piece (n x : Nat) : Nat :=
  ((List.range 41).find? fun b => n.testBit b && above b n ≤ x && x < above b n + 2 ^ b).getD 0

theorem column_eq (lens : List Nat) (s x : Nat) :
    column lens s x = (lens.map (above (piece (lens.getD s 0) x))).sum
      + ((lens.take s).filter (·.testBit (piece (lens.getD s 0) x))).length
          * 2 ^ piece (lens.getD s 0) x
      + (x - above (piece (lens.getD s 0) x) (lens.getD s 0)) := rfl

theorem exists_piece {n x : Nat} (hx : x < n) (hn : n < 2 ^ 41) :
    ∃ b, b < 41 ∧ n.testBit b = true ∧ above b n ≤ x ∧ x < above b n + 2 ^ b := by
  have step : ∀ m, ¬ (x / 2 ^ m < n / 2 ^ m) →
      ∃ b, b < m ∧ x / 2 ^ b < n / 2 ^ b ∧ ¬ (x / 2 ^ (b + 1) < n / 2 ^ (b + 1)) := by
    intro m
    induction m with
    | zero => intro h; exact absurd (by simpa using hx) h
    | succ m ih =>
      intro h
      by_cases hm : x / 2 ^ m < n / 2 ^ m
      · exact ⟨m, Nat.lt_succ_self m, hm, h⟩
      · obtain ⟨b, hb, h1, h2⟩ := ih hm
        exact ⟨b, Nat.lt_succ_of_lt hb, h1, h2⟩
  have h41 : ¬ (x / 2 ^ 41 < n / 2 ^ 41) := by
    rw [Nat.div_eq_of_lt hn]
    exact Nat.not_lt_zero _
  obtain ⟨b, hb, h1, h2⟩ := step 41 h41
  have hp : 0 < 2 ^ b := by positivity
  have e : ∀ y, y / 2 ^ (b + 1) = y / 2 ^ b / 2 := fun y => by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [e, e] at h2
  have hab : above b n = 2 ^ b * (x / 2 ^ b) := by
    unfold above
    rw [e, pow_succ]
    have hq : x / 2 ^ b = 2 * (n / 2 ^ b / 2) := by omega
    rw [hq]
    ring
  have hdm := Nat.div_add_mod x (2 ^ b)
  have hml := Nat.mod_lt x hp
  refine ⟨b, hb, ?_, ?_, ?_⟩
  · rw [Nat.testBit_eq_decide_div_mod_eq]
    exact decide_eq_true (by omega)
  · rw [hab]
    omega
  · rw [hab]
    omega

theorem piece_spec {n x : Nat} (hx : x < n) (hn : n < 2 ^ 41) :
    n.testBit (piece n x) = true ∧ above (piece n x) n ≤ x
      ∧ x < above (piece n x) n + 2 ^ piece n x := by
  have key : ∀ o : Option Nat,
      (List.range 41).find? (fun b => n.testBit b && above b n ≤ x && x < above b n + 2 ^ b) = o →
      n.testBit (o.getD 0) = true ∧ above (o.getD 0) n ≤ x
        ∧ x < above (o.getD 0) n + 2 ^ (o.getD 0) := by
    intro o h
    cases o with
    | none =>
      obtain ⟨b, hb, h1, h2, h3⟩ := exists_piece hx hn
      have h4 := List.find?_eq_none.1 h b (List.mem_range.2 hb)
      simp [h1, h2, h3] at h4
    | some b =>
      have h4 := List.find?_some h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
      exact ⟨h4.1.1, h4.1.2, h4.2⟩
  exact key _ rfl

theorem le_block {S A i j : Nat} (hS : 0 < S) (hj : j < S) :
    A * S ≤ S * i + j ↔ A * S ≤ S * i := by
  rw [← Nat.le_div_iff_mul_le hS, ← Nat.le_div_iff_mul_le hS, Nat.mul_add_div hS,
    Nat.div_eq_of_lt hj, Nat.mul_div_cancel_left _ hS, Nat.add_zero]

theorem lt_block {S A i j : Nat} (hS : 0 < S) (hj : j < S) :
    S * i + j < A * S ↔ S * i < A * S := by
  rw [← Nat.div_lt_iff_lt_mul hS, ← Nat.div_lt_iff_lt_mul hS, Nat.mul_add_div hS,
    Nat.div_eq_of_lt hj, Nat.mul_div_cancel_left _ hS, Nat.add_zero]

/-- A set bit of a multiple of 2^l is at l or above. -/
theorem le_of_testBit {l n b : Nat} (hd : 2 ^ l ∣ n) (hb : n.testBit b = true) : l ≤ b := by
  by_contra hlt
  obtain ⟨c, rfl⟩ := hd
  have h := Nat.testBit_two_pow_mul_add c (show 0 < 2 ^ l by positivity) b
  rw [Nat.add_zero, if_pos (by omega), Nat.zero_testBit] at h
  rw [h] at hb
  exact Bool.false_ne_true hb

theorem dvd_above {l b : Nat} (h : l ≤ b) (n : Nat) : 2 ^ l ∣ above b n :=
  Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _

theorem piece_block {l n i j : Nat} (hd : 2 ^ l ∣ n) (hj : j < 2 ^ l) :
    piece n (2 ^ l * i + j) = piece n (2 ^ l * i) := by
  have hS : 0 < 2 ^ l := by positivity
  have hp : (fun b => n.testBit b && decide (above b n ≤ 2 ^ l * i + j)
        && decide (2 ^ l * i + j < above b n + 2 ^ b))
      = fun b => n.testBit b && decide (above b n ≤ 2 ^ l * i)
        && decide (2 ^ l * i < above b n + 2 ^ b) := by
    funext b
    cases hb : n.testBit b with
    | false => simp
    | true =>
      have hlb : l ≤ b := le_of_testBit hd hb
      obtain ⟨A, hA⟩ := dvd_above hlb n
      obtain ⟨B, hB⟩ : 2 ^ l ∣ 2 ^ b := pow_dvd_pow 2 hlb
      have h1 : above b n ≤ 2 ^ l * i + j ↔ above b n ≤ 2 ^ l * i := by
        rw [hA, Nat.mul_comm (2 ^ l) A]
        exact le_block hS hj
      have h2 : 2 ^ l * i + j < above b n + 2 ^ b ↔ 2 ^ l * i < above b n + 2 ^ b := by
        rw [hA, hB, ← Nat.mul_add, Nat.mul_comm (2 ^ l) (A + B)]
        exact lt_block hS hj
      simp only [h1, h2]
  unfold piece
  rw [hp]

/-- **A block of 2^l entries takes 2^l neighbouring columns from a multiple of 2^l on.** -/
theorem column_block {lens : List Nat} {s i j l : Nat} (hd : 2 ^ l ∣ lens.getD s 0)
    (hn : lens.getD s 0 < 2 ^ 41) (hj : j < 2 ^ l) (hx : 2 ^ l * i + j < lens.getD s 0) :
    column lens s (2 ^ l * i + j) = column lens s (2 ^ l * i) + j
      ∧ 2 ^ l ∣ column lens s (2 ^ l * i) := by
  have hx0 : 2 ^ l * i < lens.getD s 0 := by omega
  obtain ⟨t1, t2, _⟩ := piece_spec hx0 hn
  have hb : l ≤ piece (lens.getD s 0) (2 ^ l * i) := le_of_testBit hd t1
  rw [column_eq, column_eq, piece_block hd hj]
  generalize piece (lens.getD s 0) (2 ^ l * i) = b at t2 hb ⊢
  constructor
  · omega
  · refine dvd_add (dvd_add ?_ ?_) ?_
    · apply List.dvd_sum
      intro y hy
      obtain ⟨n, _, rfl⟩ := List.mem_map.1 hy
      exact dvd_above hb n
    · exact Dvd.dvd.mul_left (pow_dvd_pow 2 hb) _
    · exact Nat.dvd_sub (dvd_mul_right _ _) (dvd_above hb _)

/-! ## 5. A point in two parts -/

theorem wt_app : ∀ (a b : List K) (i : Nat), wt (a ++ b) i = wt a (i / 2 ^ b.length) * wt b i
  | [], b, i => by simp [wt]
  | x :: xs, b, i => by
    simp only [List.cons_append, wt, List.length_append]
    rw [wt_app xs b i, Nat.testBit_div_two_pow]
    ring

/-- **The equality weight at a point in two parts**, as records. -/
theorem eq_split {z pa pb : Point} (h : z.toList = pa.toList ++ pb.toList) (q j : Nat)
    (hj : j < 2 ^ pb.size) : eq z (2 ^ pb.size * q + j) = eq pa q * eq pb j := by
  apply eq_of_rd (okE_eq _ _) (okE_mul _ _)
  have hs : z.size = pa.size + pb.size := by
    have h0 := congrArg List.length h
    simpa using h0
  have hpos : 0 < 2 ^ pb.size := by positivity
  have h1 : (2 ^ pb.size * q + j) / 2 ^ pb.size = q := by
    rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hj, Nat.add_zero]
  have h2 : wt (pb.toList.map rd) (2 ^ pb.size * q + j) = wt (pb.toList.map rd) j := by
    apply wt_congr
    intro t ht
    rw [List.length_map, Array.length_toList] at ht
    rw [Nat.testBit_two_pow_mul_add _ hj, if_pos ht]
  have hiff : 2 ^ pb.size * q + j < 2 ^ (pa.size + pb.size) ↔ q < 2 ^ pa.size := by
    rw [pow_add, ← Nat.div_lt_iff_lt_mul hpos, h1]
  rw [rd_mul, rd_eq, rd_eq, rd_eq, if_pos hj, h, List.map_append, wt_app, List.length_map,
    Array.length_toList, hs, h1, h2]
  by_cases hq : q < 2 ^ pa.size
  · rw [if_pos (hiff.2 hq), if_pos hq]
  · rw [if_neg (fun h' => hq (hiff.1 h')), if_neg hq, zero_mul]

/-! ## 6. The parts of a key point that passes the test -/

theorem toList_last (z : Point) (n : Nat) : (z.last n).toList = z.toList.drop (z.size - n) := by
  unfold Point.last
  rw [toList_extract]
  apply List.take_of_length_le
  simp

/-- The last b of the last a + b coordinates are the last b. -/
theorem toList_last_last (z : Point) (a b : Nat) :
    ((z.last (a + b)).last b).toList = (z.last b).toList := by
  have hs : (z.last (a + b)).size = z.size - (z.size - (a + b)) := by
    rw [← Array.length_toList, toList_last, List.length_drop, Array.length_toList]
  rw [toList_last, toList_last, toList_last, hs, List.drop_drop]
  congr 1
  omega

/-- The lookup's point on the positions is the end of every key point. -/
theorem zt_of_test {zkc zx : Point} {J a b : Nat} (hsz : zkc.size = J + b)
    (hl : zkc.last (a + b) = zx.last (a + b)) : (zx.last b).toList = zkc.toList.drop J := by
  rw [← toList_last_last zx a b, ← hl, toList_last_last, toList_last, hsz]
  congr 1
  omega

/-- A key point's part on the columns ends in the lookup's point on a block's features. -/
theorem split_of_test {zkc zx : Point} {J a b : Nat} (hsz : zkc.size = J + b)
    (hl : zkc.last (a + b) = zx.last (a + b)) (hJ : a ≤ J) :
    (zkc.extract 0 J).toList
        = ((zkc.extract 0 J).extract 0 ((zkc.extract 0 J).size - a)).toList
          ++ ((zx.last (a + b)).extract 0 a).toList
      ∧ ((zx.last (a + b)).extract 0 a).size = a := by
  have hlen : zkc.toList.length = J + b := by rw [Array.length_toList, hsz]
  have s1 : (zkc.extract 0 J).size = J := by
    rw [← Array.length_toList, toList_extract, List.length_take, List.length_drop, hlen]
    exact Nat.min_eq_left (by omega)
  have e3 : ((zx.last (a + b)).extract 0 a).toList = (zkc.toList.drop (J - a)).take a := by
    rw [← hl, toList_extract, toList_last, hsz, List.drop_zero, Nat.sub_zero]
    congr 2
    omega
  constructor
  · rw [e3, s1]
    simp only [toList_extract, List.drop_zero, Nat.sub_zero, List.take_take]
    rw [Nat.min_eq_left (Nat.sub_le J a)]
    have hJe : J = (J - a) + a := by omega
    conv_lhs => rw [hJe]
    rw [List.take_add]
  · rw [← Array.length_toList, e3, List.length_take, List.length_drop, hlen]
    exact Nat.min_eq_left (by omega)

/-! ## 7. One key's weights -/

section Sized
variable [Sizes]

theorem pos_S2 : 0 < S2 := by
  unfold S2
  positivity

theorem kw_ew (zj : Point) (lens : List Nat) (s : Nat) (k : PlaceKey) (x : Nat) :
    (keyWeights zj lens s k).ew.getD x 0
      = if x < lenOf k then eq zj (column lens s x) else 0 := by
  show ((Array.range (lenOf k)).map fun x => (eqAll zj).getD (column lens s x) 0).getD x 0 = _
  rw [getD_mapRange, eqAll_getD]

theorem kw_ewh (zj : Point) (lens : List Nat) (s : Nat) (k : PlaceKey) (i : Nat) :
    (keyWeights zj lens s k).ewh.getD i 0
      = if i < lenOf k / S2 then
          eq (zj.extract 0 (zj.size - ls)) (column lens s (S2 * i) / S2) else 0 := by
  show ((Array.range (lenOf k / S2)).map fun i =>
    (eqAll (zj.extract 0 (zj.size - ls))).getD (column lens s (S2 * i) / S2) 0).getD i 0 = _
  rw [getD_mapRange, eqAll_getD]

theorem kw_wsum (zj : Point) (lens : List Nat) (s : Nat) (k : PlaceKey) :
    (keyWeights zj lens s k).wsum
      = sumTo (lenOf k) fun x => (keyWeights zj lens s k).ew.getD x 0 := by
  show ((Array.range (lenOf k)).map fun x => (eqAll zj).getD (column lens s x) 0).foldl
    (· + ·) 0 = _
  rw [foldl_mapRange]
  apply sumTo_congr
  intro x hx
  rw [kw_ew, if_pos hx, eqAll_getD]

theorem kw_wx (zj : Point) (lens : List Nat) (s : Nat) (k : PlaceKey) :
    (keyWeights zj lens s k).wx = sumTo (lenOf k) fun x =>
      if (firstEntry k).getD 0 + x < V then (keyWeights zj lens s k).ew.getD x 0 else 0 := by
  show (((Array.range (lenOf k)).map fun x => (eqAll zj).getD (column lens s x) 0).extract 0
    (V - (firstEntry k).getD 0)).foldl (· + ·) 0 = _
  rw [foldl_extract_mapRange,
    sumTo_cut (lenOf k) (V - (firstEntry k).getD 0) _ (fun x => (firstEntry k).getD 0 + x < V)
      (fun x _ => by omega)]
  apply sumTo_congr
  intro x hx
  rw [kw_ew, if_pos hx, eqAll_getD]

omit [Sizes] in
theorem le_two_pow_clog2 (n : Nat) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  split
  · rename_i h
    simpa using h
  · have h := Nat.lt_log2_self (n := n - 1)
    omega

theorem ls_le_lJ (floor : Nat) {keys : List PlaceKey} {k : PlaceKey} (hk : k ∈ keys)
    (h : S2 ≤ lenOf k) : ls ≤ lJ floor keys := by
  have h1 : lenOf k ≤ (keys.map lenOf).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨k, hk, rfl⟩)
  have h3 : 2 ^ ls ≤ 2 ^ clog2 (keys.map lenOf).sum :=
    le_trans (le_trans h h1) (le_two_pow_clog2 _)
  exact le_trans ((Nat.pow_le_pow_iff_right (by norm_num)).1 h3) (le_max_left _ _)

/-! ## 8. fromLookup's letters -/

/-- A key's weights, as fromLookup makes them. -/
def made (floor : Nat) (zk : Nat → Point) (k : PlaceKey) : KeyWeights :=
  keyWeights (onColumns floor zk k) ((keysOf k).map lenOf) (placeOf k).2 k

theorem ew_made (floor : Nat) (zx : Point) (zk : Nat → Point) (k : PlaceKey) (x : Nat) :
    ewOf (fromLookup floor zx zk) k x = (made floor zk k).ew.getD x 0 := by
  rcases k with k | k <;> cases k <;> rfl

theorem ewh_made (floor : Nat) (zx : Point) (zk : Nat → Point) (k : PlaceKey) (i : Nat) :
    ewhOf (fromLookup floor zx zk) k i = (made floor zk k).ewh.getD i 0 := by
  rcases k with k | k <;> cases k <;> rfl

theorem wsum_made (floor : Nat) (zx : Point) (zk : Nat → Point) (k : PlaceKey) :
    wsumOf (fromLookup floor zx zk) k = (made floor zk k).wsum := by
  rcases k with k | k <;> cases k <;> rfl

theorem wx_made (floor : Nat) (zx : Point) (zk : Nat → Point) (k : Key) :
    (fromLookup floor zx zk).head.wx k = (made floor zk (.inr k)).wx := by
  cases k <;> rfl

theorem below_made (floor : Nat) (zx : Point) (zk : Nat → Point) (v : Nat) :
    (fromLookup floor zx zk).head.below v
      = (run (fun v => (made floor zk (.inr .marginTop)).ew.getD v 0) V).1.getD v 0 := rfl

omit [Sizes] in
theorem mem_keysOf (k : PlaceKey) : k ∈ keysOf k := by
  rcases k with k | k <;> cases k <;> simp [keysOf, placeOf, callList]

omit [Sizes] in
theorem call_keysOf (k : PlaceKey) : callList[(placeOf k).1]? = some (keysOf k) := by
  rcases k with k | k <;> cases k <;> rfl

theorem len_keysOf (k : PlaceKey) : ((keysOf k).map lenOf).getD (placeOf k).2 0 = lenOf k := by
  rcases k with k | k <;> cases k <;> rfl

/-! ## 9. The law -/

theorem block_law {floor : Nat} {zx : Point} {zk : Nat → Point} (hP : PointsOk floor zx zk)
    (k : PlaceKey) (hlen : lenOf k < 2 ^ 41) (hd : S2 ∣ lenOf k) (x : Nat) (hx : x < lenOf k) :
    (made floor zk k).ew.getD x 0
      = (made floor zk k).ewh.getD (x / S2) 0 * eq ((zx.last (ls + lt)).extract 0 ls) (x % S2) := by
  obtain ⟨hsz, hl⟩ := hP _ _ (call_keysOf k)
  have hS : S2 ≤ lenOf k := Nat.le_of_dvd (by omega) hd
  obtain ⟨hsplit, hzl⟩ := split_of_test hsz hl (ls_le_lJ floor (mem_keysOf k) hS)
  have hj : x % S2 < 2 ^ ls := Nat.mod_lt _ pos_S2
  have hxe : 2 ^ ls * (x / S2) + x % S2 = x := Nat.div_add_mod x S2
  have hi : x / S2 < lenOf k / S2 := by
    obtain ⟨m, hm⟩ := hd
    rw [hm, Nat.mul_div_cancel_left _ pos_S2]
    exact Nat.div_lt_of_lt_mul (hm ▸ hx)
  obtain ⟨c1, q, hq⟩ := column_block (lens := (keysOf k).map lenOf) (s := (placeOf k).2)
    (i := x / S2) (j := x % S2) (l := ls) (by rw [len_keysOf]; exact hd)
    (by rw [len_keysOf]; exact hlen) hj (by rw [len_keysOf, hxe]; exact hx)
  rw [hxe] at c1
  have hsp := eq_split hsplit q (x % S2) (by rw [hzl]; exact hj)
  rw [hzl] at hsp
  unfold made
  rw [kw_ew, if_pos hx, kw_ewh, if_pos hi, c1]
  have hq' : column ((keysOf k).map lenOf) (placeOf k).2 (S2 * (x / S2)) = 2 ^ ls * q := hq
  rw [hq, hq']
  have hdiv : 2 ^ ls * q / S2 = q := Nat.mul_div_cancel_left q pos_S2
  rw [hdiv]
  exact hsp

theorem S2_le_JV (hV : 0 < V) : S2 ≤ JV := by
  unfold JV
  exact Nat.le_mul_of_pos_left _ (Nat.div_pos (by omega) pos_S2)

end Sized

/-- **THE LAW OF fromLookup.** -/
theorem fromLookup_law : FromLookupStatement := by
  intro _ floor zx zk hV hlen hP
  have eH : ∀ (k : Key) (x : Nat),
      (fromLookup floor zx zk).head.ew k x = (made floor zk (.inr k)).ew.getD x 0 :=
    fun k x => ew_made floor zx zk (.inr k) x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k x hx
    rw [ew_made]
    unfold made
    rw [kw_ew, if_pos hx]
    rfl
  · intro k x hx
    rw [ew_made]
    unfold made
    rw [kw_ew, if_neg (by omega)]
  · intro k hd x hx
    rw [ew_made, ewh_made]
    exact block_law hP k (hlen k) hd x hx
  · intro k
    rw [wsum_made]
    simp only [ew_made]
    exact kw_wsum _ _ _ _
  · intro k
    have hf : (firstEntry (.inr k)).getD 0 = first k := by cases k <;> rfl
    rw [wx_made]
    simp only [eH]
    rw [← hf]
    exact kw_wx _ _ _ _
  · intro v hv
    rw [below_made]
    simp only [eH]
    exact (run_spec _ V).2.2 v hv
  · obtain ⟨hsz, hl⟩ := hP 0 _ rfl
    show (zx.last lt).size = lt
    rw [← Array.length_toList, zt_of_test hsz hl, List.length_drop, Array.length_toList, hsz]
    omega
  · obtain ⟨hsz, hl⟩ := hP _ _ (call_keysOf (.inr .marginMid))
    exact (split_of_test hsz hl (ls_le_lJ floor (mem_keysOf (.inr .marginMid))
      (S2_le_JV hV))).2
  · intro c keys hc
    obtain ⟨hsz, hl⟩ := hP c keys hc
    show _ = _ ++ (zx.last lt).toList
    rw [zt_of_test hsz hl, toList_extract, List.drop_zero, Nat.sub_zero, List.take_append_drop]

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.fromLookup_law
