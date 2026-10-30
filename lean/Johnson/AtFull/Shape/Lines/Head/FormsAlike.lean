-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Head/FormsAlike.lean: the shapes of the output head's 35 forms and six
key vectors (formsSh and keysSh: Johnson/Desc/K6/Shape/Forms.lean, Johnson/Desc/K6/Shape/Keys.lean)
are made of their leaves by "one behind the other" alone, and name a read's entry only below that
read's length. So a relation on forms' shapes that is kept by "one behind the other" and holds leaf
by leaf (of a read's entries those below its length alone) holds form by form. General in the
sizes, the leaves and the relation. Nothing is evaluated.

Why. HeadLeaves.lean gives such a relation at the leaves, and HeadCover.lean needs it at the forms.

  KeptByAppending Q       Q is a relation on forms' shapes that holds at noTerm and that "one behind
                          the other" keeps.
  LeavesAlike Q L L'      Q holds leaf by leaf.
  PositionRowAlike, positionRow_alike   Q holds field by field at a position's row.
  quotientIndex_lt, numberDigit_lt, limbIndex_lt   the counting: every read stays below its length.
  square_alike … logit_alike   the forms run by run.
  **forms_alike**         the 35 forms, run by run.
  **keys_alike**          the six key vectors.
  LeafSh.bare             the leaves with no read.

Limits. An implication, given S2 ∣ d (and JVa ≤ JV at the keys). Nothing on what a form is worth.
What any of this costs Lean's kernel is not measured here. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.K6.Shape.Keys
import Johnson.Desc.Kinds.Law.CoveredNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Shape
open Norm (lt ls d lPd T S2)
open VerifiableInference.Desc.First.Shape (AffSh)
open VerifiableInference.Desc.Kinds.Head.Law (readLenN wideLenN readLen)

local infixl:65 " ⋆ " => AffSh.append

/-- A relation on forms' shapes that holds at noTerm and that "one behind the other" keeps. -/
structure KeptByAppending (Q : AffSh → AffSh → Prop) : Prop where
  nil : Q noTerm noTerm
  app : ∀ {a a' b b' : AffSh}, Q a a' → Q b b' → Q (a ⋆ b) (a' ⋆ b')

/-- Leaf by leaf; of a read's entries those below its length alone. -/
structure LeavesAlike [Sizes] (Q : AffSh → AffSh → Prop) (L L' : LeafSh) : Prop where
  W : ∀ s, Q (L.W s) (L'.W s)
  P : ∀ s, Q (L.P s) (L'.P s)
  sqLeft : Q L.sqLeft L'.sqLeft
  sqEnd : ∀ j, Q (L.sqEnd j) (L'.sqEnd j)
  prLeft : Q L.prLeft L'.prLeft
  prClaimed : Q L.prClaimed L'.prClaimed
  prEnd : ∀ j, Q (L.prEnd j) (L'.prEnd j)
  nmLeft : Q L.nmLeft L'.nmLeft
  nmClaimed : Q L.nmClaimed L'.nmClaimed
  nmEnd : ∀ j, Q (L.nmEnd j) (L'.nmEnd j)
  lgLeft : Q L.lgLeft L'.lgLeft
  lgClaimed : Q L.lgClaimed L'.lgClaimed
  lgEnd : ∀ j, Q (L.lgEnd j) (L'.lgEnd j)
  entryN : ∀ r i, i < readLenN r → Q (L.entryN r i) (L'.entryN r i)
  wide : ∀ i, i < wideLenN → Q (L.wide i) (L'.wide i)
  entryH : ∀ r i, i < readLen r → Q (L.entryH r i) (L'.entryH r i)

variable {Q : AffSh → AffSh → Prop}

/-- A sum of n + 1 terms is the sum of n terms with the last behind it. -/
theorem sumSh_succ (n : Nat) (g : Nat → AffSh) : sumSh (n + 1) g = sumSh n g ⋆ g n := by
  unfold sumSh
  rw [List.range_succ, List.foldl_append]
  rfl

/-- Q holds between two sums where it holds term by term. -/
theorem KeptByAppending.sum (C : KeptByAppending Q) : ∀ (n : Nat) (f f' : Nat → AffSh), (∀ i,
    i < n → Q (f i) (f' i)) →
    Q (sumSh n f) (sumSh n f')
  | 0, _, _, _ => C.nil
  | n + 1, f, f', h => by
    rw [sumSh_succ, sumSh_succ]
    exact C.app (KeptByAppending.sum C n f f' fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n
        (Nat.lt_succ_self n))

/-- Q holds between two folds of "one behind the other" where it holds member by member. -/
theorem KeptByAppending.fold (C : KeptByAppending Q) : ∀ (l l' : List AffSh), List.Forall₂ Q l l' →
    ∀ a a', Q a a' →
    Q (l.foldl (· ⋆ ·) a) (l'.foldl (· ⋆ ·) a')
  | _, _, .nil, _, _, h => h
  | _, _, .cons h1 h2, _, _, h => KeptByAppending.fold C _ _ h2 _ _ (C.app h h1)

/-- So between two lists laid one behind the other. -/
theorem KeptByAppending.cat (C : KeptByAppending Q) {l l' : List AffSh} (h : List.Forall₂ Q l l') :
    Q (catSh l) (catSh l') := KeptByAppending.fold C l l' h _ _ C.nil

/-- So between two sums of digits. -/
theorem KeptByAppending.dig (C : KeptByAppending Q) {D D' : Nat → AffSh} (h : ∀ j, j < 99 →
    Q (D j) (D' j)) (j n : Nat)
    (hj : j + n ≤ 99) : Q (digSh D j n) (digSh D' j n) :=
  C.sum n _ _ fun i hi => h (j + i) (by omega)

/-- A position's row, field by field; the carries up to the ninth. -/
structure PositionRowAlike (Q : AffSh → AffSh → Prop) (ρ ρ' : Row6Sh) : Prop where
  Vlo : Q ρ.Vlo ρ'.Vlo
  Vhi : Q ρ.Vhi ρ'.Vhi
  a : Q ρ.a ρ'.a
  b : Q ρ.b ρ'.b
  s0 : Q ρ.s0 ρ'.s0
  sig : Q ρ.sig ρ'.sig
  l1 : Q ρ.l1 ρ'.l1
  h1 : Q ρ.h1 ρ'.h1
  Blo : Q ρ.Blo ρ'.Blo
  Bhi : Q ρ.Bhi ρ'.Bhi
  kap : Q ρ.kap ρ'.kap
  Rlo : Q ρ.Rlo ρ'.Rlo
  Rhi : Q ρ.Rhi ρ'.Rhi
  R : Q ρ.R ρ'.R
  q1 : Q ρ.q1 ρ'.q1
  rr : Q ρ.rr ρ'.rr
  rq : Q ρ.rq ρ'.rq
  c : ∀ s, s ≤ 9 → Q (ρ.c s) (ρ'.c s)

/-- Q holds field by field at a position's row where it holds digit by digit. -/
theorem positionRow_alike (C : KeptByAppending Q) {D D' : Nat → AffSh} (h : ∀ j, j < 99 →
    Q (D j) (D' j)) :
    PositionRowAlike Q (row6Sh D) (row6Sh D') where
  Vlo := C.dig h 0 6 (by omega)
  Vhi := C.dig h 6 4 (by omega)
  a := C.app (C.app (C.app (h 58 (by omega)) (h 59 (by omega))) (h 60 (by omega))) (h 61 (by omega))
  b := C.app (h 62 (by omega)) (h 63 (by omega))
  s0 := h 59 (by omega)
  sig := C.app
    (C.app (C.app (C.app (h 58 (by omega)) (h 59 (by omega))) (h 60 (by omega))) (h 61 (by omega)))
    (C.app (h 62 (by omega)) (h 63 (by omega)))
  l1 := C.dig h 64 5 (by omega)
  h1 := C.dig h 69 5 (by omega)
  Blo := C.dig h 74 3 (by omega)
  Bhi := C.dig h 77 2 (by omega)
  kap := h 79 (by omega)
  Rlo := C.dig h 80 3 (by omega)
  Rhi := C.dig h 83 3 (by omega)
  R := C.app (C.dig h 80 3 (by omega)) (C.dig h 83 3 (by omega))
  q1 := C.dig h 86 3 (by omega)
  rr := C.dig h 89 5 (by omega)
  rq := C.dig h 94 5 (by omega)
  c := fun s hs => by
    show Q (if s == 0 then noTerm else if s == 9 then D 9 else digSh D (10 + 6 * (s - 1)) 6)
      (if s == 0 then noTerm else if s == 9 then D' 9 else digSh D' (10 + 6 * (s - 1)) 6)
    by_cases h0 : (s == 0) = true
    · rw [if_pos h0, if_pos h0]
      exact C.nil
    · rw [if_neg h0, if_neg h0]
      by_cases h9 : (s == 9) = true
      · rw [if_pos h9, if_pos h9]
        exact h 9 (by omega)
      · rw [if_neg h9, if_neg h9]
        have n9 : s ≠ 9 := fun e => h9 (by rw [e]; rfl)
        exact C.dig h _ 6 (by omega)

/-- A relation between two maps over a range, from the relation at each index. -/
theorem forall₂_map_range {α : Type} {R : α → α → Prop} (n : Nat) (f f' : Nat → α)
    (h : ∀ i, i < n → R (f i) (f' i)) :
    List.Forall₂ R ((List.range n).map f) ((List.range n).map f') := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun i hi => h i (List.mem_range.1 hi)

/-- Appending keeps List.Forall₂. -/
theorem forall₂_append {α : Type} {R : α → α → Prop} {a a' b b' : List α}
    (h1 : List.Forall₂ R a a') (h2 : List.Forall₂ R b b') : List.Forall₂ R (a ++ b) (a' ++ b') :=
  List.rel_append h1 h2

/-- A relation between two maps over one list, from the relation at each member. -/
theorem forall₂_map_same {α β : Type} {R : β → β → Prop} (f f' : α → β) :
    ∀ l : List α, (∀ x, R (f x) (f' x)) → List.Forall₂ R (l.map f) (l.map f')
  | [], _ => .nil
  | x :: l, h => .cons (h x) (forall₂_map_same f f' l h)

/-! The counting. The library's idx_lt0 and number_lt0 (Johnson/Desc/Kinds/Law/Covered.lean) and
limb_lt (Johnson/Desc/Kinds/Law/CoveredNorm.lean) have parameters (Policy, Request, …) that a shape
does not have, so these laws, and S2_positive, are stated here again. -/

/-- An index of a block of a stretch stays below the number of blocks of what holds the stretch. -/
theorem quotientIndex_lt {a n S N i : Nat} (hS : 0 < S) (hi : i < n / S) (h : a + n ≤ N) :
    a / S + i < N / S := by
  have h1 : (a / S + (i + 1)) * S ≤ N := by
    have e1 : a / S * S ≤ a := Nat.div_mul_le_self a S
    have e2 : (i + 1) * S ≤ n / S * S := Nat.mul_le_mul_right S hi
    have e3 : n / S * S ≤ n := Nat.div_mul_le_self n S
    rw [Nat.add_mul]
    omega
  have h2 := (Nat.le_div_iff_mul_le hS).mpr h1
  omega

/-- A digit's place of a Number stays below NR + 21. -/
theorem numberDigit_lt (n : Number) (l : Nat) (hl : l < n.digits.2) : NR + n.digits.1 + l < NR + 21
    := by
  cases n <;> simp only [Number.digits] at hl ⊢ <;> omega

/-- S2 is positive. -/
theorem S2_positive [Norm.Sizes] : 0 < S2 := by unfold S2; exact Nat.pos_of_ne_zero (by simp)

/-- An index of limb l stays below the end of n limbs. -/
theorem limbIndex_lt [Norm.Sizes] {l i n : Nat} (hd : S2 ∣ d) (hl : l < n) (hi : i < d / S2) :
    l * d / S2 + i < n * d / S2 := by
  obtain ⟨q, hq⟩ := hd
  have hS : 0 < S2 := S2_positive
  have e1 : l * d / S2 = l * q := by
    rw [hq, show l * (S2 * q) = S2 * (l * q) by ring, Nat.mul_div_cancel_left _ hS]
  have e2 : n * d / S2 = n * q := by
    rw [hq, show n * (S2 * q) = S2 * (n * q) by ring, Nat.mul_div_cancel_left _ hS]
  have e3 : d / S2 = q := by rw [hq, Nat.mul_div_cancel_left _ hS]
  rw [e1, e2]
  rw [e3] at hi
  have : (l + 1) * q ≤ n * q := Nat.mul_le_mul_right q hl
  nlinarith

section Walk
variable [Sizes] (C : KeptByAppending Q) {L L' : LeafSh} (A : LeavesAlike Q L L')
include C A

/-- At squareSh. -/
theorem square_alike (hd : S2 ∣ d) : List.Forall₂ Q (squareSh L) (squareSh L') :=
  .cons A.sqLeft (.cons (C.app (A.sqEnd 0) (A.sqEnd 1)) (.cons
    (C.app (A.sqEnd 0) (C.sum 1 _ _ fun _ _ => C.sum _ _ _ fun k hk => C.sum 5 _ _ fun l hl =>
      A.entryN .streamAtSquares _ (limbIndex_lt hd hl hk))) .nil))

/-- At productSh. -/
theorem product_alike : List.Forall₂ Q (productSh L) (productSh L') :=
  have R := positionRow_alike C fun j hj => A.entryN .rowAtProducts j hj
  .cons (C.app A.prClaimed (C.sum 7 _ _ fun i _ => A.P i)) (.cons A.prLeft
    (.cons (C.app (A.prEnd 0) R.a) (.cons (C.app (A.prEnd 1) R.b) (.cons (C.app (A.prEnd 2) R.Rlo)
      (.cons (C.app (A.prEnd 3) R.Rhi) .nil)))))

/-- At rowsSh. -/
theorem rows_alike : List.Forall₂ Q (rowsSh L) (rowsSh L') := by
  have hD : ∀ j, j < 99 → Q (L.entryN .rowAtPV j) (L'.entryN .rowAtPV j) :=
    fun j hj => A.entryN .rowAtPV j hj
  have R := positionRow_alike C hD
  refine forall₂_append ?_ (forall₂_append ?_ ?_)
  · exact forall₂_map_range 9 _ _ fun s hs =>
      C.app (C.app (C.app (A.W s) (R.c s (by omega))) (hD s (by omega))) (R.c (s + 1) (by omega))
  · exact .cons (C.app (C.app (A.P 1) R.Blo) R.Bhi)
      (.cons (C.app (C.app (C.app (C.app R.Vlo (A.P 0)) R.Blo) R.l1) R.kap)
        (.cons (C.app (C.app (C.app R.Vhi R.Bhi) (A.P 2)) R.kap)
          (.cons (C.app (C.app R.l1 R.h1) R.sig) .nil)))
  · exact .cons (C.app (C.app (A.P 4) (A.P 5)) R.q1) (.cons (A.P 6)
      (.cons (C.app (C.app (C.app (C.app R.sig R.s0) (A.P 3)) R.q1) R.rr)
        (.cons (C.app (C.app R.rr R.rq) R.sig) .nil)))

/-- At normedSh. -/
theorem normed_alike (hd : S2 ∣ d) : List.Forall₂ Q (normedSh L) (normedSh L') :=
  have R := positionRow_alike C fun j hj => A.entryN .rowAtNormed j hj
  .cons A.nmLeft (.cons (C.app (A.nmEnd 0) R.R) (.cons
    (C.app (A.nmEnd 1) (C.sum _ _ _ fun i hi => C.sum 5 _ _ fun l hl =>
      A.entryN .streamAtNormed _ (limbIndex_lt hd hl hi))) .nil))

/-- At normSh, the run "norm". -/
theorem norm_alike (hd : S2 ∣ d) : List.Forall₂ Q (normSh L) (normSh L') :=
  forall₂_append (forall₂_append (forall₂_append (square_alike C A hd) (product_alike C A))
    (rows_alike C A)) (normed_alike C A hd)

/-- At atCostsSh. -/
theorem atCosts_alike (n : Number) : Q (atCostsSh L n) (atCostsSh L' n) :=
  C.sum _ _ _ fun l hl => A.entryH .rowAtCosts _ (numberDigit_lt n l hl)

/-- At summedSh. -/
theorem summed_alike (n : Number) : Q (summedSh L n) (summedSh L' n) :=
  C.sum _ _ _ fun l hl => A.entryH .rowCount _ (numberDigit_lt n l hl)

/-- At tableCostsSh. -/
theorem tableCosts_alike : Q (tableCostsSh L) (tableCostsSh L') :=
  C.sum 3 _ _ fun l hl => C.sum _ _ _ fun i hi =>
    A.entryH .wideAtCosts _ (quotientIndex_lt S2_positive hi (by
      have : l = 0 ∨ l = 1 ∨ l = 2 := by omega
      rcases this with rfl | rfl | rfl <;> omega))

/-- At policySh, the run "policy". -/
theorem policy_alike : List.Forall₂ Q (policySh L) (policySh L') :=
  .cons (C.app (C.app (summed_alike C A _) (summed_alike C A _)) (summed_alike C A _))
    (.cons (C.app (summed_alike C A _) (summed_alike C A _))
      (.cons (C.app (atCosts_alike C A _) (atCosts_alike C A _))
        (.cons (C.app (atCosts_alike C A _) (tableCosts_alike C A)) .nil)))

/-- At logitSh, the run "logits". -/
theorem logit_alike : List.Forall₂ Q (logitSh L) (logitSh L') :=
  .cons A.lgLeft (.cons (C.app (A.lgEnd 0) (C.sum _ _ _ fun k hk =>
    C.app (A.entryH .actAtLogits k (show k < 2 * d by omega))
      (A.entryH .actAtLogits (d + k) (show d + k < 2 * d by omega)))) .nil)

/-- **The 35 forms, run by run.** -/
theorem forms_alike (hd : S2 ∣ d) :
    List.Forall₂ (fun c c' => c.1 = c'.1 ∧ List.Forall₂ Q c.2 c'.2) (formsSh L) (formsSh L') :=
  .cons ⟨rfl, norm_alike C A hd⟩ (.cons ⟨rfl, policy_alike C A⟩ (.cons ⟨rfl, logit_alike C A⟩ .nil))

/-- At wideAtNSh, at the offsets m * d with m at most 2. -/
theorem wideAtN_alike (hd : S2 ∣ d) (m : Nat) (hm : m ≤ 2) :
    Q (wideAtNSh L (m * d)) (wideAtNSh L' (m * d)) :=
  C.sum _ _ _ fun i hi => C.sum 2 _ _ fun l hl => A.wide _ (by
    rw [← Nat.add_mul]
    exact limbIndex_lt hd (show m + l < 4 by omega) hi)

/-- At the normalization's four keys, with 21 more digits. -/
theorem keyN_alike (hd : S2 ∣ d) (k : FinalNorm.Key) : Q (keyNSh L 21 k) (keyNSh L' 21 k) := by
  have w0 : Q (wideAtNSh L 0) (wideAtNSh L' 0) := by
    have := wideAtN_alike C A hd 0 (by omega)
    rwa [Nat.zero_mul] at this
  have w2 := wideAtN_alike C A hd 2 (by omega)
  cases k with
  | remLow => exact C.app (C.app A.nmClaimed w0) w2
  | remHigh => exact w2
  | clamp =>
    exact C.app w0 (C.sum _ _ _ fun k hk =>
      C.app (A.entryN .actAtKeys k (show k < 2 * d by omega))
        (A.entryN .actAtKeys (d + k) (show d + k < 2 * d by omega)))
  | digits => exact C.sum _ _ _ fun j hj => A.entryN .rowAtKeys j hj

/-- At wideAtSh, where each stretch ends inside the wide array. -/
theorem wideAt_alike (k : Key) (f0 nl stride : Nat)
    (hb : ∀ l, l < nl → f0 + l * stride + len k ≤ 4 * d + 6 * JV) :
    Q (wideAtSh L k f0 nl stride) (wideAtSh L' k f0 nl stride) :=
  C.sum _ _ _ fun i hi => C.sum nl _ _ fun l hl =>
    A.entryH .wideAtKeys _ (quotientIndex_lt S2_positive hi (hb l hl))

/-- At midSh. -/
theorem mid_alike (k : Key) (v0 : Nat) (hv : v0 + len k ≤ JV) : Q (midSh L k v0) (midSh L' k v0) :=
  wideAt_alike C A k _ 2 JV fun l hl => by
    have : l = 0 ∨ l = 1 := by omega
    rcases this with rfl | rfl <;> omega

/-- At lowSh. -/
theorem low_alike (k : Key) (hv : len k ≤ JV) : Q (lowSh L k) (lowSh L' k) :=
  wideAt_alike C A k _ 1 JV fun l hl => by
    have : l = 0 := by omega
    subst this; omega

/-- At tableValueSh. -/
theorem tableValue_alike (k : Key) (v0 : Nat) (hv : v0 + len k ≤ JV) :
    Q (tableValueSh L k v0) (tableValueSh L' k v0) :=
  wideAt_alike C A k _ 3 JV fun l hl => by
    have : l = 0 ∨ l = 1 ∨ l = 2 := by omega
    rcases this with rfl | rfl | rfl <;> omega

/-- At the head's five keys. -/
theorem key_alike (hJ : JVa ≤ JV) (k : Key) : Q (keySh L k) (keySh L' k) := by
  cases k with
  | marginTop =>
    exact C.app (C.app (C.app A.lgClaimed (C.app (atCosts_alike C A _) (atCosts_alike C A _)))
      (mid_alike C A _ 0 (by simp only [len]; omega))) (low_alike C A _ (Nat.le_refl _))
  | marginMid => exact mid_alike C A _ 0 (by simp only [len]; omega)
  | marginLow => exact low_alike C A _ (Nat.le_refl _)
  | tableA =>
    exact C.app (mid_alike C A _ 0 (by simp only [len]; omega))
      (tableValue_alike C A _ 0 (by simp only [len]; omega))
  | tableB =>
    exact C.app (mid_alike C A _ JVa (by simp only [len]; omega))
      (tableValue_alike C A _ JVa (by simp only [len]; omega))

/-- At a key of the place. -/
theorem placeKey_alike (hd : S2 ∣ d) (hJ : JVa ≤ JV) (k : PlaceKey) :
    Q (placeKeySh L k) (placeKeySh L' k) := by
  cases k with
  | inl k => exact keyN_alike C A hd k
  | inr k => exact key_alike C A hJ k

/-- **The six key vectors.** -/
theorem keys_alike (hd : S2 ∣ d) (hJ : JVa ≤ JV) : List.Forall₂ Q (keysSh L) (keysSh L') :=
  forall₂_map_same _ _ callList fun keys =>
    C.cat (forall₂_map_same _ _ keys fun k => placeKey_alike C A hd hJ k)

end Walk

/-- The leaves with no read. -/
def LeafSh.bare (L : LeafSh) : LeafSh :=
  { L with entryN := fun _ _ => noTerm, wide := fun _ => noTerm, entryH := fun _ _ => noTerm }

end VerifiableInference.Desc.Kinds.Head.Shape

#print axioms VerifiableInference.Desc.Kinds.Head.Shape.KeptByAppending
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.LeavesAlike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.sumSh_succ
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.KeptByAppending.sum
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.KeptByAppending.fold
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.KeptByAppending.cat
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.KeptByAppending.dig
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.PositionRowAlike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.positionRow_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.forall₂_map_range
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.forall₂_append
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.forall₂_map_same
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.quotientIndex_lt
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.numberDigit_lt
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.S2_positive
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.limbIndex_lt
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.square_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.product_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.rows_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.normed_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.norm_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.atCosts_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.summed_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.tableCosts_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.policy_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.logit_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.forms_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.wideAtN_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.keyN_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.wideAt_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.mid_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.low_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.tableValue_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.key_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.placeKey_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.keys_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.LeafSh.bare
