-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Alg/Count.lean: counting the values of a challenge that have a property.

Every count is written `Nat.card {a : α // p a}`, a notion of Mathlib: no definition of a count is
made here, and the file mentions no protocol, field or polynomial. `Prob.cnt` (Prob/Cnt.lean)
unfolds to the same expression, so a lemma of this file proves a goal about `cnt`; Prob/Count.lean
states some of the basic rules again for `cnt`.

Notation: `α`, `β`: types, the values of a challenge (in the section `Parts`: `β j`, the type of the
part j of a message); `ι`: a type, the index of a family of claims.
Terms: lean/GLOSSARY.md.
-/
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Alg

open Finset

variable {α β ι : Type*}

/-! ## Basic rules -/

/-- The count is the cardinality of the filtered finite set, for every enumeration and every
decision procedure (the instances `Fintype α`, `DecidablePred p`). -/
theorem count_eq_card_filter [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {a : α // p a} = (univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- A weaker property has at least as many values. -/
theorem count_mono [Finite α] {p q : α → Prop} (h : ∀ a, p a → q a) :
    Nat.card {a : α // p a} ≤ Nat.card {a : α // q a} :=
  Nat.card_le_card_of_injective (fun x : {a : α // p a} => (⟨x.1, h x.1 x.2⟩ : {a : α // q a}))
    (fun _ _ hab => Subtype.ext (congrArg (fun y : {a : α // q a} => y.1) hab))

theorem count_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    Nat.card {a : α // p a} = Nat.card {a : α // q a} :=
  Nat.card_congr (Equiv.subtypeEquivRight h)

theorem count_eq_zero {p : α → Prop} (h : ∀ a, ¬ p a) : Nat.card {a : α // p a} = 0 := by
  haveI : IsEmpty {a : α // p a} := ⟨fun x => h x.1 x.2⟩
  exact Nat.card_of_isEmpty

theorem count_le_card [Fintype α] (p : α → Prop) : Nat.card {a : α // p a} ≤ Fintype.card α := by
  classical
  rw [count_eq_card_filter]
  exact card_le_univ _

theorem count_true [Fintype α] : Nat.card {_a : α // True} = Fintype.card α := by
  classical
  rw [count_eq_card_filter]
  simp

/-- Union bound. The sizes of the bad sets of two claims that one challenge checks add up. -/
theorem count_or_le [Finite α] (p q : α → Prop) :
    Nat.card {a : α // p a ∨ q a} ≤ Nat.card {a : α // p a} + Nat.card {a : α // q a} := by
  classical
  cases nonempty_fintype α
  rw [count_eq_card_filter, count_eq_card_filter, count_eq_card_filter, filter_or]
  exact card_union_le _ _

/-- Union bound over a finite family of claims that one challenge checks. -/
theorem count_exists_le [Finite α] [Fintype ι] (p : ι → α → Prop) :
    Nat.card {a : α // ∃ i, p i a} ≤ ∑ i, Nat.card {a : α // p i a} := by
  classical
  cases nonempty_fintype α
  simp only [count_eq_card_filter]
  have : (univ.filter fun a => ∃ i, p i a) = univ.biUnion fun i => univ.filter (p i) := by
    ext a; simp
  rw [this]
  exact card_biUnion_le

/-- If at most one value has the property, the count is at most 1. -/
theorem count_le_one [Finite α] {p : α → Prop} (h : ∀ a b, p a → p b → a = b) :
    Nat.card {a : α // p a} ≤ 1 := by
  classical
  cases nonempty_fintype α
  rw [count_eq_card_filter, card_le_one]
  intro a ha b hb
  simp only [mem_filter, mem_univ, true_and] at ha hb
  exact h a b ha hb

theorem count_eq_le_one [Finite α] (v : α) : Nat.card {a : α // a = v} ≤ 1 :=
  count_le_one fun _ _ ha hb => ha.trans hb.symm

/-- The count is invariant under a bijection of the challenge space. -/
theorem count_equiv (e : α ≃ β) (p : β → Prop) :
    Nat.card {a : α // p (e a)} = Nat.card {b : β // p b} :=
  Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)

/-- For a pair of challenges, the count is the sum, over the first challenge, of the counts over the
second. -/
theorem count_prod [Fintype α] [Finite β] (p : α × β → Prop) :
    Nat.card {x : α × β // p x} = ∑ a, Nat.card {b : β // p (a, b)} := by
  classical
  cases nonempty_fintype β
  simp only [count_eq_card_filter, card_filter]
  rw [← univ_product_univ, sum_product]

/-- A challenge that is computed from a raw value. The verifier samples a raw value c (for example a
string of bits) and uses coin c. If at most m raw values are mapped to any one value, a property
with k values has at most k · m raw values. -/
theorem count_comp_le [Finite α] [Finite β] (coin : α → β) (m : ℕ)
    (hm : ∀ v : β, Nat.card {c : α // coin c = v} ≤ m) (p : β → Prop) :
    Nat.card {c : α // p (coin c)} ≤ Nat.card {v : β // p v} * m := by
  classical
  cases nonempty_fintype α
  cases nonempty_fintype β
  rw [count_eq_card_filter, count_eq_card_filter]
  have himg : ((univ.filter fun c : α => p (coin c)).image coin) ⊆ univ.filter p := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hc).2⟩
  have hfib : ∀ v ∈ (univ.filter fun c : α => p (coin c)).image coin,
      ((univ.filter fun c : α => p (coin c)).filter fun c => coin c = v).card ≤ m := by
    intro v _
    refine le_trans (card_le_card ?_)
      (le_of_eq_of_le (count_eq_card_filter fun c : α => coin c = v).symm (hm v))
    intro c hc
    exact mem_filter.mpr ⟨mem_univ c, (mem_filter.mp hc).2⟩
  calc
    (univ.filter fun c : α => p (coin c)).card ≤
        m * ((univ.filter fun c : α => p (coin c)).image coin).card :=
      card_le_mul_card_image _ m hfib
    _ ≤ m * (univ.filter p).card := Nat.mul_le_mul_left m (card_le_card himg)
    _ = (univ.filter p).card * m := Nat.mul_comm _ _

/-- A property of the first of two challenges holds for as many pairs as it has values, times the
number |β| of second challenges. -/
theorem count_fst [Fintype α] [Fintype β] (p : α → Prop) :
    Nat.card {x : α × β // p x.1} = Nat.card {a : α // p a} * Fintype.card β := by
  classical
  rw [count_prod]
  have : ∀ a : α, Nat.card {_b : β // p a} = if p a then Fintype.card β else 0 := by
    intro a
    by_cases ha : p a
    · simp only [ha, if_true]; exact count_true
    · simp only [ha, if_false]; exact count_eq_zero fun _ h => h
  simp only [this]
  rw [← sum_filter, sum_const, count_eq_card_filter]
  rfl

/-- A property of the second of two challenges holds for as many pairs as it has values, times the
number |α| of first challenges. -/
theorem count_snd [Fintype α] [Fintype β] (p : β → Prop) :
    Nat.card {x : α × β // p x.2} = Fintype.card α * Nat.card {b : β // p b} := by
  rw [mul_comm, ← count_fst (β := α) p]
  exact count_equiv (Equiv.prodComm α β) (fun x : β × α => p x.1)

/-! ## Two challenges in turn -/

/-- Two challenges in turn. Suppose that at most a values of the first challenge are bad, and that
after every first challenge that is not bad, p holds for at most b values of the second. Then p
holds for at most a · |β| + |α| · b pairs. -/
theorem count_prod_le [Fintype α] [Fintype β] (p : α × β → Prop) (bad : α → Prop) (a b : ℕ)
    (hbad : Nat.card {x : α // bad x} ≤ a) (hp : ∀ x, ¬ bad x → Nat.card {y : β // p (x, y)} ≤ b) :
    Nat.card {x : α × β // p x} ≤ a * Fintype.card β + Fintype.card α * b := by
  classical
  rw [count_prod]
  have hx : ∀ x : α, Nat.card {y : β // p (x, y)} ≤ (if bad x then Fintype.card β else 0) + b := by
    intro x
    split_ifs with h
    · exact le_trans (count_le_card _) (Nat.le_add_right _ _)
    · simpa using hp x h
  calc ∑ x : α, Nat.card {y : β // p (x, y)}
      ≤ ∑ x : α, ((if bad x then Fintype.card β else 0) + b) := sum_le_sum fun x _ => hx x
    _ = Nat.card {x : α // bad x} * Fintype.card β + Fintype.card α * b := by
        rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, card_univ, count_eq_card_filter]
        simp only [smul_eq_mul]
    _ ≤ a * Fintype.card β + Fintype.card α * b := by gcongr

/-- `count_prod_le` with fractions of one denominator D: if the first challenge is bad with
probability at most a / D, and after every first challenge that is not bad p holds with probability
at most b / D, then p holds for the pair with probability at most (a + b) / D. -/
theorem count_prod_mul_le [Fintype α] [Fintype β] (p : α × β → Prop) (bad : α → Prop) (D a b : ℕ)
    (hbad : Nat.card {x : α // bad x} * D ≤ a * Fintype.card α)
    (hp : ∀ x, ¬ bad x → Nat.card {y : β // p (x, y)} * D ≤ b * Fintype.card β) :
    Nat.card {x : α × β // p x} * D ≤ (a + b) * Fintype.card (α × β) := by
  classical
  rw [count_prod, sum_mul, Fintype.card_prod]
  have hx : ∀ x : α, Nat.card {y : β // p (x, y)} * D
      ≤ (if bad x then D * Fintype.card β else 0) + b * Fintype.card β := by
    intro x
    split_ifs with h
    · have : Nat.card {y : β // p (x, y)} ≤ Fintype.card β := count_le_card _
      nlinarith
    · simpa using hp x h
  calc ∑ x : α, Nat.card {y : β // p (x, y)} * D
      ≤ ∑ x : α, ((if bad x then D * Fintype.card β else 0) + b * Fintype.card β) :=
        sum_le_sum fun x _ => hx x
    _ = Nat.card {x : α // bad x} * D * Fintype.card β + Fintype.card α * (b * Fintype.card β) := by
        rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, card_univ, count_eq_card_filter]
        simp only [smul_eq_mul]; ring
    _ ≤ a * Fintype.card α * Fintype.card β + Fintype.card α * (b * Fintype.card β) := by
        gcongr
    _ = (a + b) * (Fintype.card α * Fintype.card β) := by ring

/-! ## A challenge that is a tuple -/

/-- For q > 0: converts a bound of the form c · q ≤ s · q^n into the bound c ≤ s · q^(n - 1) on a
number of tuples. -/
theorem le_mul_pow_pred {c s q n : ℕ} (hq : 0 < q) (h : c * q ≤ s * q ^ n) :
    c ≤ s * q ^ (n - 1) := by
  cases n with
  | zero => simpa using le_trans (Nat.le_mul_of_pos_right c hq) h
  | succ k =>
    rw [pow_succ, ← mul_assoc] at h
    simpa using Nat.le_of_mul_le_mul_right h hq

/-- Converts a bound of the form c · q ≤ s · T, where q > 0 divides T, into c ≤ s · (T / q). -/
theorem le_mul_div_of_mul_le {c s T q : ℕ} (hq : 0 < q) (hd : q ∣ T) (h : c * q ≤ s * T) :
    c ≤ s * (T / q) := by
  obtain ⟨t, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left t hq]
  rw [mul_comm q t, ← mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right h hq

section Tuple

variable {J : Type*} [Fintype J] [DecidableEq J] [Fintype α]

/-- The map that replaces coordinate i of a tuple by a new value and returns the old value is a
bijection. -/
def swapAt (i : J) : ((J → α) × α) ≃ ((J → α) × α) where
  toFun x := (Function.update x.1 i x.2, x.1 i)
  invFun x := (Function.update x.1 i x.2, x.1 i)
  left_inv x := by simp
  right_inv x := by simp

/-- One free coordinate. If at most m values of coordinate i make p true, whatever the other
coordinates are, then p holds for at most the fraction m / |α| of all tuples. -/
theorem count_pi_mul_le_of_fiber (i : J) (p : (J → α) → Prop) (m : ℕ)
    (h : ∀ f : J → α, Nat.card {a : α // p (Function.update f i a)} ≤ m) :
    Nat.card {f : J → α // p f} * Fintype.card α ≤ m * Fintype.card (J → α) := by
  have e1 : Nat.card {x : (J → α) × α // p x.1} = Nat.card {f : J → α // p f} * Fintype.card α := by
    classical
    rw [count_prod]
    have : ∀ f : J → α, Nat.card {_a : α // p f} = if p f then Fintype.card α else 0 := by
      intro f
      by_cases hf : p f
      · simp only [hf, if_true]; exact count_true
      · simp only [hf, if_false]; exact count_eq_zero fun _ h => h
    simp only [this]
    rw [← sum_filter, sum_const, count_eq_card_filter]
    rfl
  have e2 : Nat.card {x : (J → α) × α // p (Function.update x.1 i x.2)} =
      Nat.card {x : (J → α) × α // p x.1} :=
    count_equiv (swapAt i) (fun x => p x.1)
  rw [← e1, ← e2, count_prod]
  calc
    ∑ f : J → α, Nat.card {a : α // p (Function.update f i a)} ≤ ∑ _f : J → α, m :=
      sum_le_sum fun f _ => h f
    _ = m * Fintype.card (J → α) := by simp [mul_comm]

/-- `count_pi_mul_le_of_fiber` as a number of tuples: at most m · |α|^(|J| - 1). -/
theorem count_pi_le_of_fiber (i : J) (p : (J → α) → Prop) (m : ℕ)
    (h : ∀ f : J → α, Nat.card {a : α // p (Function.update f i a)} ≤ m) :
    Nat.card {f : J → α // p f} ≤ m * Fintype.card α ^ (Fintype.card J - 1) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · haveI : IsEmpty (J → α) := ⟨fun f => hα.elim (f i)⟩
    rw [count_eq_zero fun f => (IsEmpty.false f).elim]
    exact Nat.zero_le _
  · have h1 := count_pi_mul_le_of_fiber i p m h
    rw [Fintype.card_fun] at h1
    exact le_mul_pow_pred Fintype.card_pos h1

/-- A message that holds several challenges. The message is bad if one of its coordinates is bad. If
at most m j values of coordinate j are bad, whatever the other coordinates are, at most (∑ j, m j) ·
|α|^(|J| - 1) messages are bad. -/
theorem count_pi_exists_le (p : J → (J → α) → Prop) (m : J → ℕ)
    (h : ∀ j f, Nat.card {a : α // p j (Function.update f j a)} ≤ m j) :
    Nat.card {f : J → α // ∃ j, p j f} ≤ (∑ j, m j) * Fintype.card α ^ (Fintype.card J - 1) := by
  refine le_trans (count_exists_le p) ?_
  rw [sum_mul]
  exact sum_le_sum fun j _ => count_pi_le_of_fiber j (p j) (m j) (h j)

omit [DecidableEq J] [Fintype α] in
/-- The number of tuples all of whose coordinates have the property A is the number of values with A
to the power |J|. -/
theorem count_forall_pow [Finite α] (A : α → Prop) :
    Nat.card {f : J → α // ∀ j, A (f j)} = Nat.card {a : α // A a} ^ Fintype.card J := by
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (β := fun _ : J => α) (p := fun _ a => A a)),
    Nat.card_fun, Nat.card_eq_fintype_card (α := J)]

end Tuple

/-! ## A message whose parts have different types -/

section Parts

variable {J : Type*} [Fintype J] [DecidableEq J] {β : J → Type*} [∀ j, Fintype (β j)]

/-- The number of messages is the number of values of one part times the number of values of the
other parts. -/
theorem card_pi_split (j0 : J) :
    Fintype.card (∀ j, β j) = Fintype.card (β j0) * Fintype.card (∀ j : {j // j ≠ j0}, β j) := by
  rw [Fintype.card_congr (Equiv.piSplitAt j0 β), Fintype.card_prod]

/-- A property of one part of a message holds for as many messages as it has values, times the
number of values of the other parts. -/
theorem count_pi_apply (j0 : J) (p : β j0 → Prop) :
    Nat.card {f : ∀ j, β j // p (f j0)} =
      Nat.card {b : β j0 // p b} * Fintype.card (∀ j : {j // j ≠ j0}, β j) := by
  rw [← count_fst p]
  exact count_equiv (Equiv.piSplitAt j0 β) (fun x => p x.1)

/-- `count_pi_apply`, with the number of values of the other parts written as a quotient. -/
theorem count_pi_apply_div (j0 : J) [Nonempty (β j0)] (p : β j0 → Prop) :
    Nat.card {f : ∀ j, β j // p (f j0)} =
      Nat.card {b : β j0 // p b} * (Fintype.card (∀ j, β j) / Fintype.card (β j0)) := by
  rw [count_pi_apply, card_pi_split j0, Nat.mul_div_cancel_left _ Fintype.card_pos]

end Parts

/-! ## Families that share a challenge -/

/-- m is the first member of the family with the property P. -/
def IsFirst {M : Type*} [LT M] (P : M → Prop) (m : M) : Prop := P m ∧ ∀ m', m' < m → ¬ P m'

theorem IsFirst.unique {M : Type*} [LinearOrder M] {P : M → Prop} {m m' : M}
    (h : IsFirst P m) (h' : IsFirst P m') : m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd h.1 (h'.2 m hlt)
  · exact heq
  · exact absurd h'.1 (h.2 m' hgt)

/-- In a finite linear order, if some member has the property P, there is a first member with it. -/
theorem exists_isFirst {M : Type*} [LinearOrder M] [Finite M] {P : M → Prop} (h : ∃ m, P m) :
    ∃ m, IsFirst P m := by
  classical
  cases nonempty_fintype M
  obtain ⟨m0, hm0⟩ := h
  have hne : (univ.filter P).Nonempty := ⟨m0, by simp [hm0]⟩
  refine ⟨(univ.filter P).min' hne, ?_, fun m' hlt hP => ?_⟩
  · exact (mem_filter.mp ((univ.filter P).min'_mem hne)).2
  · exact absurd hlt (not_lt.mpr ((univ.filter P).min'_le m' (by simp [hP])))

/-- In a finite linear order, if no member is the first with the property P, no member has it. -/
theorem forall_not_of_no_first
    {M : Type*} [LinearOrder M] [Finite M] {P : M → Prop} (h : ∀ m, ¬ IsFirst P m) (m : M) :
    ¬ P m :=
  fun hm => by
    obtain ⟨m', hm'⟩ := exists_isFirst ⟨m, hm⟩
    exact h m' hm'

/-- Families. Several objects in a fixed order share one challenge. The bad values are those of the
first member with the property P (for example, not zero). If each member with P has at most e bad
values, they are at most e. -/
theorem count_first_le {M : Type*} [LinearOrder M] [Finite α] (P : M → Prop) (bad : M → α → Prop)
    (e : ℕ) (h : ∀ m, P m → Nat.card {a : α // bad m a} ≤ e) :
    Nat.card {a : α // ∃ m, IsFirst P m ∧ bad m a} ≤ e := by
  by_cases hex : ∃ m, IsFirst P m
  · obtain ⟨m, hm⟩ := hex
    refine le_trans (count_mono fun a ha => ?_) (h m hm.1)
    obtain ⟨m', hm', hb⟩ := ha
    rwa [hm.unique hm']
  · rw [count_eq_zero fun a ha => hex ⟨ha.choose, ha.choose_spec.1⟩]
    exact Nat.zero_le _

end Alg
