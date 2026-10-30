-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheFallsPrice.lean: THE SUM OF PRICES MEMBER BY MEMBER LIES WITHIN THE ROOM. The law that bounds
the falls' measure ends in a sum over the members of the first chain (priceAt,
Honest/Law/CoverSum.lean): at each member the marks at its place, and, at a member with a round, the
falls of its group. This file bounds that sum from the records' tests. Each mark is counted once, by
the members' places being apart. Each fall is counted once, by the groups being apart.

  sum_range_get          a sum over numbers is a sum over the list
  filter_lengths_le      over places apart, the marks at each place are no more than the marks
  group_eq, once_bound   a group is its member and the members without a round behind it; over the
                         members with a round, the falls of their groups are no more than the falls
  price_sum_le           the sum is at most the count of records times tiny
  price_le_room          at 87 falls and 164 marks it lies within the room

Limits. The prices are letters here, asked to be small. This file proves nothing about completeness,
soundness or zero knowledge.
-/
import E2E.TheFallsSum
import Johnson.Desc.ProofFile.Honest.Law.CoverSum
import Johnson.Desc.ProofFile.Honest.Law.CoverReps

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.TheFalls
open ProofFile.Honest
open VerifiableInference.Desc (Block Place)

variable {S Cl : Type}

/-- A sum over the numbers of a list is a sum over the list. -/
theorem sum_range_get {α : Type} (f : α → ℝ≥0∞) (l : List α) :
    ((List.range l.length).map fun n =>
      match l[n]? with
      | some b => f b
      | none => 0).sum = (l.map f).sum := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
      List.sum_append, List.map_append, List.sum_append]
    congr 1
    · rw [← ih]
      congr 1
      refine List.map_congr_left fun n hn => ?_
      rw [List.getElem?_append_left (List.mem_range.1 hn)]
    · simp

/-- Over places apart, the marks at each place are no more than the marks. -/
theorem filter_lengths_le : ∀ (ps : List Place) (hm : List Mark), ps.Nodup →
    ((ps.map fun p => (hm.filter fun m => m.place == p).length).sum) ≤ hm.length
  | [], _, _ => by simp
  | p :: t, hm, hn => by
    obtain ⟨hp, ht⟩ := List.nodup_cons.1 hn
    have ih := filter_lengths_le t (hm.filter fun m => !(m.place == p)) ht
    have e : (t.map fun q => (hm.filter fun m => m.place == q).length) =
        t.map fun q => ((hm.filter fun m => !(m.place == p)).filter
          fun m => m.place == q).length := by
      refine List.map_congr_left fun q hq => ?_
      rw [List.filter_filter]
      refine congrArg List.length (List.filter_congr fun m _ => ?_)
      by_cases h : m.place = q
      · have hq' : q ≠ p := fun e' => hp (e' ▸ hq)
        subst h
        simp [hq']
      · simp [h]
    have s : (hm.filter fun m => m.place == p).length +
        (hm.filter fun m => !(m.place == p)).length = hm.length :=
      (List.length_eq_length_filter_add _).symm
    rw [List.map_cons, List.sum_cons, e]
    omega

/-- Two tests that never both speak, and a third that speaks where either does. -/
theorem filter_add_le {α : Type} (p q r : α → Bool) (h : ∀ x, p x = true → q x = false)
    (hr : ∀ x, p x = true ∨ q x = true → r x = true) : ∀ fs : List α,
    (fs.filter p).length + (fs.filter q).length ≤ (fs.filter r).length
  | [] => by simp
  | x :: t => by
    have ih := filter_add_le p q r h hr t
    by_cases hp : p x = true
    · have hq := h x hp
      have hx := hr x (Or.inl hp)
      simp [List.filter_cons, hp, hq, hx]
      omega
    · by_cases hq : q x = true
      · have hx := hr x (Or.inr hq)
        simp [List.filter_cons, hp, hq, hx]
        omega
      · by_cases hx : r x = true
        · simp [List.filter_cons, hp, hq, hx]
          omega
        · simp [List.filter_cons, hp, hq, hx]
          omega

/-- **A group is its member and the members without a round behind it.** -/
theorem group_eq {all A t : List (Block S Cl)} {b : Block S Cl} (e : all = A ++ b :: t)
    (hnd : (all.map (·.place)).Nodup) :
    groupPlaces all b.place =
      b.place :: (t.takeWhile fun d => d.rounds.isEmpty).map (·.place) := by
  have hA : ∀ a ∈ A, a.place ≠ b.place := by
    intro a ha he
    rw [e, List.map_append] at hnd
    exact List.disjoint_of_nodup_append hnd (List.mem_map.2 ⟨a, ha, rfl⟩)
      (List.mem_map.2 ⟨b, List.mem_cons_self, he.symm⟩)
  unfold groupPlaces
  rw [e, dropWhile_at hA rfl]
  rfl

/-- A member's count of falls. -/
def cntAt (all : List (Block S Cl)) (fs : List (Fall S)) (b : Block S Cl) : ℕ :=
  if b.rounds.isEmpty then 0 else (repsAt all fs b).length

/-- **Over the members with a round, the falls of their groups are no more than the falls at places
from the first such member on.** -/
theorem once_bound (all : List (Block S Cl)) (fs : List (Fall S))
    (hnd : (all.map (·.place)).Nodup) : ∀ (l A : List (Block S Cl)), all = A ++ l →
    (l.map (cntAt all fs)).sum ≤
      (fs.filter fun f => decide (f.place ∈
        (l.dropWhile fun d => d.rounds.isEmpty).map (·.place))).length
  | [], _, _ => by simp
  | b :: t, A, e => by
    have ih := once_bound all fs hnd t (A ++ [b]) (by rw [e]; simp)
    rw [List.map_cons, List.sum_cons]
    by_cases hb : b.rounds.isEmpty = true
    · have c0 : cntAt all fs b = 0 := by simp [cntAt, hb]
      have d0 : ((b :: t).dropWhile fun d => d.rounds.isEmpty) =
          t.dropWhile fun d => d.rounds.isEmpty := by simp [List.dropWhile_cons, hb]
      rw [c0, Nat.zero_add, d0]
      exact ih
    · have d0 : ((b :: t).dropWhile fun d => d.rounds.isEmpty) = b :: t := by
        simp [List.dropWhile_cons, hb]
      have c0 : cntAt all fs b = (fs.filter fun f => decide (f.place ∈
          b.place :: (t.takeWhile fun d => d.rounds.isEmpty).map (·.place))).length := by
        unfold cntAt repsAt
        rw [if_neg hb, group_eq e hnd]
      have hbt : ((b :: t).map (·.place)).Nodup := by
        have h := hnd
        rw [e, List.map_append] at h
        exact List.Nodup.of_append_right h
      have sp : (b :: t).map (·.place) =
          (b.place :: (t.takeWhile fun d => d.rounds.isEmpty).map (·.place)) ++
            (t.dropWhile fun d => d.rounds.isEmpty).map (·.place) := by
        have h := List.takeWhile_append_dropWhile (p := fun d : Block S Cl => d.rounds.isEmpty) (l := t)
        rw [List.cons_append, ← List.map_append, h]
        rfl
      have dj := List.disjoint_of_nodup_append (sp ▸ hbt)
      rw [c0, d0]
      refine le_trans (Nat.add_le_add_left ih _) (filter_add_le _ _ _ ?_ ?_ fs)
      · intro f hf
        have h1 := of_decide_eq_true hf
        exact decide_eq_false fun h2 => dj h1 h2
      · intro f hf
        refine decide_eq_true ?_
        rw [sp]
        rcases hf with hf | hf
        · exact List.mem_append_left _ (of_decide_eq_true hf)
        · exact List.mem_append_right _ (of_decide_eq_true hf)

/-- The falls at places of a list are no more than the falls. -/
theorem filter_length_le {α : Type} (p : α → Bool) (l : List α) : (l.filter p).length ≤ l.length :=
  List.length_filter_le _ _

/-- **The sum of prices, from small prices.** -/
theorem price_sum_le (all pre : List (Block S Cl)) (rest : List (Block S Cl)) (cut : all = pre ++ rest)
    (hm : List Mark) (qM : Block S Cl → Mark → ℝ≥0∞) (fs : List (Fall S))
    (qF : Block S Cl → Fall S → ℝ≥0∞) (hall : (all.map (·.place)).Nodup)
    (hM : ∀ b mk, mk ∈ hm → qM b mk ≤ tiny) (hF : ∀ b g, g ∈ fs → qF b g ≤ tiny) :
    ((List.range pre.length).map (priceAt pre hm qM (repsAt all fs) qF)).sum ≤
      (hm.length : ℝ≥0∞) * tiny + (fs.length : ℝ≥0∞) * tiny := by
  have e : ((List.range pre.length).map (priceAt pre hm qM (repsAt all fs) qF)).sum =
      (pre.map fun b => ((hm.filter fun m => m.place == b.place).map (qM b)).sum +
        (if b.rounds.isEmpty then 0 else ((repsAt all fs b).map (qF b)).sum)).sum := by
    rw [← sum_range_get (fun b => ((hm.filter fun m => m.place == b.place).map (qM b)).sum +
      (if b.rounds.isEmpty then 0 else ((repsAt all fs b).map (qF b)).sum)) pre]
    congr 1
    refine List.map_congr_left fun n _ => ?_
    unfold priceAt
    cases pre[n]? <;> first | rfl | simp
  rw [e]
  have one : ∀ b : Block S Cl, ((hm.filter fun m => m.place == b.place).map (qM b)).sum +
      (if b.rounds.isEmpty then 0 else ((repsAt all fs b).map (qF b)).sum) ≤
      (((hm.filter fun m => m.place == b.place).length : ℕ) : ℝ≥0∞) * tiny +
        ((cntAt all fs b : ℕ) : ℝ≥0∞) * tiny := by
    intro b
    refine add_le_add (sum_map_le _ _ _ fun m hm' => hM b m (List.mem_of_mem_filter hm')) ?_
    unfold cntAt
    split
    · simp
    · exact sum_map_le _ _ _ fun g hg => hF b g (List.mem_of_mem_filter hg)
  have two : ∀ l : List (Block S Cl), (l.map fun b =>
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum +
        (if b.rounds.isEmpty then 0 else ((repsAt all fs b).map (qF b)).sum)).sum ≤
      (((l.map fun b => (hm.filter fun m => m.place == b.place).length).sum : ℕ) : ℝ≥0∞) * tiny +
        (((l.map (cntAt all fs)).sum : ℕ) : ℝ≥0∞) * tiny := by
    intro l
    induction l with
    | nil => simp
    | cons b t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons,
        List.sum_cons]
      refine le_trans (add_le_add (one b) ih) (le_of_eq ?_)
      push_cast
      ring
  have hpre : (pre.map (·.place)).Nodup := by
    have h := hall
    rw [cut, List.map_append] at h
    exact List.Nodup.of_append_left h
  have m₁ := filter_lengths_le (pre.map (·.place)) hm hpre
  rw [List.map_map] at m₁
  have m₂ : (pre.map (cntAt all fs)).sum ≤ fs.length := by
    have h := once_bound all fs hall (pre ++ rest) [] (by simpa using cut)
    rw [List.map_append, List.sum_append] at h
    exact le_trans (Nat.le_add_right _ _) (le_trans h (List.length_filter_le _ _))
  refine le_trans (two pre) (add_le_add (mul_le_mul_right' ?_ _) (mul_le_mul_right' ?_ _))
  · exact_mod_cast m₁
  · exact_mod_cast m₂

/-- **At 87 falls and 164 marks the sum lies within the room.** -/
theorem price_le_room (all pre rest : List (Block S Cl)) (cut : all = pre ++ rest) (hm : List Mark)
    (qM : Block S Cl → Mark → ℝ≥0∞) (fs : List (Fall S)) (qF : Block S Cl → Fall S → ℝ≥0∞)
    (hall : (all.map (·.place)).Nodup) (h164 : hm.length ≤ 164) (h87 : fs.length ≤ 87)
    (hM : ∀ b mk, mk ∈ hm → qM b mk ≤ tiny) (hF : ∀ b g, g ∈ fs → qF b g ≤ tiny) :
    ((List.range pre.length).map (priceAt pre hm qM (repsAt all fs) qF)).sum ≤
      AtPublicFiles.AtFiles.HonestTerm.fallsRoom := by
  refine le_trans (price_sum_le all pre rest cut hm qM fs qF hall hM hF) ?_
  calc (hm.length : ℝ≥0∞) * tiny + (fs.length : ℝ≥0∞) * tiny
      = ((hm.length + fs.length : ℕ) : ℝ≥0∞) * tiny := by
        push_cast
        ring
    _ ≤ AtPublicFiles.AtFiles.HonestTerm.fallsRoom := room_of_count (by omega)

end AtPublicFiles.TheFalls

#print axioms AtPublicFiles.TheFalls.sum_range_get
#print axioms AtPublicFiles.TheFalls.filter_lengths_le
#print axioms AtPublicFiles.TheFalls.once_bound
#print axioms AtPublicFiles.TheFalls.price_sum_le
#print axioms AtPublicFiles.TheFalls.price_le_room
