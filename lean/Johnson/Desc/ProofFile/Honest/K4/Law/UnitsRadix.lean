-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/UnitsRadix.lean.

What is here. The number of an entry of a table with open groups (`stridesOf`, `strideOf`,
Johnson/Desc/K4/Honest/Units.lean) is a number of mixed radix: it lies below the number of entries,
it fixes the open groups' indices, and it is the same sum whether it is taken over the open names or
over the unit's groups.

  `numFree`   the number that a choice of indices spells
  `numFree_lt`, `numFree_inj`   below the number of entries; it fixes the indices
  `strides_names`, `strideOf_some`, `strideOf_none`   the strides' names are the open names
  `sum_one_name`, `sum_groups`   **the sum over the unit's groups is the sum over the open names**

Limits. On natural numbers and lists alone. Nothing on a weight, a factor or a matrix.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Units
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Model (WsUnit WsGrp)
open OnBytes.Desc.First.K4.Honest (stridesOf strideOf)

/-- The number of the entry that a choice spells: the sum of the open groups' strides times their
indices. -/
def numFree (st : List (String × ℕ)) (idx : String → ℕ) : ℕ := (st.map fun x => x.2 * idx x.1).sum

/-- A name's extent in a unit: that of the first group of the name; 1 if there is none. -/
def extOf (u : WsUnit) (n : String) : ℕ := ((u.g.find? fun g => g.name == n).map (·.R)).getD 1

theorem stridesOf_cons (u : WsUnit) (n : String) (free : List String) :
    stridesOf u (n :: free) =
      ((n, (stridesOf u free).2) :: (stridesOf u free).1, (stridesOf u free).2 * extOf u n) := rfl

/-- The number lies below the number of entries. -/
theorem numFree_lt (u : WsUnit) (idx : String → ℕ) : ∀ free : List String,
    (∀ n ∈ free, idx n < extOf u n) → numFree (stridesOf u free).1 idx < (stridesOf u free).2
  | [], _ => Nat.one_pos
  | n :: free, h => by
    have ih := numFree_lt u idx free fun m hm => h m (List.mem_cons_of_mem _ hm)
    have hn := h n List.mem_cons_self
    rw [stridesOf_cons]
    show ((stridesOf u free).2 * idx n + numFree (stridesOf u free).1 idx) < _
    calc (stridesOf u free).2 * idx n + numFree (stridesOf u free).1 idx
        < (stridesOf u free).2 * idx n + (stridesOf u free).2 := Nat.add_lt_add_left ih _
      _ = (stridesOf u free).2 * (idx n + 1) := by ring
      _ ≤ (stridesOf u free).2 * extOf u n := Nat.mul_le_mul_left _ hn

/-- **The number fixes the indices.** -/
theorem numFree_inj (u : WsUnit) (a b : String → ℕ) : ∀ free : List String,
    (∀ n ∈ free, a n < extOf u n) → (∀ n ∈ free, b n < extOf u n) →
    numFree (stridesOf u free).1 a = numFree (stridesOf u free).1 b → ∀ n ∈ free, a n = b n
  | [], _, _, _ => fun _ hn => absurd hn List.not_mem_nil
  | m :: free, ha, hb, h => by
    have la := numFree_lt u a free fun k hk => ha k (List.mem_cons_of_mem _ hk)
    have lb := numFree_lt u b free fun k hk => hb k (List.mem_cons_of_mem _ hk)
    rw [stridesOf_cons] at h
    have h' : (stridesOf u free).2 * a m + numFree (stridesOf u free).1 a =
        (stridesOf u free).2 * b m + numFree (stridesOf u free).1 b := h
    have hS : 0 < (stridesOf u free).2 := by omega
    have e1 : a m = b m := by
      have d1 := congrArg (· / (stridesOf u free).2) h'
      simp only [Nat.mul_add_div hS, Nat.div_eq_of_lt la, Nat.div_eq_of_lt lb, Nat.add_zero] at d1
      exact d1
    have e2 : numFree (stridesOf u free).1 a = numFree (stridesOf u free).1 b := by
      rw [e1] at h'
      omega
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn'
    · exact e1
    · exact numFree_inj u a b free (fun k hk => ha k (List.mem_cons_of_mem _ hk))
        (fun k hk => hb k (List.mem_cons_of_mem _ hk)) e2 n hn'

/-- The strides' names are the open names, in their order. -/
theorem strides_names (u : WsUnit) : ∀ free : List String,
    (stridesOf u free).1.map (·.1) = free
  | [] => rfl
  | n :: free => by
    rw [stridesOf_cons, List.map_cons, strides_names u free]

/-- A group whose name stands among the strides' has a stride. -/
theorem strideOf_some (g : WsGrp) : ∀ st : List (String × ℕ), g.name ∈ st.map (·.1) →
    ∃ s, strideOf st g = some s
  | [], h => absurd h List.not_mem_nil
  | x :: st, h => by
    unfold strideOf
    rw [List.find?_cons]
    by_cases hx : (x.1 == g.name) = true
    · rw [hx]
      exact ⟨x.2, rfl⟩
    · have hx' : (x.1 == g.name) = false := by simpa using hx
      rw [hx']
      rcases List.mem_cons.mp h with e | h'
      · exact absurd (by rw [e]; exact beq_self_eq_true _) hx
      · exact strideOf_some g st h'

/-- Another has none. -/
theorem strideOf_none (g : WsGrp) : ∀ st : List (String × ℕ), g.name ∉ st.map (·.1) →
    strideOf st g = none
  | [], _ => rfl
  | x :: st, h => by
    have h1 : x.1 ≠ g.name := fun e => h (by rw [List.map_cons, e]; exact List.mem_cons_self)
    have h2 : g.name ∉ st.map (·.1) := fun k => h (List.mem_cons_of_mem _ k)
    have ih := strideOf_none g st h2
    unfold strideOf at ih ⊢
    rw [List.find?_cons, show (x.1 == g.name) = false by simpa using h1]
    exact ih

/-- Where just one group has the name n: a sum over the groups that counts c at that name. -/
theorem sum_one_name (n : String) (c : ℕ) : ∀ G : List WsGrp, (G.map (·.name)).Nodup →
    n ∈ G.map (·.name) → (G.map fun g => if g.name = n then c else 0).sum = c
  | [], _, h => absurd h List.not_mem_nil
  | g :: G, hd, h => by
    rw [List.map_cons, List.nodup_cons] at hd
    rw [List.map_cons, List.sum_cons]
    by_cases hg : g.name = n
    · have hz : (G.map fun g' => if g'.name = n then c else 0).sum = 0 := by
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hx
        rw [if_neg fun e => hd.1 (by rw [hg, ← e]; exact List.mem_map_of_mem hg')]
      rw [if_pos hg, hz, Nat.add_zero]
    · rw [if_neg hg, Nat.zero_add]
      rcases List.mem_cons.mp h with e | h'
      · exact absurd e.symm hg
      · exact sum_one_name n c G hd.2 h'

/-- **The sum over a unit's groups, each open one with its stride, is the sum over the strides.** A:
a number for each name. No two groups have one name; no name stands twice among the strides'; each
is a group's. -/
theorem sum_groups (G : List WsGrp) (hG : (G.map (·.name)).Nodup) (A : String → ℕ) :
    ∀ st : List (String × ℕ), (st.map (·.1)).Nodup → (∀ x ∈ st, x.1 ∈ G.map (·.name)) →
    (G.map fun g => match strideOf st g with
      | none => 0
      | some s => s * A g.name).sum = numFree st A
  | [], _, _ => by
    show (G.map fun _ => 0).sum = 0
    exact List.sum_eq_zero fun x hx => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
      rfl
  | x :: st, hd, hin => by
    rw [List.map_cons, List.nodup_cons] at hd
    have ih := sum_groups G hG A st hd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have e : ∀ g ∈ G, (match strideOf (x :: st) g with
        | none => 0
        | some s => s * A g.name) =
        (if g.name = x.1 then x.2 * A x.1 else 0) + match strideOf st g with
          | none => 0
          | some s => s * A g.name := by
      intro g _
      by_cases hg : g.name = x.1
      · have h1 : strideOf (x :: st) g = some x.2 := by
          unfold strideOf
          rw [List.find?_cons, show (x.1 == g.name) = true by rw [hg]; exact beq_self_eq_true _]
          rfl
        have h2 : strideOf st g = none := strideOf_none g st (by rw [hg]; exact hd.1)
        rw [h1, h2, if_pos hg, hg]
        rfl
      · have h1 : strideOf (x :: st) g = strideOf st g := by
          unfold strideOf
          rw [List.find?_cons, show (x.1 == g.name) = false by
            simpa using fun e : x.1 = g.name => hg e.symm]
        rw [h1, if_neg hg, Nat.zero_add]
    rw [List.map_congr_left e, List.sum_map_add, ih,
      sum_one_name x.1 _ G hG (hin x List.mem_cons_self)]
    rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.stridesOf_cons
#print axioms ProofFile.Honest.K4.numFree_lt
#print axioms ProofFile.Honest.K4.numFree_inj
#print axioms ProofFile.Honest.K4.strides_names
#print axioms ProofFile.Honest.K4.strideOf_some
#print axioms ProofFile.Honest.K4.strideOf_none
#print axioms ProofFile.Honest.K4.sum_one_name
#print axioms ProofFile.Honest.K4.sum_groups
