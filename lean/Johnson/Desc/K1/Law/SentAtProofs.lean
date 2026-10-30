-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SentAtProofs.lean: the proofs of the three statements of
Johnson/Desc/K1/Law/SentAt.lean, for the kind K1's law (k01_law).

  `sum_range_add`, `sum_range_ite`, `sum_cnt`: sums over the first numbers; the trees below T hold
    all n messages where each message lies in a tree below T.
  `declaredCounts : DeclaredCounts`: row N3's part.
  `mem_tenantsOf`: who is a member of `tenantsOf`. `declaredSeats : DeclaredSeats`.
  `laterSeatsOfTold : LaterSeatsOfTold`: row N4.

Limits. Plain data: the numbers N and what the blocks tell stay letters; that `bookFit` or `sentAtB`
says yes at the plan's numbers is shown by nothing here: `sentAtB` has run at no plan.

(Where this and lean/THEOREM.md differ, the page holds.) K01_law is
not proved by this. Nothing on soundness.
-/
import Johnson.Desc.K1.Law.SentAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open VerifiableInference.Desc.Book (cnt)
open VerifiableInference.Desc.First (Numbers bookFit bookFit_at treesTold tenantsOf sameMembers)

/-! ## Sums over the first numbers -/

theorem sum_range_add (a b : Nat → Nat) : ∀ T : Nat,
    ((List.range T).map fun τ => a τ + b τ).sum =
      ((List.range T).map a).sum + ((List.range T).map b).sum
  | 0 => rfl
  | T + 1 => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil]
    rw [sum_range_add a b T]
    omega

theorem sum_range_ite (c : Nat) : ∀ T : Nat,
    ((List.range T).map fun τ => if c = τ then 1 else 0).sum = if c < T then 1 else 0
  | 0 => by simp
  | T + 1 => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil]
    rw [sum_range_ite c T]
    by_cases h1 : c < T
    · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]
      omega
    · by_cases h2 : c = T
      · rw [if_neg h1, if_pos h2, if_pos (by omega)]
        omega
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]
        omega

/-- Where each of the first n messages lies in a tree below T, the trees below T hold n messages. -/
theorem sum_cnt (tree : Array Nat) (T : Nat) : ∀ n : Nat, (∀ i, i < n → tree.getD i 0 < T) →
    ((List.range T).map fun τ => cnt tree τ n).sum = n
  | 0, _ => by
    show ((List.range T).map fun _ => 0).sum = 0
    simp
  | n + 1, h => by
    show ((List.range T).map fun τ =>
      cnt tree τ n + (if tree.getD n 0 = τ then 1 else 0)).sum = n + 1
    rw [sum_range_add, sum_cnt tree T n (fun i hi => h i (Nat.lt_succ_of_lt hi)), sum_range_ite,
      if_pos (h n (Nat.lt_succ_self n))]

/-! ## The declared list -/

/-- **A declared list that is the layout has n tenants in all.** -/
theorem declaredCounts : DeclaredCounts := by
  intro decl lay n ten D
  have e : (decl.map fun o => o.tenants.length) =
      (List.range decl.length).map fun τ => cnt lay.tree τ n := by
    refine List.ext_getElem? fun τ => ?_
    rw [List.getElem?_map, List.getElem?_map]
    by_cases hτ : τ < decl.length
    · rw [List.getElem?_eq_getElem hτ, List.getElem?_range hτ]
      exact congrArg some (D.shape τ _ (List.getElem?_eq_getElem hτ)).2.2
    · have e1 : decl[τ]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hτ)
      have e2 : (List.range decl.length)[τ]? = none :=
        List.getElem?_eq_none (by rw [List.length_range]; exact Nat.le_of_not_lt hτ)
      simp only [e1, e2, Option.map_none]
  rw [e]
  refine sum_cnt lay.tree decl.length n fun i hi => ?_
  obtain ⟨O, hO, _⟩ := D.tenant i hi
  exact (List.getElem?_eq_some_iff.1 hO).1

/-- Who is a member of `tenantsOf`. -/
theorem mem_tenantsOf (os : List Oracle) (b : Bool) (x : Nat × Nat) :
    x ∈ tenantsOf os b ↔
      ∃ O T, os[x.1]? = some O ∧ O.tenants[x.2]? = some T ∧ T.sampled = b := by
  obtain ⟨τ, t⟩ := x
  unfold tenantsOf
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Prod.exists, Prod.mk.injEq,
    List.mem_zipIdx_iff_getElem?, beq_iff_eq]
  constructor
  · rintro ⟨O, τ', hO, T, t', ⟨hT, hs⟩, rfl, rfl⟩
    exact ⟨O, T, hO, hT, hs⟩
  · rintro ⟨O, T, hO, hT, hs⟩
    exact ⟨O, τ, hO, T, t, ⟨hT, hs⟩, rfl, rfl⟩

/-- **Where every message has a sample, the declared list's sampled tenants are just the layout's
seats.** -/
theorem declaredSeats : DeclaredSeats := by
  intro decl lay n ten D hs
  refine (sameMembers_iff _ _).2 fun x => ?_
  rw [mem_tenantsOf, List.mem_map]
  constructor
  · rintro ⟨O, T, hO, hT, _⟩
    obtain ⟨i, hi, e1, e2⟩ := D.back x.1 O x.2 hO (List.getElem?_eq_some_iff.1 hT).1
    exact ⟨i, List.mem_range.2 hi, by rw [e1, e2]⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨O, hO, hT⟩ := D.tenant i (List.mem_range.1 hi)
    exact ⟨O, ten i, hO, hT, hs i (List.mem_range.1 hi)⟩

/-! ## Row N4 -/

/-- **Row N4.** -/
theorem laterSeatsOfTold : LaterSeatsOfTold := by
  intro N ps told k m t P decl hf hk ht D hs hB
  unfold laterSeatsB
  unfold sentAtB at hB
  rw [ht] at hB
  rw [(bookFit_at N ps told hf k hk).1]
  have hS := (sameMembers_iff _ _).1 (declaredSeats decl (layOf P) P.sent.size (tenantOf P) D hs)
  have hB' := (sameMembers_iff _ _).1 hB
  refine (sameMembers_iff _ _).2 fun x => ?_
  rw [← hB' x, List.mem_map, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, (hS _).2 (List.mem_map.2 ⟨i, hi, rfl⟩), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ((hS y).1 hy)
    exact ⟨i, hi, rfl⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.sum_range_add
#print axioms VerifiableInference.Desc.K1.sum_range_ite
#print axioms VerifiableInference.Desc.K1.sum_cnt
#print axioms VerifiableInference.Desc.K1.declaredCounts
#print axioms VerifiableInference.Desc.K1.mem_tenantsOf
#print axioms VerifiableInference.Desc.K1.declaredSeats
#print axioms VerifiableInference.Desc.K1.laterSeatsOfTold
