-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/OracleNoNew.lean: behind a sending of kind K1 the book's reader `oracleNo`
(Johnson/Desc/SmpRows.lean) finds each new message at its seat: the tenant (the trees in front + the
place's tree number i, its part) is message number n + i. `Booked` and `layOf` are those of
Johnson/Desc/K1/Law/BookAtRecord.lean.

Main names: `find?_range_eq_some`; `OracleNoNew` (the statement, as a definition); `oracleNoNew`
(its proof).

What is not claimed. That the book in front names only trees that it holds, or that the place's
seats part, is not shown here: both are premises. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.SmpRows
import Johnson.Desc.K1.Law.BookAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1

/-- The first number below N at which a test says yes. -/
theorem find?_range_eq_some (N k : Nat) (p : Nat → Bool) (hk : k < N) (hp : p k = true)
    (hlt : ∀ a, a < k → p a = false) : (List.range N).find? p = some k := by
  obtain ⟨m, rfl⟩ : ∃ m, N = k + (m + 1) := ⟨N - k - 1, by omega⟩
  have h1 : (List.range k).find? p = none :=
    List.find?_eq_none.2 fun a ha => by simp [hlt a (List.mem_range.1 ha)]
  rw [List.range_add, List.find?_append, h1, List.range_succ_eq_map]
  simp [hp]

/-- bk, n: the book and the number of messages in front; bk', n': behind. The third premise: every
place of the book in front names a tree that the book holds. The fourth: the place's seats part. -/
def OracleNoNew : Prop :=
  ∀ (P : Par) (bk bk' : OnBytes.TreeBook) (n n' : Nat), Booked P bk n bk' n' → bk.place.size = n →
    (∀ (o : Nat) (x : Nat × Nat), bk.place[o]? = some x → x.1 < bk.trees.size) →
    (∀ i i' : Nat, i < P.sent.size → i' < i →
      ((layOf P).tree.getD i' 0, (layOf P).part.getD i' 0) ≠
        ((layOf P).tree.getD i 0, (layOf P).part.getD i 0)) →
    ∀ i : Nat, i < P.sent.size →
      oracleNo bk' (bk.trees.size + (layOf P).tree.getD i 0) ((layOf P).part.getD i 0) =
        some (n + i)

/-- **Behind a sending the book's reader finds each new message at its seat.** -/
theorem oracleNoNew : OracleNoNew := by
  intro P bk bk' n n' hB hn hold hpart i hi
  unfold oracleNo
  refine find?_range_eq_some _ _ _ ?_ ?_ ?_
  · rw [hB.full hn, hB.msgs]
    omega
  · show (bk'.place[n + i]? == _) = true
    rw [hB.newer hn hi]
    exact beq_self_eq_true _
  · intro a ha
    show (bk'.place[a]? == _) = false
    refine beq_eq_false_iff_ne.2 fun e => ?_
    by_cases han : a < n
    · have hs : a < bk.place.size := by omega
      rw [hB.older hs] at e
      have := hold a _ e
      simp only at this
      omega
    · obtain ⟨i', rfl⟩ : ∃ i', a = n + i' := ⟨a - n, by omega⟩
      have hi' : i' < i := by omega
      rw [hB.newer hn (by omega)] at e
      have e' := Option.some.inj e
      refine hpart i i' hi hi' ?_
      have e1 := congrArg Prod.fst e'
      have e2 := congrArg Prod.snd e'
      simp only at e1 e2
      exact Prod.ext (by simp only; omega) e2

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.oracleNoNew
