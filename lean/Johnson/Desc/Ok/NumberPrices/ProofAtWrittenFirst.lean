-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/ProofAtWrittenFirst.lean: one more negative test of the closed fact on
the proof file's prices (Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean): with the price of a
round "RNG" of the first chain raised by one part in 1024 (`fineProof`,
Johnson/Desc/Ok/NumberPrices/ProofAtWrittenTeeth.lean), the half of the statement on `PricedAt` is
itself false. That price is the bound itself, so any increase is above it.

The first list of a file's data lacks the chain's last round, and `PricedRounds` holds it against
the plan's rounds of the chain without the last. So the test needs that the changed round is not the
last.

`expand_append`, `exists_mem_dropLast_expand` are tools on lists that are written as runs
(Johnson/G/Runs.lean). `not_proofPriced_of_first` is a tool at the written lists.
`not_proofPriced_fine` is the negative test.

By evaluations in Lean's kernel (`decide +kernel`): the two premises inside `not_proofPriced_fine`.

What of OnBytes/Model/ is used: nothing by name.

Limits. One changed value, at one distinct round of the written plan. Nothing on soundness.

-/
import Johnson.Desc.Ok.NumberPrices.ProofAtWrittenTeeth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open OnBytes.Params OnBytes.Flat OnBytes.Flat.Held OnBytes.Maker
open Johnson.G Johnson.G.Runs

theorem expand_append {α : Type} (A B : List (Nat × α)) :
    expand (A ++ B) = expand A ++ expand B := by
  induction A with
  | nil => rfl
  | cons x xs ih =>
    show List.replicate x.1 x.2 ++ expand (xs ++ B) =
      List.replicate x.1 x.2 ++ expand xs ++ expand B
    rw [ih, List.append_assoc]

/-- A value with q in a run that is not the last, where neither run is of 0 members, is a member of
the list without its last member. -/
theorem exists_mem_dropLast_expand {α : Type} {q : α → Bool} {l : List (Nat × α)}
    (h1 : l.dropLast.any (fun x => x.1 != 0 && q x.2) = true)
    (h2 : (l.getLast?).any (fun x => x.1 != 0) = true) :
    ∃ v ∈ (expand l).dropLast, q v = true := by
  obtain ⟨x, hx, hq⟩ := List.any_eq_true.1 h1
  have c := Bool.and_eq_true_iff.1 hq
  have x0 : x.1 ≠ 0 := by simpa using c.1
  cases hl : l.getLast? with
  | none => simp [hl] at h2
  | some y =>
    have y0 : y.1 ≠ 0 := by simpa [hl] using h2
    have e : l.dropLast ++ [y] = l := List.dropLast_append_getLast? y hl
    have ne : expand [y] ≠ [] := by
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero y0
      show List.replicate y.1 y.2 ++ [] ≠ []
      rw [hn]
      simp [List.replicate_succ]
    have hm : x.2 ∈ expand l.dropLast := by
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero x0
      refine mem_expand_of (n := n) ?_
      have ex : ((n + 1, x.2) : Nat × α) = x := by
        rw [← Nat.succ_eq_add_one, ← hn]
      rw [ex]
      exact hx
    refine ⟨x.2, ?_, c.2⟩
    rw [← e, expand_append, List.dropLast_append_of_ne_nil ne]
    exact List.mem_append_left _ hm

/-- A plan of the first chain with a round above the bound that is not the last: the half on
`PricedAt` is false. -/
theorem not_proofPriced_of_first {T : Three}
    (h : ∃ r ∈ (chainRounds T.A.plan).dropLast, aboveB 20 r = true) : ¬ ProofPricedAt T := by
  intro H
  have H1 : List.Forall₂ Number.PricedAt writtenPFull.ds₁ (chainRounds T.A.plan).dropLast := H.1
  obtain ⟨r, hr, hb⟩ := h
  obtain ⟨d, _, P⟩ := f2_right H1 r hr
  exact not_pricedAt_of_above (above_of_test hb) P

set_option maxRecDepth 1000000 in
/-- **With the price of a round "RNG" raised by one part in 1024 the half on `PricedAt` is
false.** -/
theorem not_proofPriced_fine : ¬ ProofPricedAt fineProof := by
  refine not_proofPriced_of_first ?_
  have e : chainRounds fineProof.A.plan =
      expand (chainRuns (scaleAt 31 finer pricedProofRecsFull0) pricedProofRunsFull0) :=
    chainRounds_of_runs pricedProofSetFull (scaleAt 31 finer pricedProofRecsFull0)
      pricedProofRunsFull0
  rw [e]
  exact exists_mem_dropLast_expand (by decide +kernel) (by decide +kernel)

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.expand_append
#print axioms VerifiableInference.Number.ByRuns.exists_mem_dropLast_expand
#print axioms VerifiableInference.Number.ByRuns.not_proofPriced_of_first
#print axioms VerifiableInference.Number.ByRuns.not_proofPriced_fine
