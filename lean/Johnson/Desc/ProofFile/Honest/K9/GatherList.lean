-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GatherList.lean: WHEN THE GATHERER RETURNS, WITH THE CLAIMS MADE SO FAR IN THE
FAMILY. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

`gather_returns` (Honest/K9/GatherYes.lean) carries a family I i n u on the place, the NUMBER of claims made so far
and the state. What the batching asks of the gatherer's list (each claim fits the arrays; at most the plan's number)
is said of the CLAIMS: so here the family bears the list itself.
  `fold_returns_list`, **`gather_returns_list`**   J i cs u ("in front of entry number i of the order, with the claims
      cs made so far, the state u is as it should be") holds at (0, [], the gatherer's state); at each entry i, from J
      i cs u: the named run returns at cs.length and u, K9's test behind it says yes, and J (i + 1) (cs ++ the run's
      list) holds behind: THEN THE GATHERER RETURNS y, AND J order.length y.1 y.2
  `gather_returns_of_list`   `gather_returns` is the case in which J reads of the list its length alone
A predicate Q carried up to an entry i₀ (`gather_returns_with`, Honest/K9/GatherLeaves.lean) needs no list form of its
own: J can bear "i ≤ i₀ → Q u"; for the slots' marks the turn is typed: `withKept`, Honest/K9/MarksKept.lean. Called
at members: Honest/K9/YesToy.lean (`returnsHL`, `seatedFamilyH`); `gather_returns_of_list` by no line.
WHAT IS NOT CLAIMED. The clauses of any kind's run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GatherYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference.Desc (Block Claim claimsInBy)
open VerifiableInference.Desc.First (S)

/-- The fold returns, from any place, list and state. -/
theorem fold_returns_list (each : Nat × String → List Claim → S → Except String Unit) (bs : List (Block S Claim))
    (J : Nat → List Claim → S → Prop) : ∀ (order : List (Nat × String)) (i : Nat) (x : List Claim × S),
    J i x.1 x.2 →
    (∀ j o, order[j]? = some o → ∀ cs u, J (i + j) cs u → ∃ run z, claimsRunOf bs o = some run ∧
      run cs.length u = .ok z ∧ each o z.1 z.2 = .ok () ∧ J (i + j + 1) (cs ++ z.1) z.2) →
    ∃ y, order.foldl (gatherStep each bs) (.ok x) = .ok y ∧ J (i + order.length) y.1 y.2
  | [], i, x, hJ, _ => ⟨x, rfl, hJ⟩
  | o :: l, i, x, hJ, h => by
    obtain ⟨run, z, hr, hz, he, hJ'⟩ := h 0 o rfl x.1 x.2 hJ
    obtain ⟨y, hy, hJy⟩ := fold_returns_list each bs J l (i + 1) (x.1 ++ z.1, z.2) hJ' (by
      intro j o' hj cs u hu
      have e1 : i + 1 + j = i + (j + 1) := by omega
      rw [e1] at hu
      have := h (j + 1) o' (by simpa using hj) cs u hu
      rw [e1]
      exact this)
    refine ⟨y, ?_, ?_⟩
    · rw [List.foldl_cons]
      have hs : gatherStep each bs (.ok x) o = .ok (x.1 ++ z.1, z.2) := step_yes each bs x o run z hr hz he
      rw [hs]
      exact hy
    · have e2 : i + (o :: l).length = i + 1 + l.length := by rw [List.length_cons]; omega
      rw [e2]
      exact hJy

/-- **The gatherer returns**, with the claims in the family. -/
theorem gather_returns_list (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String)) (J : Nat → List Claim → S → Prop) (t : S)
    (hJ : J 0 [] t)
    (h : ∀ j o, order[j]? = some o → ∀ cs u, J j cs u → ∃ run z, claimsRunOf bs o = some run ∧
      run cs.length u = .ok z ∧ each o z.1 z.2 = .ok () ∧ J (j + 1) (cs ++ z.1) z.2) :
    ∃ y, claimsInBy each bs order t = .ok y ∧ J order.length y.1 y.2 := by
  obtain ⟨y, hy, hJy⟩ := fold_returns_list each bs J order 0 ([], t) hJ (by
    intro j o hj cs u hu
    rw [Nat.zero_add] at hu ⊢
    exact h j o hj cs u hu)
  rw [Nat.zero_add] at hJy
  exact ⟨y, hy, hJy⟩

/-- `gather_returns` is the case in which the family reads of the list its length alone. -/
theorem gather_returns_of_list (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String)) (I : Nat → Nat → S → Prop) (t : S)
    (hI : I 0 0 t)
    (h : ∀ j o, order[j]? = some o → ∀ n u, I j n u → ∃ run z, claimsRunOf bs o = some run ∧
      run n u = .ok z ∧ each o z.1 z.2 = .ok () ∧ I (j + 1) (n + z.1.length) z.2) :
    ∃ y, claimsInBy each bs order t = .ok y ∧ I order.length y.1.length y.2 :=
  gather_returns_list each bs order (fun j cs u => I j cs.length u) t hI (by
    intro j o hj cs u hu
    obtain ⟨run, z, hr, hz, he, hI'⟩ := h j o hj cs.length u hu
    exact ⟨run, z, hr, hz, he, by show I (j + 1) (cs ++ z.1).length z.2; rw [List.length_append]; exact hI'⟩)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.gather_returns_list
#print axioms ProofFile.Honest.K9.gather_returns_of_list
#print axioms ProofFile.Honest.K9.fold_returns_list
