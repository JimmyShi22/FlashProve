-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/OpensOfPlan.lean: the test `Thread.opensAvailable`
(Honest/Thread/OneState.lean) at every border of the first and of the shared chain, from the
description's tests on the plan. By `BookPlan.inTime` no tree is opened in front of its sending, and on
these two chains no tree is taken over. What a round opens was so sent by a round at or in front of it.

  `roots_eq_trees`   the roots that a list of sub-protocols declares are the trees that it sends
  `roots_of_fits`   the clause of `Thread.fits` that says so
  `opensAvailable_of_plan`   the test at every border, at a thread whose flat list has the rounds of a
                   chain number other than 2
  `opensAvailable_first`, `opensAvailable_shared`   the same at the description's two chains

The premise `hor` is a clause of `Thread.fits`: each round declares as many roots as it sends. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.OneState
import Johnson.Desc.ProofFile.Honest.Law.PlanGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W X Pb Xi : Type} {Bk : ProverCoinCounts}

/-- **The roots that a list of sub-protocols declares are the trees that it sends.** -/
theorem roots_eq_trees : ∀ bs : List (Block S Cl),
    (∀ x ∈ bs, x.rounds.map (·.entry.roots) = x.oracles.map (·.length)) →
    ((bs.flatMap (·.rounds)).map (·.entry.roots)).sum =
      (bs.flatMap fun x => x.oracles.flatMap id).length
  | [], _ => rfl
  | x :: l, h => by
    have e : (x.oracles.flatMap id).length = (x.oracles.map (·.length)).sum := by
      rw [List.length_flatMap]
      rfl
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.sum_append, List.length_append,
      h x List.mem_cons_self, e, roots_eq_trees l fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- The clause of `Thread.fits`. -/
theorem roots_of_fits {T : Thread Bk S Cl V W X Pb} {n : Nat} (h : T.fits n = true) :
    ∀ x ∈ T.bs, x.rounds.map (·.entry.roots) = x.oracles.map (·.length) := by
  unfold Thread.fits at h
  simp only [Bool.and_eq_true] at h
  intro x hx
  have h2 := List.all_eq_true.1 h.1.1.1.2 x hx
  simp only [Bool.and_eq_true] at h2
  exact beq_iff_eq.1 h2.2

/-- **The test at every border.** -/
theorem opensAvailable_of_plan {F : FileDescription Xi} (hp : F.planOk = true)
    (T : Thread Bk S Cl V W X Pb) {i : Nat}
    (hi : (T.bs.flatMap (·.rounds), i) ∈ [(F.roundsDeclaredByBlocks.1, 0), (F.roundsDeclaredByBlocks.2.1, 1), (F.roundsDeclaredByBlocks.2.2, 2)])
    (h2 : i ≠ 2)
    (hor : ∀ x ∈ T.bs, x.rounds.map (·.entry.roots) = x.oracles.map (·.length)) (b : Nat) :
    T.opensAvailable b = true := by
  have hT := inTime_plan hp
  unfold BookPlan.inTime at hT
  have h1 := List.all_eq_true.1 hT (T.bs.flatMap (·.rounds), i) hi
  have hsplit : T.bs.flatMap (·.rounds) =
      declsTo T.bs b ++ (T.bs.drop b).flatMap (·.rounds) := by
    unfold declsTo
    rw [← List.flatMap_append, List.take_append_drop]
  unfold Thread.opensAvailable
  rw [List.all_eq_true]
  intro d hd
  rw [List.all_eq_true]
  intro o ho
  obtain ⟨r, hr⟩ := List.mem_iff_getElem?.1 hd
  have hrl : r < (declsTo T.bs b).length := (List.getElem?_eq_some_iff.1 hr).1
  have hr' : (T.bs.flatMap (·.rounds))[r]? = some d := by
    rw [hsplit, List.getElem?_append_left hrl]
    exact hr
  have h3 := List.all_eq_true.1 (List.all_eq_true.1 h1 (d, r) (by
    have e := mem_zipIdx_of _ 0 r d hr'
    rw [Nat.zero_add] at e
    exact e)) o ho
  cases hs : o.2 with
  | own n =>
    rw [hs] at h3
    have h3' : ((BookPlan.roundOfRoot (T.bs.flatMap (·.rounds)) n).any fun j =>
        decide (j + (if BookPlan.holdsSampled F.roots i n then 1 else 0) ≤ r)) = true := h3
    cases hj1 : BookPlan.roundOfRoot (T.bs.flatMap (·.rounds)) n with
    | none =>
      rw [hj1] at h3'
      cases h3'
    | some j =>
      rw [hj1] at h3'
      have hj2 : j + (if BookPlan.holdsSampled F.roots i n then 1 else 0) ≤ r :=
        of_decide_eq_true h3'
      have hjr : j ≤ r := Nat.le_trans (Nat.le_add_right _ _) hj2
      have hlt := root_lt _ n j hj1
      have htake : (T.bs.flatMap (·.rounds)).take (j + 1) = (declsTo T.bs b).take (j + 1) := by
        rw [hsplit, List.take_append_of_le_length (by omega)]
      rw [htake, List.map_take] at hlt
      have hle := sum_take_le ((declsTo T.bs b).map (·.entry.roots)) (j + 1)
        (declsTo T.bs b).length (by omega)
      have hall : ((declsTo T.bs b).map (·.entry.roots)).take (declsTo T.bs b).length =
          (declsTo T.bs b).map (·.entry.roots) := by
        apply List.take_of_length_le
        rw [List.length_map]
      rw [hall] at hle
      have htr : ((declsTo T.bs b).map (·.entry.roots)).sum = treesTo T.bs b :=
        roots_eq_trees (T.bs.take b) fun y hy => hor y (List.mem_of_mem_take hy)
      have hn : n < treesTo T.bs b := by omega
      refine decide_eq_true ?_
      exact List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)
  | taken ch j =>
    rw [hs] at h3
    have h4 : (i == 2 && decide (ch < 2) && (BookPlan.roundOfRoot
        (([F.roundsDeclaredByBlocks.1, F.roundsDeclaredByBlocks.2.1, F.roundsDeclaredByBlocks.2.2][ch]?).getD []) j).isSome) = true := h3
    rw [Bool.and_eq_true, Bool.and_eq_true] at h4
    exact absurd (beq_iff_eq.1 h4.1.1) h2

/-- **At the description's first chain.** -/
theorem opensAvailable_first {F : FileDescription Xi} (hp : F.planOk = true)
    (T : Thread Bk F.S₁ F.Cl V W X Pb) (hbs : T.bs = F.first.blocksInOrder)
    (hor : ∀ x ∈ T.bs, x.rounds.map (·.entry.roots) = x.oracles.map (·.length)) (b : Nat) :
    T.opensAvailable b = true :=
  opensAvailable_of_plan hp T (i := 0) (by rw [hbs]; exact .head _) (by decide) hor b

/-- **At the description's shared chain.** -/
theorem opensAvailable_shared {F : FileDescription Xi} (hp : F.planOk = true)
    (T : Thread Bk F.S₂ F.Cl V W X Pb) (hbs : T.bs = F.shared.blocksInOrder)
    (hor : ∀ x ∈ T.bs, x.rounds.map (·.entry.roots) = x.oracles.map (·.length)) (b : Nat) :
    T.opensAvailable b = true :=
  opensAvailable_of_plan hp T (i := 1) (by rw [hbs]; exact .tail _ (.head _)) (by decide) hor b

end ProofFile.Honest

#print axioms ProofFile.Honest.roots_eq_trees
#print axioms ProofFile.Honest.roots_of_fits
#print axioms ProofFile.Honest.opensAvailable_of_plan
#print axioms ProofFile.Honest.opensAvailable_first
#print axioms ProofFile.Honest.opensAvailable_shared
