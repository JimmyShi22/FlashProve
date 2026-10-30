-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/OrderMeans.lean: WHAT EACH TEST OF Johnson/Desc/First/K8/Order.lean CHECKS, AS
A PROPOSITION, PROVED: for every yes-or-no text there a statement in plain logic (and, or, there is,
for all; equalities and inequalities of numbers) with the proof that the text says yes exactly where
the statement holds. NO RUNNING TEXT IMPORTS THIS FILE. Nothing on soundness is said: these say what
is asked, not why that is enough.
  sentInFront_iff · answered_iff · fixed_iff · orderOk_iff · front_ok_iff_means · close_ok_iff
liesAt and namedNow are readings: what they return is their own text.

-/
import Johnson.Desc.First.K8.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Order
open OnBytes OnBytes.Model

/-- (3): born at this link, at an earlier moment than the present one; or born at an earlier link,
with a life that reaches this link. -/
theorem sentInFront_iff (L : LinkCtx) (w : Lies) :
    sentInFront L w = true ↔
      (w.born = L.link ∧ w.moment < L.moments) ∨
        (w.born < L.link ∧ L.link ≤ w.born + w.life) := by
  unfold sentInFront
  by_cases h : w.born = L.link
  · simp [h]
  · simp [h]

/-- (4): the statement has the message under the number that it bears now, and its sample is
answered. -/
theorem answered_iff (L : LinkCtx) (S : Statement) (w : Lies) :
    answered L S w = true ↔
      ∃ o x, namedNow L.check.frame w = some o ∧ S.oracles[o]? = some x ∧ x.sampled = true := by
  unfold answered
  cases h1 : namedNow L.check.frame w with
  | none => simp
  | some o =>
    cases h2 : S.oracles[o]? with
    | none => simp [h2]
    | some x => simp [h2]

/-- (1) to (4), of one array. -/
theorem fixed_iff (L : LinkCtx) (S : Statement) (array : Nat) :
    fixed L S array = true ↔
      ∃ w, liesAt L array = some w ∧ sentInFront L w = true ∧ answered L S w = true := by
  unfold fixed
  cases h : liesAt L array with
  | none => simp
  | some w => simp

/-- The guard of order. -/
theorem orderOk_iff (tl : HTailF2) (L : LinkCtx) (S : Statement) :
    orderOk tl L S = true ↔
      L.check.link = L.link ∧ L.link < L.check.links ∧ tl.gtTree.size = tl.NM ∧
        (∀ a ∈ tl.gtTree, fixed L S a = true) ∧
        ∀ n, n < 4 → ∀ u, tl.ix.U.getD n none = some u → fixed L S u = true := by
  unfold orderOk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem,
    List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨h1, h2, h3, h4, fun n hn u hu => ?_⟩
    have h := h5 n hn
    simpa [hu] using h
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, fun n hn => ?_⟩
    cases hu : tl.ix.U.getD n none with
    | none => rfl
    | some u => simpa [hu] using h5 n hn u hu

/-- In front of the draw. -/
theorem front_ok_iff_means (tl : HTailF2) (L : LinkCtx) (S : Statement) :
    front tl L S = .ok () ↔
      tl.funClosed = true ∧ tl.shp.size = tl.NM ∧ orderOk tl L S = true := by
  unfold front
  by_cases h1 : tl.funClosed <;> by_cases h2 : tl.shp.size = tl.NM <;>
    by_cases h3 : orderOk tl L S <;> simp [h1, h2, h3]

/-- The closing of the list of tables. -/
theorem close_ok_iff (tl tl' : HTailF2) (funs : Array HFun) :
    close tl funs = .ok tl' ↔
      tl.funClosed = false ∧ tl' = { tl with funClosed := true, funs := funs } := by
  unfold close
  by_cases h : tl.funClosed
  · simp [h]
  · simp [h, eq_comm]

end VerifiableInference.Desc.First.K8.Order

#print axioms VerifiableInference.Desc.First.K8.Order.sentInFront_iff
#print axioms VerifiableInference.Desc.First.K8.Order.answered_iff
#print axioms VerifiableInference.Desc.First.K8.Order.fixed_iff
#print axioms VerifiableInference.Desc.First.K8.Order.orderOk_iff
#print axioms VerifiableInference.Desc.First.K8.Order.front_ok_iff_means
#print axioms VerifiableInference.Desc.First.K8.Order.close_ok_iff
