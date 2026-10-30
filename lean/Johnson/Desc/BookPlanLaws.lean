-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/BookPlanLaws.lean: what a yes of the tests on the plan (`BookPlan.allClausesHold`,
Johnson/Desc/BookPlan.lean) says, clause by clause; and THE ROW opened_trees_in_order OF THE LIST OF
LAWS OWED: under that yes the trees that a round opens are declared in strictly rising order of
their places. Statements and proofs.

Main names (namespace `VerifiableInference.Desc.BookPlan`).
  `ok_clause`: under `allClausesHold` every clause of the list says yes.
  `earlierPlace_trans`, `risingPlaces_pairwise`: each place before the next gives each place before
    every later one.
  `opened_trees_in_order`: under `allClausesHold D T`, in each of the three chains, for every declared round: of
    the places of the trees that it opens, in the declared order, each stands before every later
    one. `opened_trees_nodup`: so no round opens a tree twice.

The two silly members, read for a test on the plan. A test that says yes to all plans: the law is
false of it (a round that declares two trees the other way round). A test that says no to all: the
law holds and says nothing: that `allClausesHold` says yes at a real plan is a run's matter.

Limits. The order is by place (the chain that sent the tree; its number in that chain's order of
sending). That a verifier's book of trees lists them so, and that a view lists the opened columns in
the declared order, is not said here. Nothing on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.BookPlan

set_option autoImplicit false

namespace VerifiableInference.Desc.BookPlan

/-- Under `allClausesHold` every clause of the list says yes. -/
theorem ok_clause {D : DeclaredRoundsByChain} {T : SentOraclesByChain} (h : allClausesHold D T = true) {x : String × Bool}
    (hx : x ∈ clauses D T) : x.2 = true :=
  List.all_eq_true.1 h x hx

theorem earlierPlace_trans {a b c : Nat × Nat} (h1 : earlierPlace a b = true)
    (h2 : earlierPlace b c = true) : earlierPlace a c = true := by
  unfold earlierPlace at *
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
  omega

theorem earlierPlace_ne {a b : Nat × Nat} (h : earlierPlace a b = true) : a ≠ b := by
  intro e
  subst e
  unfold earlierPlace at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

/-- The first place of a rising list stands before every later one. -/
theorem risingPlaces_head : ∀ {l : List (Nat × Nat)} {a : Nat × Nat},
    risingPlaces (a :: l) = true → ∀ b ∈ l, earlierPlace a b = true
  | [], _, _, _, hb => absurd hb List.not_mem_nil
  | x :: l, a, h, b, hb => by
    have h' : (earlierPlace a x && risingPlaces (x :: l)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h'.1
    · exact earlierPlace_trans h'.1 (risingPlaces_head h'.2 b hb)

theorem risingPlaces_tail : ∀ {l : List (Nat × Nat)} {a : Nat × Nat},
    risingPlaces (a :: l) = true → risingPlaces l = true
  | [], _, _ => rfl
  | x :: l, a, h => by
    have h' : (earlierPlace a x && risingPlaces (x :: l)) = true := h
    rw [Bool.and_eq_true] at h'
    exact h'.2

/-- Each place before the next gives each place before every later one. -/
theorem risingPlaces_pairwise : ∀ {l : List (Nat × Nat)}, risingPlaces l = true →
    l.Pairwise fun a b => earlierPlace a b = true
  | [], _ => List.Pairwise.nil
  | _ :: _, h =>
    List.Pairwise.cons (risingPlaces_head h) (risingPlaces_pairwise (risingPlaces_tail h))

theorem inOrderIn_round {own : Nat} {ds : List Fmt.DeclaredRound} (h : inOrderIn own ds = true)
    {d : Fmt.DeclaredRound} (hd : d ∈ ds) :
    (d.opens.map fun o => treePlace own o.2).Pairwise fun a b => earlierPlace a b = true :=
  risingPlaces_pairwise (List.all_eq_true.1 h d hd)

/-- **opened_trees_in_order.** Under the tests on the plan, in each chain, for every declared round:
of the places of the trees that it opens, in the declared order, each stands before every later
one. -/
theorem opened_trees_in_order {D : DeclaredRoundsByChain} {T : SentOraclesByChain} (h : allClausesHold D T = true) :
    (∀ d ∈ D.1, (d.opens.map fun o => treePlace 0 o.2).Pairwise
      fun a b => earlierPlace a b = true) ∧
    (∀ d ∈ D.2.1, (d.opens.map fun o => treePlace 1 o.2).Pairwise
      fun a b => earlierPlace a b = true) ∧
    (∀ d ∈ D.2.2, (d.opens.map fun o => treePlace 2 o.2).Pairwise
      fun a b => earlierPlace a b = true) := by
  have hO : inOrder D = true :=
    ok_clause h (x := ("inOrder", inOrder D)) (by unfold clauses; simp)
  unfold inOrder at hO
  simp only [Bool.and_eq_true] at hO
  exact ⟨fun _ hd => inOrderIn_round hO.1.1 hd, fun _ hd => inOrderIn_round hO.1.2 hd,
    fun _ hd => inOrderIn_round hO.2 hd⟩

/-- So no round opens a tree twice. -/
theorem opened_trees_nodup {D : DeclaredRoundsByChain} {T : SentOraclesByChain} (h : allClausesHold D T = true) :
    (∀ d ∈ D.1, (d.opens.map fun o => treePlace 0 o.2).Nodup) ∧
    (∀ d ∈ D.2.1, (d.opens.map fun o => treePlace 1 o.2).Nodup) ∧
    (∀ d ∈ D.2.2, (d.opens.map fun o => treePlace 2 o.2).Nodup) :=
  ⟨fun d hd => ((opened_trees_in_order h).1 d hd).imp earlierPlace_ne,
    fun d hd => ((opened_trees_in_order h).2.1 d hd).imp earlierPlace_ne,
    fun d hd => ((opened_trees_in_order h).2.2 d hd).imp earlierPlace_ne⟩

end VerifiableInference.Desc.BookPlan

#print axioms VerifiableInference.Desc.BookPlan.opened_trees_in_order
#print axioms VerifiableInference.Desc.BookPlan.opened_trees_nodup
