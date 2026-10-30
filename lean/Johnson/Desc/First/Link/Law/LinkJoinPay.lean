-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkJoinPay.lean: THE LAW OF A LINK FROM ONE DUTY AN ENTRY OF THE ORDER:
the list of runs with their terms that `LinkJoin.RunsAsk` takes
(Johnson/Desc/First/Link/Law/LinkJoinRuns.lean: rl, hrl, hrun, hrund) IS MADE HERE off the link
itself, from a table of terms by the order's entries. Theorems: tools for the assembly of the
kinds' payers.

What is said.
  `At L o run`, `AtAfter L o run`: the run that the link's hearing blocks state under the entry o of
    the order (of the order behind the batching). `rlOf L tmOf lenOf`: the runs that the order
    names, each with the terms and the number that the table gives its entry. `rlOf_runs`: they ARE
    the runs that the order names (`hrl`). `rlOf_runOk`, `rlOf_door`: **`hrun` and `hrund` from one
    duty an entry**: for each entry o of the order, whatever run stands there meets `RunOk` at `tmOf
    o`, `lenOf o`, and keeps the door.
  `order_layers`, `order_attention`, `order_head`, and the three for the orders behind the batching:
    **the driver's orders, entry by entry**: a sentence on every entry of a sort's order is the
    conjunction of that sentence at its 7, 10, 11 (3, 2, 2) entries. `order_at`: a segment (`SegAt`)
    has its sort's orders.

Limits. Tools. Each entry's duty stays its kind's files' to show. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkJoinRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.JoinAtBlocks

variable {T P K : Type}

/-- The run of claims that the link's hearing blocks state under an entry of the order. -/
def At (L : Link T Claim) (o : ℕ × String) (run : ℕ → T → Except String (List Claim × T)) : Prop :=
  ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some run

/-- The run behind the batching that they state under an entry of the order behind it. -/
def AtAfter (L : Link T Claim) (o : ℕ × String) (run : T → Except String T) : Prop :=
  ((L.hear[o.1]?).bind fun b => b.after.lookup o.2) = some run

/-- The runs that the order names, each with the terms that a table gives its entry. -/
def rlOf (L : Link T Claim) (tmOf : ℕ × String → ℕ → P → Bound K → List (ℕ × K))
    (lenOf : ℕ × String → P → ℕ) : List (TermedRun T P K) :=
  L.order.filterMap fun o =>
    ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2).map fun r => ⟨(o.2, r), tmOf o, lenOf o⟩

/-- They are the runs that the order names. -/
theorem rlOf_runs (L : Link T Claim) (tmOf : ℕ × String → ℕ → P → Bound K → List (ℕ × K))
    (lenOf : ℕ × String → P → ℕ) :
    (rlOf L tmOf lenOf).map (·.run) = runsIn L.hear L.order := by
  unfold rlOf runsIn
  rw [List.map_filterMap]
  congr 1
  funext o
  cases ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) <;> rfl

theorem mem_rlOf {L : Link T Claim} {tmOf : ℕ × String → ℕ → P → Bound K → List (ℕ × K)}
    {lenOf : ℕ × String → P → ℕ} {r : TermedRun T P K} (h : r ∈ rlOf L tmOf lenOf) :
    ∃ o ∈ L.order, At L o r.run.2 ∧ r.tm = tmOf o ∧ r.len = lenOf o := by
  obtain ⟨o, ho, h2⟩ := List.mem_filterMap.1 h
  refine ⟨o, ho, ?_⟩
  unfold At
  cases hl : ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) with
  | none =>
    rw [hl] at h2
    exact nomatch h2
  | some run =>
    rw [hl] at h2
    obtain rfl := Option.some.inj h2
    exact ⟨rfl, rfl, rfl⟩

variable [Field K] (ρ : Reading K) (X : Lens T) (O : Others T P K) (Fx : P → T → Prop)

/-- **hrun, FROM ONE DUTY AN ENTRY OF THE ORDER.** -/
theorem rlOf_runOk (L : Link T Claim) (tmOf : ℕ × String → ℕ → P → Bound K → List (ℕ × K))
    (lenOf : ℕ × String → P → ℕ)
    (h : ∀ o ∈ L.order, ∀ run, At L o run → RunOk ρ X O Fx run (tmOf o) (lenOf o)) :
    ∀ r ∈ rlOf L tmOf lenOf, RunOk ρ X O Fx r.run.2 r.tm r.len := by
  intro r hr
  obtain ⟨o, ho, ha, e1, e2⟩ := mem_rlOf hr
  rw [e1, e2]
  exact h o ho _ ha

omit [Field K] in
/-- **hrund, the like.** -/
theorem rlOf_door (L : Link T Claim) (tmOf : ℕ × String → ℕ → P → Bound K → List (ℕ × K))
    (lenOf : ℕ × String → P → ℕ)
    (h : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor X e e₁) :
    ∀ r ∈ rlOf L tmOf lenOf, ∀ n e c e₁, r.run.2 n e = .ok (c, e₁) → KeepsDoor X e e₁ := by
  intro r hr
  obtain ⟨o, ho, ha, _, _⟩ := mem_rlOf hr
  exact h o ho _ ha

/-! ## The driver's orders, entry by entry -/

/-- A segment has its sort's orders. -/
theorem order_at {S' Cl : Type} {l : ℕ} {sub : First.ModelPart} {L : Link S' Cl} (h : SegAt l sub L) :
    L.order = First.orderOf sub ∧ L.orderAfter = First.orderAfterOf sub := ⟨h.order, h.orderAfter⟩

theorem order_layers (Q : ℕ × String → Prop) : (∀ o ∈ First.orderOf .layers, Q o) ↔
    Q (1, "objects") ∧ Q (1, "guests") ∧ Q (2, "front") ∧ Q (6, "objects") ∧ Q (6, "guests") ∧
      Q (4, "K8.equations") ∧ Q (2, "back") := by
  simp [First.orderOf, First.orderCuts]

theorem order_attention (Q : ℕ × String → Prop) : (∀ o ∈ First.orderOf .attention, Q o) ↔
    Q (1, "objects") ∧ Q (1, "guests") ∧ Q (2, "first") ∧ Q (2, "keys") ∧ Q (2, "join") ∧
      Q (2, "second") ∧ Q (1, "planes") ∧ Q (6, "objects") ∧ Q (6, "guests") ∧
      Q (4, "K8.equations") := by
  simp [First.orderOf, First.orderCuts]

theorem order_head (Q : ℕ × String → Prop) : (∀ o ∈ First.orderOf .head, Q o) ↔
    Q (2, "objects") ∧ Q (2, "guests") ∧ Q (3, "norm") ∧ Q (3, "join") ∧ Q (3, "policy") ∧
      Q (2, "planes") ∧ Q (7, "objects") ∧ Q (7, "guests") ∧ Q (5, "K8.equations") ∧
      Q (3, "logits") ∧ Q (8, "the merge") := by
  simp [First.orderOf, First.orderCuts]

theorem after_layers (Q : ℕ × String → Prop) : (∀ o ∈ First.orderAfterOf .layers, Q o) ↔
    Q (4, "K8.lsTail") ∧ Q (2, "free-slot") ∧ Q (4, "K8.tests") := by
  simp [First.orderAfterOf]

theorem after_attention (Q : ℕ × String → Prop) : (∀ o ∈ First.orderAfterOf .attention, Q o) ↔
    Q (4, "K8.lsTail") ∧ Q (4, "K8.tests") := by
  simp [First.orderAfterOf]

theorem after_head (Q : ℕ × String → Prop) : (∀ o ∈ First.orderAfterOf .head, Q o) ↔
    Q (5, "K8.lsTail") ∧ Q (5, "K8.tests") := by
  simp [First.orderAfterOf]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rlOf_runs
#print axioms VerifiableInference.Desc.LinkJoin.rlOf_runOk
#print axioms VerifiableInference.Desc.LinkJoin.rlOf_door
#print axioms VerifiableInference.Desc.LinkJoin.order_at
#print axioms VerifiableInference.Desc.LinkJoin.order_layers
#print axioms VerifiableInference.Desc.LinkJoin.order_attention
#print axioms VerifiableInference.Desc.LinkJoin.order_head
#print axioms VerifiableInference.Desc.LinkJoin.after_layers
#print axioms VerifiableInference.Desc.LinkJoin.after_attention
#print axioms VerifiableInference.Desc.LinkJoin.after_head
