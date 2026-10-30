-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RunsKeep.lean: A LIGHT FILE, over the library's Block and its lemmas on keeping
alone: a sub-protocol's RUNS keep a relation, apart from its decision. General in the state's type,
the claims' type and the relation.
  RunsKeep R b: a sub-protocol's runs of claims and its runs behind the batching keep R: Whole
    without the decision: for one that sends, whose decision does not keep R. Whole.runs, runs_none.
  idle b: b with its decision struck. idle_whole, claimsIn_idle, afterIn_idle.
  claimsIn_runs, afterIn_runs, link_claims_runs, link_behind_runs: the gathered claims and "behind
    the batching" keep R where the hearing sub-protocols' RUNS do: by striking the decisions and
    calling the library's claimsIn_keeps, afterIn_keeps.
Cut out of Johnson/Goal/Meaning/GroupCalmK9.lean, which imports it: not a sign of a statement or a
proof has turned.
No soundness.
-/
import Johnson.Desc.BlockLaws
import Johnson.Desc.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open VerifiableInference.Desc
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)

/-! ## The runs of claims and the runs behind the batching, apart from the blocks' decisions -/

section Runs
variable {T C : Type} {R : T → T → Prop}

/-- A block's runs of claims and its runs behind the batching keep R: Whole without the decision:
for a block that sends, whose decision does not keep R, but which has no run, or calm ones. -/
def RunsKeep (R : T → T → Prop) (b : Block T C) : Prop :=
  (∀ c ∈ b.claims, ∀ n, FnCl R (c.2 n)) ∧ ∀ c ∈ b.after, Fn R c.2

theorem Whole.runs {b : Block T C} (W : Whole R b) : RunsKeep R b := W.2

theorem runs_none {b : Block T C} (h1 : b.claims = []) (h2 : b.after = []) : RunsKeep R b :=
  ⟨fun c hc => (by rw [h1] at hc; cases hc), fun c hc => (by rw [h2] at hc; cases hc)⟩

/-- The block with its decision struck: it hands the state on. -/
def idle (b : Block T C) : Block T C := { b with decide := fun s _ _ => .ok s }

theorem idle_whole (hr : ∀ s, R s s) {b : Block T C} (h : RunsKeep R b) : Whole R (idle b) :=
  ⟨fun s _ _ s' e => by cases e; exact hr s, h.1, h.2⟩

theorem claimsIn_idle (bs : List (Block T C)) (order : List (Nat × String)) (s : T) :
    claimsIn (bs.map idle) order s = claimsIn bs order s := by
  rw [Keeps.claimsIn_eq, Keeps.claimsIn_eq]
  congr 1
  funext acc o
  unfold Keeps.stepC
  rw [List.getElem?_map]
  cases bs[o.1]? <;> rfl

theorem afterIn_idle (bs : List (Block T C)) (order : List (Nat × String)) (s : T) :
    afterIn (bs.map idle) order s = afterIn bs order s := by
  rw [Keeps.afterIn_eq, Keeps.afterIn_eq]
  congr 1
  funext acc o
  unfold Keeps.stepA
  rw [List.getElem?_map]
  cases bs[o.1]? <;> rfl

/-- **The gathered claims keep R where the hearing blocks' RUNS do.** -/
theorem claimsIn_runs (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (bs : List (Block T C)) (hb : ∀ b ∈ bs, RunsKeep R b) (order : List (Nat × String)) :
    FnCl R (claimsIn bs order) := fun s y h =>
  Keeps.claimsIn_keeps R hr ht (bs.map idle)
    (fun b hb' => by
      obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb'
      exact idle_whole hr (hb b₀ h₀)) order s y ((claimsIn_idle bs order s).trans h)

/-- **So do the runs behind the batching.** -/
theorem afterIn_runs (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (bs : List (Block T C)) (hb : ∀ b ∈ bs, RunsKeep R b) (order : List (Nat × String)) :
    Fn R (afterIn bs order) := fun s y h =>
  Keeps.afterIn_keeps R hr ht (bs.map idle)
    (fun b hb' => by
      obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb'
      exact idle_whole hr (hb b₀ h₀)) order s y ((afterIn_idle bs order s).trans h)

/-- **At a link**: the function of claims that its batching is handed. -/
theorem link_claims_runs (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c) (Lk : Link T C)
    (hb : ∀ b ∈ Lk.hear, RunsKeep R b) : FnCl R (claimsInBy Lk.each Lk.hear Lk.order) :=
  fun s y h => claimsIn_runs hr ht Lk.hear hb Lk.order s y
    (claimsIn_of_claimsInBy Lk.each Lk.hear Lk.order s y h)

/-- **At a link**: what its block "behind the batching" decides by. -/
theorem link_behind_runs (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c) (Lk : Link T C)
    (hb : ∀ b ∈ Lk.hear, RunsKeep R b) : Fn R Lk.runBehind := fun s y h => by
  unfold Link.runBehind at h
  split at h
  · exact afterIn_runs hr ht Lk.hear hb Lk.orderAfter s y h
  · cases h

end Runs

#print axioms claimsIn_runs
#print axioms afterIn_runs
#print axioms link_claims_runs
#print axioms link_behind_runs

end Meaning.K2
