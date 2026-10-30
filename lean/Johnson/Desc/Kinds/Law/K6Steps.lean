-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Steps.lean: what the output head's own law at the table's frame spends of
the head's block: three sentences on Block.step, as one record; and the two blocks that meet it.

Law/K6Own.lean and Law/K6OwnW.lean call the bridge from a kind's rule of bad elements to a block's
own law. Of the block they spend three facts alone, all on its step. Here these are a record,
general in the block, in its type of claims and in the condition on the record in front; so that one
chain of laws serves the block at the unit type (blockOf W l, under K6On) and the block that a lot
seats (seatedClaims W l ms, under the shorter K6Left).

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  K6Steps W b on after: row (the out-law: on in front, no bad draw, canonical rounds, the step goes
      on, what the block opens: then what it closes) · promise (on in front, the step goes on: after
      behind) · unmarked (the step goes on: no mark in front, none behind).
  K6Steps.weaken: a weaker promise behind.
  K6AfterAll W s': K6After, and the two readers of the lookup's hearing agree whole.
  k6Steps_blockOf: blockOf W l meets it at on := K6On W, after := K6AfterAll W.
  k6Steps_seated: THE SEATED BLOCK seatedClaims W l ms, where its test on the plan says yes, meets
      it at after := K6AfterAll W and on := K6Left W (the ledger well laid; a heard token below V;
      the lookup's last claim's numbers filled): of K6On's six clauses two are paid by the plan's
      yes and one by the step's.

What it does not say. That K6Left holds anywhere. Nothing on chance beyond "no bad draw". Nothing on
soundness.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.SeatedSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)

/-- **What the head's own law at the table's frame spends of the head's block.** -/
structure K6Steps {Cl : Type} (W : OnBytes.Model.Verify.Public) (b : Block S Cl)
    (on after : S → Prop) : Prop where
  row : ∀ (ft : Nat) (s : S) (d : Pinned) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat),
    on s → Sound.NoBad (ruleStep W s d) rs → Canonical rs → b.step ft s rs cols = .ok (s', n) →
    K6Out W s' d → K6In W s d
  promise : ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat),
    on s → b.step ft s rs cols = .ok (s', n) → after s'
  unmarked : ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat),
    b.step ft s rs cols = .ok (s', n) → s.failed = none ∧ s'.failed = none

/-- A weaker promise behind. -/
theorem K6Steps.weaken {Cl : Type} {W : OnBytes.Model.Verify.Public} {b : Block S Cl}
    {on after after' : S → Prop} (h : K6Steps W b on after) (hw : ∀ s', after s' → after' s') :
    K6Steps W b on after' :=
  ⟨h.row, fun ft s rs cols s' n ha hs => hw s' (h.promise ft s rs cols s' n ha hs), h.unmarked⟩

/-- K6After, and the two readers of the lookup's hearing agree whole. -/
def K6AfterAll (W : OnBytes.Model.Verify.Public) (s' : S) : Prop :=
  K6After W s' ∧ s'.look? = s'.lookHeard?

/-- The block at the unit type, under K6On. -/
theorem k6Steps_blockOf (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) : K6Steps W b (K6On W) (K6AfterAll W) where
  row := fun ft s d rs cols s' n ha hnb hcan hs hout =>
    Came.rowStep W l b hb ft s d rs cols s' n ha hnb hcan hs hout
  promise := fun ft s rs cols s' n ha hs =>
    ⟨(Came.rowPromise W l b hb ft s rs cols s' n ha hs).1,
      (Came.rowPromise W l b hb ft s rs cols s' n ha hs).2.2⟩
  unmarked := fun ft s rs cols s' n hs => Came.unmarked_both W l b hb ft s rs cols s' n hs

/-- **The seated block, under K6Left.** -/
theorem k6Steps_seated {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (hb : seatedClaims W l ms = some b) (hp : b.planOk = true) :
    K6Steps W b (K6Left W) (K6AfterAll W) where
  row := fun ft s d rs cols s' n ha hnb hcan hs hout =>
    rowStep_seated hb hp ft s d rs cols s' n ha hnb hcan hs hout
  promise := fun ft s rs cols s' n ha hs =>
    ⟨(rowPromise_seated hb hp ft s rs cols s' n ha hs).1.1,
      (rowPromise_seated hb hp ft s rs cols s' n ha hs).2⟩
  unmarked := fun ft s rs cols s' n hs => by
    obtain ⟨bU, hU, hsU, _⟩ := seated_step hb hs
    exact Came.unmarked_both W l bU hU ft s rs cols s' n hsU

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Steps_blockOf
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Steps_seated
