-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineShapeOfFold.lean: a verifier's state that a chain's own accepted fold reaches has the shape that
the shape's run has there: `shape_at` (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) with no thread.
General in the chain and the shape.

  `shape_of_fold`   the statement

A law on the verifier's side alone: it reads no prover, no input and no coin. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Shape
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)

/-- **Where the fold over a chain's first b sub-protocols accepts, the state has the shape that the shape's run
has there.** -/
theorem shape_of_fold {S Cl : Type} (Z : Shape S) {ft : Nat} {bs : List (Block S Cl)}
    (hC : ∀ j, Carries bs ft Z j) {a₀ : Z.Sh} {n b : Nat} (hn : n ≤ bs.length) (hb : b ≤ n)
    (hyes : Z.yes a₀ n = true) {s₀ s : S} {rs r : List Fmt.RoundView} {cols c : List OpenedColumn}
    (h0 : Z.sh s₀ = a₀) (hf : foldBlocks ft (bs.take b) s₀ rs cols = .ok (s, r, c)) :
    Z.run b a₀ = .ok (Z.sh s) := by
  have hr : Reach ft bs (fun _ : Unit => s₀) b ((), s) :=
    reach_of_fold b (Nat.le_trans hb hn) s _ _ _ _ hf
  obtain ⟨e, he⟩ := run_front Z a₀ n b hb hyes
  have e1 := shape_reach Z hC hr e (by
    show Z.run b (Z.sh s₀) = .ok e
    rw [h0]
    exact he)
  rw [he, e1]

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.shape_of_fold
