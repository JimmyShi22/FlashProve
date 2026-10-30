-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ShapesSide.lean: FoldFacts' FIELD "K12.msgShapes" AT THE LIST THAT THE FIELD
NAMES: the fold of Johnson/IMR/ShapesFold.lean joined to the planner's side
(Johnson/Desc/K12/Door/SentAtPlace.lean: snAt, sendsAreB, shapes_side). One theorem, proved.

Compiled with the whole library.

  shapes_field   the debts ShapesOn at the table snAt Z G ps, the test sendsAreB at the chain's own
    number of sub-protocols, a first state without an oracle message: at every state that the fold
    reaches: atFirstShapes (msgsOfChain Z.made.proof.1) = true.

OBJECT: foldBlocks ft (c.blocksInOrder.take k) s₀ rs cols = .ok out. LETTERS: Z, G,
ps, c, s₀: free: nothing ties c to Z here.

What is not claimed. ShapesOn at any sub-protocol. That the test accepts anywhere. No soundness.

-/
import Johnson.IMR.ShapesFold
import Johnson.Desc.K12.Door.SentAtPlace

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Chain Place foldBlocks OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB shapes_side msgsOfChain atFirstShapes)
open ProofFile (Cl)

/-- **The field, at the planner's own list.** -/
theorem shapes_field {ft : ℕ} {Z : ProofFile.Pub} {G : ProofFile.Ground} {ps : List Place} {c : Chain S Cl}
    {s₀ : S}
    (h : ∀ j b, c.blocksInOrder[j]? = some b → ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ j) (snAt Z G ps j) b)
    (hB : sendsAreB Z.made.proof.1 c.blocksInOrder.length (snAt Z G ps) = true)
    (h0 : s₀.st.oracles = #[]) {k : ℕ} (hk : k ≤ c.blocksInOrder.length) {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft (c.blocksInOrder.take k) s₀ rs cols = .ok out) :
    atFirstShapes (msgsOfChain Z.made.proof.1) out.1 = true := by
  rw [shapes_side Z G ps c.blocksInOrder.length hB]
  exact (shapes_at_cutR h h0 hk hf).1

end IM

#print axioms IM.shapes_field
