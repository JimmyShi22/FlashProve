-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/ReachPure.lean: "REACHED" (ReachAt.lean) AT THE PROOF FILE's OWN IOP AS WRITTEN
IN LEAN (ProofFile.fileDescBy, Johnson/Desc/ProofFile/Frames1.lean): what a law that spends it gets, in
the letters in which the theorems along the fold are stated: the first chain c's own flat list, from
the first state "start" of the statement's own public part, at the first tree 0.

  rch_pure_fold     by unfolding: fileDescBy's field first is c, its field start₁ is start

No soundness statement.

-/
import Johnson.Top.H0.Walk.ReachAt
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open VerifiableInference.Desc (Chain foldBlocks)
open VerifiableInference.Desc.First (S)

theorem rch_pure_fold {σ Str : Type} {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Z : ProofFile.Pub}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {get : σ → S} {start : ProofFile.InstPub → σ}
    {c : Chain σ ProofFile.Cl} {k : ℕ} {a : (ProofFile.InstPub × σ) × Str}
    (h : RchAt (ProofFile.fileDescBy o mk Z A B get start c) k a) :
    k ≤ c.blocksInOrder.length ∧
      ∃ rs cols, foldBlocks 0 (c.blocksInOrder.take k) (start a.1.1) rs cols = .ok (a.1.2, [], []) :=
  rchAt_fold h

#print axioms rch_pure_fold

end Johnson.Desc.First.Walk.Tied
