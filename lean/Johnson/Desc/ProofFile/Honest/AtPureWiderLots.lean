-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureWiderLots.lean: how a kind's list of prover's sides stands in
the choice of fields `widerFillOwn` (Honest/AtPureWiderAt.lean). Two lemmas with their proofs.

Why. In that choice every list that reads the index is wrapped by `HLot.byPub`, because the reader
of the index depends on the public part. So such a list, at one reader, need not be a member of the
field `lots`, and a lemma about the maker's prover that asks for that membership does not apply
there as it stands. What can be had is a member whose sides at every public part are those of the
kind's list at the reader of that public part. `atPure_first_find_kind` (Honest/FirstFindKind.lean)
needs no more for its premise of membership; its other premises are still owed.

  `HLot.byPub_halves`   the wrapped list's sides
  `widerFillOwn_k4`     the member for K4's list: one member, at every public part and ground

Limits.
  * One kind. The other wrapped lists (K1, K2, K11, K13, K3, K6) have the same form; for K1, K3, K6,
    K11 and K13 the list is a field of the letter for the long lists, so a like lemma reaches the
    kind's own list only at `LongLots.plain` or under a premise on that letter. K7's, K5's and K8's
    lists are not wrapped.
  * Names are not compared: the lemmas speak of a list's sides alone.
  * A like lemma at every pair of a list of pairs, under the premise that the choice's field `lots`
    is the list of the pairs' first halves, and with the public part and the ground bound before the
    member, is `FirstFill.pairs_hex` (Honest/Thread/FirstFillPairs.lean, by the authors of K5's
    rounds; not imported here).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W₀ V W X : Type}

/-- The wrapped list's sides at a public part are the list's, at the reader of that public part. -/
theorem HLot.byPub_halves (weights : Pub → W₀ → Weights) (L : (W₀ → Weights) → HLot V W X)
    (Z : Pub) (G : Ground) : (HLot.byPub weights L).halves Z G = (L (weights Z)).halves Z G :=
  rfl

/-- **K4's list in the choice of fields**: one member of `lots` whose sides at every public part and
ground are those of `K4.k4HLot` at the reader of that public part. -/
theorem widerFillOwn_k4 (own₀ : X) (Ls : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ M ∈ (widerFillOwn own₀ Ls I o S O).lots, ∀ (Z : Pub) (G : Ground),
      M.halves Z G = (K4.k4HLot id (I.weights Z) fun _ _ => K4.k4LookAt).halves Z G :=
  ⟨HLot.byPub I.weights fun wt => K4.k4HLot id wt fun _ _ => K4.k4LookAt,
    .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), fun _ _ => rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.HLot.byPub_halves
#print axioms ProofFile.Honest.widerFillOwn_k4
