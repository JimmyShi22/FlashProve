-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/MovedDrawn.lean: where a sub-protocol has been played
(`Thread.Moved`, Pays.lean), the challenges in the rounds played are the challenges that were handed
to the play. The lemmas that end in `Accepted`, `AcceptedS` or `AcceptedJ` take this fact inside
their proofs. Here it has a name, for lemmas that compare a test on the rounds with a test on the
challenges. No definition.

  1  `moved_drawn`   the lemma

Limits.
  * It says nothing about what was sent.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- The rounds played show the challenges that were handed to the play. -/
theorem moved_drawn {blk : Block S Cl} {k : Coins Bk} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (h : T.Moved blk k m E ds y cols) : (roundsOf y.1).map (·.drawn) = ds := by
  unfold Thread.Moved at h
  obtain ⟨⟨l, -, hy⟩, -⟩ := h
  exact yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)

end ProofFile.Honest

#print axioms ProofFile.Honest.moved_drawn
