-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureStoredW.lean: at the prover that `onlineProverFromPublicFiles` (Honest/AtPure.lean)
returns, at any choice of fields over `IndexCommitterCoins` whose columns are `Bind.ForProver.encW` at a reader of
the index, the stored words are the term `Bind.ForProver.storedW`
(Johnson/Bind/ForProver/TabCols.lean) at that reader. No definition; one short lemma.

  `atPure_storedW`   the filling is a letter; the one premise on its columns: he, on its field `enc`

Why. The columns' authors state their laws on the stored words at `storedW Z (weights w)`, from the
premise that a prover's field `stored` is `encW Z` at a reader of the index
(`storedWords_encW_at`); by that file's own Limits the premise «is said of no prover here». The
fifth clause of `atPure_ok` (Honest/AtPureLaw.lean) carries it to the filling's field `enc` (he) at
the prover that `onlineProverFromPublicFiles` returns. So these laws speak of that prover's stored words at a filling
that pays he, under their own premises.

Limits.
  * That `onlineProverFromPublicFiles` returns is a premise. No filling is named here, and of none is he shown.
  * What the columns are is their authors' matter (Johnson/Bind/ForProver/): nothing just at another
    item than 0, where `rowsFit` fails, and from 2^a on, a the depth of `shapeOf A.Z`. That they
    encode the index is not said here.
  * Nothing here ties the stored words to a commitment, to a key or to a witness's cells.
  * All limits of Johnson/Bind/ForProver/TabCols.lean hold here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.SharedChainProverSides
import Johnson.Bind.ForProver.TabCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W₀ : Type}

/-- **The stored words of the prover that `onlineProverFromPublicFiles` returns are `storedW` at the reader of the
index.** The filling is a letter. he: its columns are `encW` at that reader, at the public part that
`onlineProverFromPublicFiles` has made. -/
theorem atPure_storedW {Tr X₀ Y : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ IndexCommitterCoins Tr X₀ Y} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Tr X₀ Y} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (weights : W₀ → Weights) (he : ∀ w, P.enc A.Z w = Bind.ForProver.encW A.Z (weights w))
    (w₀ : W₀) : A.H.storedWords w₀ = Bind.ForProver.storedW A.Z (weights w₀) :=
  Bind.ForProver.storedWords_encW_at A.H A.Z weights
    (fun w => (congrFun (atPure_ok h).2.2.2.2.1 w).trans (he w)) w₀

end ProofFile.Honest

#print axioms ProofFile.Honest.atPure_storedW
