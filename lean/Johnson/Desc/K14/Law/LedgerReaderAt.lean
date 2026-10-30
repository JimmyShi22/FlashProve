-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerReaderAt.lean: wordsSh (Johnson/Desc/K14/Law/LedgerReader.lean) IS
wordsShared (Johnson/Desc/Sound/WordsAt.lean), as a term. A file of its own: whatever
imports WordsAt.lean cannot import the fence (two structures named Sound.Booked), over which the
ledger stands.

  wordsSh_is      by rfl.

-/
import Johnson.Desc.K14.Law.LedgerReader
import Johnson.Desc.Sound.WordsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound

theorem wordsSh_is {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (t₁ : ℕ) (st : Statement) (book : TreeBook)
    (w : Wit Cells Tok MsgT) : wordsSh arr t₁ st book w = wordsShared arr t₁ st book w := rfl

end Desc.K14.Law

#print axioms Desc.K14.Law.wordsSh_is
