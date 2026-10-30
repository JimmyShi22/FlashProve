-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/AskedWords.lean: a range test on the plain data that a parser hands over for an
entry file (`AskedE`, `OnBytes/Tie/EntryAsked.lean`). One definition; no theorem.

States. `askedWords a : Bool` is `okOut` (OnBytes/Maker/OkOut.lean) at `a.out`: every field element
in every round's message and in every opened column is a 64-bit word below the prime. It calls no
hash.
Under. No hypothesis: it is a definition. Its theorems: OnBytes/TypedOracleCompiler/Slice/AskedWordsLaws.lean
[not in this library; so here read: not proved in this library].
Does not show.
  1. The words of the two lists of seeds are not tested: the check of the entry file converts them
     to field elements and compares these with the seeds that it draws.
  2. Message items of the kinds "word" and "root" are not tested.
  3. What a round draws is not tested.
  4. Nonces, salt lengths and the run's value are not tested here: `askedFit` has its own clauses.
  5. That a root inside the chain has 32 bytes is not tested.
  6. The shape of an opening is not tested (see the notes of OnBytes/Maker/OkOut.lean).
  7. No way to cheat through a word at or above the prime has been shown.
  8. No theorem here says that it refuses what the verifier program's readers refuse.
  9. At a chain over the format's first field (a smaller prime) the readers refuse more words.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Maker.OkOut
import OnBytes.Tie.EntryAsked

set_option autoImplicit false

namespace TypedOracleCompiler.Slice

/-- **Every word of a field's element in the chain as read is below the prime.** -/
def askedWords (a : OnBytes.Tie.AskedE) : Bool := OnBytes.Maker.okOut a.out

end TypedOracleCompiler.Slice

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/TypedOracleCompiler/Slice/AskedWords.lean: a test on the plain data that a parser hands over for an entry
file (`AskedE`, OnBytes/Tie/EntryAsked.lean): every word of a field's element in the chain as read
is below the prime. A definition alone.

  `askedWords a` : Bool: `okOut` (OnBytes/Maker/OkOut.lean) at `a.out`: every item of every round's
    message, and every word of every opened column. No hash function is asked.

Beside it. `askedFit` (OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean) makes the like test on the two
tables' answers. The two lists of seeds are not tested here: the check types them and compares the
typed seeds with the drawn ones. The laws: OnBytes/TypedOracleCompiler/Slice/AskedWordsLaws.lean [not in this
library; so here read: not proved in this library].

What is not tested. The words of the two lists of seeds (above). The items "word" and "root"; what
a round draws; the nonces, the leaf salts' lengths and the run's value (`askedFit` has clauses of
its own on these three); that a root inside the chain has 32 bytes; an opening's shape: the head of
OnBytes/Maker/OkOut.lean. No way to cheat through a word that is not below the prime has been shown.
What the test does: it refuses a word of an item or of an opened column that the verifier program's
readers refuse for its range, at the second of the format's two fields, which both written grounds
name; no law here says so of a reader. At a chain whose plan names the first field, whose prime is
smaller, the readers refuse more words than this test.


-/
