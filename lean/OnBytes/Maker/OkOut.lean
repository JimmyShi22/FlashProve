-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OkOut.lean: the test that every field element in a chain as read (`Fmt.ChainOut`,
Fmt/Rules8.lean) is a 64-bit word below the prime. Definitions only.

States. `okRoundOut`: every item of the round's message passes `okGot` (OnBytes/Maker/OkView.lean)
and every word of every opened column is below p. `okOut`: every round passes.
Why. The verifier program's readers return a field element only if it is below the prime; data from
an untrusted parser have passed no such reader, so a check on such data that is to refuse what the
readers refuse makes this test itself.
Under. No hypothesis: these are definitions. p = 2^64 − 2^32 + 1 (`pW`, OnBytes/Field/Word.lean),
the prime of the format's second field.
Does not show.
  1. At a chain whose parameters name the first field (a smaller prime) the readers refuse more.
  2. The `okGot` used here does not ask that a root has 32 bytes; the one in `formOf` does.
  3. Message items of the kinds "word" and "root" are not tested.
  4. What a round draws, its nonce, its list of positions and its message's bytes are not tested.
  5. An opening's shape, salts, given digests and vertices are not tested.
  6. The chain's four strings and its record of vertices are not tested.
  7. No theorem is stated here: see OnBytes/Maker/OkOutLaws.lean and OnBytes/Maker/OkOutOfRead.lean.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Maker.OkView

set_option autoImplicit false

namespace OnBytes.Maker

/-- Every word of a field's element in a round as read is below p: in the message's items and in the
opened columns. -/
def okRoundOut (r : Fmt.RoundOut) : Bool :=
  r.vals.all okGot && r.opens.all fun y => y.2.2.cols.all fun c => c.all okF

/-- **Every word of a field's element in a chain as read is below p.** -/
def okOut (o : Fmt.ChainOut) : Bool := o.rounds.toList.all okRoundOut

end OnBytes.Maker

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Maker/OkOut.lean: the test that every word of a field's element in a chain as read
(`Fmt.ChainOut`, Fmt/Rules8.lean) is below the prime. Definitions alone.

Why. The verifier program's readers return a word of a field's element only if it is below the
field's prime (`Fmt.rdElt`, Fmt/Rules1.lean). A value of the type `Fmt.ChainOut` that comes from a
parser outside the trusted side has passed no such reader, and the library's typing lays every word
as it comes (`PlainOf.ofGots`, Run/PlanQTypes.lean). So a check on such a value that is to refuse
what the readers refuse makes this test itself.

Main definitions.
  `okRoundOut`: every item of the round's message passes `okGot` (OnBytes/Maker/OkView.lean), and
    every word of every column of every opening of the round is below p.
  `okOut`: every round passes.

p is the prime of the program's field (`okF`, OnBytes/Field/Word.lean), whatever field a chain's
parameters name: at a chain whose parameters name the first field, whose prime is smaller, the
readers refuse more than this test. OnBytes/Maker/OkView.lean has the like test on a view;
OnBytes/ShellOf/EntryBody.lean [not in this library] has it inside `formOf`, at a field that is a
letter, by a test `okGot` of its own, which also asks 32 bytes of a root: the one used here does
not.

What is not tested. The items "word" and "root". What a round draws, its nonce, its list of
positions, its message's bytes. An opening's shape, salts, given digests and vertices. The chain's
four strings and its record of vertices.
No law is stated here: OnBytes/Maker/OkOutLaws.lean, OnBytes/Maker/OkOutOfRead.lean.


-/
