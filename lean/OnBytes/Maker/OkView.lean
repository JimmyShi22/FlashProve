-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OkView.lean: the test that every word of a field's element in a chain's view is below
the prime, and the like test on the seeds of a table's key. Definitions alone.

Why. The verifier program's readers return a word of a field's element only if it is below the
field's prime (`Fmt.rdElt`, Fmt/Rules1.lean): so in the items of a prover's message
(`Fmt.readItem`, Fmt/Rules8.lean) and in the opened columns (`Fmt.rdOpening`, Fmt/Rules7.lean). A
view (Fmt/View.lean) holds machine words, and a view that is made of a typed transcript has passed
no reader. The field's operations on words (OnBytes/Field/Word.lean, OnBytes/Field/Ext.lean) count a
word that is not below p as its residue, but `isZeroE` compares the words themselves with 0 (and a
few tests of equality compare words with words: these can only refuse such a word). So a
decision on views that is to refuse such a word, as the readers do, has to make this test itself.

Main definitions.
  `okGot`: an item as read. The items "f", "e" and "answer" hold elements: each word is below p
    (`okF`, `okE`). The items "word" and "root" hold no element of a field: no test, as in the
    readers.
  `okView`: every item of every round passes `okGot`, and every word of every opened column is
    below p: the columns of the chain's own trees, of trees taken over, and of the stored table.
  `okSeeds`: every word of the point and of the factor of every seed of a table's key
    (`TableKey`, OnBytes/Iop/Foldeq.lean) is below p. The program draws a seed's words below the
    prime (`Fmt.drawSeed`); a key that is a letter has passed no draw.

p is the prime of the program's field, the second of the format's two (`Fmt.Fld.two`;
`okF_eq`, OnBytes/Field/WordEq.lean), whatever field a chain's parameters name. At a chain whose
parameters name the first field, whose prime is smaller, the readers refuse more than this test.

What is not tested here, and where it is met.
  What a round draws (`Fmt.RoundView.drawn`): no prover's word; BUT A BLOCK READS IT RAW: the test that a
    drawn seed's factor is not zero (OnBytes/Iop/Send.lean) compares the drawn words themselves with
    0, so at a view that is a letter a drawn factor (p, 0, 0) passes this file's tests and that one.
    Where the draws are made by the format's rule (`Fmt.drawRound`) a word is taken only if it is
    below the prime of the field that the rule is given (by reading; `okE_drawE`, `okE_drawNZ`,
    Fmt/RecordSeedsLaws.lean, say it of two of its parts). At the
    kit of the files' own descriptions the draws are so made (`planPull_view`, Run/PlanPull.lean);
    at another kit that is its maker's matter.
  What a silent round sends: it is in no view. A file's reduction (`reductionOfWholeFile`,
    OnBytes/Maker/Whole.lean) hands it to its test `silent`, with the instance, and not to the run.
  The answers of the table's key (`TableKey.record`), that its seeds are the table's, and the
    instance. See the head of OnBytes/Maker/Decide3.lean.
  The items "word" and "root": a block receives elements, answers and roots alone
    (OnBytes/Iop/Ground.lean, `recvE`, `recvAnswer`, `recvRoot`).
No law is stated here: OnBytes/Maker/OkViewLaws.lean, OnBytes/Maker/OkWordsOfRead.lean,
OnBytes/Maker/OkSeedsOfKey.lean.


-/
import Fmt.View
import OnBytes.Iop.Foldeq

set_option autoImplicit false

namespace OnBytes.Maker

/-- The words of an item as read are below p, where the item holds an element of a field. -/
def okGot : Fmt.ItemValue → Bool
  | .f x => okF x
  | .e x => okE (E.ofTriple x)
  | .answer x => okE (E.ofTriple x)
  | .word _ => true
  | .root _ => true

/-- **Every word of a field's element in the view is below p**: in the rounds' items and in the
opened columns. -/
def okView (v : Fmt.View) : Bool :=
  (v.rounds.all fun r => r.vals.all okGot) && v.opened.all fun o => o.2.2.all okF

/-- **Every word of every seed of the key is below p**: the point's coordinates and the factor. -/
def okSeeds (key : TableKey) : Bool :=
  key.seeds.all fun x => okE x.beta && x.z.all okE

end OnBytes.Maker
