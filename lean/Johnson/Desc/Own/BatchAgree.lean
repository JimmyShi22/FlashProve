-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/BatchAgree.lean: the batching of Johnson/Desc/Own/Batch.lean, and each of its five
steps, returns what the program `verify-on-bytes`'s function returns, at all arguments. Statements
and proofs. No block's text imports this file.
  `entryInto_agrees`, `termInto_agrees`, `runInto_agrees`, `formInto_agrees`, `rowInto_agrees`,
  `batch_agrees`.

-/
import Johnson.Desc.Own.Batch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

theorem entryInto_agrees (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (o : Nat)
    (part : Part) (index : Nat) (coeff : E) :
    addEntryTo S L x acc o part index coeff = entryInto S L x acc o part index coeff := rfl

theorem termInto_agrees (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (t : Term) :
    addTermTo S L x acc t = termInto S L x acc t := rfl

theorem runInto_agrees (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (w : Run) :
    addRunTo S L x acc w = runInto S L x acc w := rfl

theorem formInto_agrees (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow)
    (f : MainForm) : addFormTo S L x acc f = formInto S L x acc f := rfl

theorem rowInto_agrees (S : Statement) (L : GroupLayout) (row : Row) (x : E) (acc : GroupRow) :
    addToGroupRow S L row x acc = rowInto S L row x acc := rfl

theorem batch_agrees (S : Statement) (g : Nat) (input : RunInput) (x : E) :
    Bat.combine S g input x = batch S g input x := rfl

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.entryInto_agrees
#print axioms VerifiableInference.Desc.Own.termInto_agrees
#print axioms VerifiableInference.Desc.Own.runInto_agrees
#print axioms VerifiableInference.Desc.Own.formInto_agrees
#print axioms VerifiableInference.Desc.Own.rowInto_agrees
#print axioms VerifiableInference.Desc.Own.batch_agrees
