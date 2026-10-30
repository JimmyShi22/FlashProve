-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/Statement.lean: FROM "THE FORM IS WORTH 0 IN THE WORLD OF THE LEDGER
BEHIND THE RUN" TO THE TABLE OF JOINTS' OWN SENTENCE ON A RUN's FORMS (`formsQ`,
Johnson/Desc/Sound/FormsQ.lean): STATEMENTS ALONE: three, each a definition of a proposition, and
one definition that they need. NOTHING IS PROVED IN THIS FILE, and none of the three is one of the
library's goals: they are lemmas' statements. The texts are the verifier's and the table's; no
prover is named.

Why. The table's sentence reads a run's forms and its late slots off the run itself, called at the
border's own state (`readerOf`, Johnson/Desc/First/Batch/ReaderOf.lean); its world reads a late slot
by what the run will lay, every other slot by the state's own ledger (`slotW`). A law on a run's
form speaks of the ledger that the run returns. At the slots that a form may name the two worlds are
one.

  `ledgerWorld`    the world whose slots are a ledger's own at a mask row, and whose entries are the
                   arrays' own rows, as the table's sentence reads them
  `FormsOfIn`      the public test `formsIn` and "each form that the reader gives is worth 0" give
                   the sentence: at every reader
  `FormsOfRun`     at a reader that is the run itself: where the run returns at the state, with a
                   ledger that is later than the state's, the public test holds, and each claim's
                   form is worth 0 in `ledgerWorld` at the ledger BEHIND the run: the sentence: AT
                   EVERY RUN
  `MergedBehind`   its case at the run "the merge" (`headMergeClaim`,
                   Johnson/Desc/First/Fork/MergeKind.lean): the premise on the value is said of
                   `Fl.pscRow`'s own return at the state's ledger, at any entries: the form names
                   none

Limits. "AT EVERY RUN" IS IDLE WHERE THE READER ANSWERS NOTHING: at a claim with runs of entries or
an index of equations, or with an entry that is no own row, the public test is false. THE VALUE IS
ASKED AT THE ARRAYS' OWN ROWS: a law that speaks at the ledger's virtual rows owes that step itself.
The reader is the run itself (`Readers.ofStates`), not the readers of a link of the description.
That the public test holds is a premise (at the merge: `merge_makes_formsIn`,
Johnson/Top/H0/MergeLaw/MergeMakesForms.lean, WHOSE OWN PREMISES IN FRONT ARE WIDER THAN WHAT THE
MERGE's DECISION AND ITS RUN ASK: the ledger has just the plan's number of slots; every slot from
the next one on is free; the mask row's seat is there). That a form is worth 0 is a premise. Nothing
on any property.
-/
import Johnson.Top.H0.MergeLaw.MergedAtLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open OnBytes (E)
open OnBytes.Model (Fork Psc Aff Reading World WsForkOut)
open OnBytes.PscRun (Later)
open OnBytes.K.Kc (Fl)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.MergeLaw (mergeStates)
open VerifiableInference.Desc.K9 (segAt? formsIn Readers RunOf)
open VerifiableInference.Desc.Sound (formsQ worldOwn dataQ MsgQ)

/-- The world whose slots are the ledger G's own at the mask row that the table's sentence reads,
and whose entries are the arrays' own rows, as that sentence reads them. a: the open segment's part.
own: the seats that may be read. rd: the witness's reader. -/
noncomputable def ledgerWorld (own : List (ℕ × ℕ)) (a : VerifiableInference.Desc.K9.Part)
    (rd : ℕ × ℕ → MsgQ) (G : Fork) : World Cb.Gl.E :=
  ⟨(G.worldOf Reading.gl (dataQ own a rd).mask fun _ _ _ => 0).slot,
    (worldOwn a [] (dataQ own a rd)).entry⟩

/-- The statement that the public test and the forms' worths give the table's sentence. Not proved
here; a lemma's statement, none of the library's goals. -/
def FormsOfIn : Prop :=
  ∀ (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S) (rd : ℕ × ℕ → MsgQ),
    formsIn Rd own piece run s = true →
    (∀ a R, segAt? s = some a → Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      f.value Reading.gl (worldOwn a R.late (dataQ own a rd)) = 0) →
    formsQ Rd own piece run s rd

/-- The statement at a reader that is the run itself. states: what the segment's sub-protocols
state; r: the run that is found under the name; it returns at s; F, G: the ledgers in front of the
run and behind it. Not proved here; a lemma's statement, none of the library's goals. -/
def FormsOfRun : Prop :=
  ∀ (states : ℕ → List (RunOf S)) (own : List (ℕ × ℕ)) (piece : ℕ) (run name : String)
    (r : ℕ → S → Except String (List Claim × S)) (s s₃ : S) (cls : List Claim) (F G : Fork)
    (a : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ),
    ((states piece).find? fun x => x.1 == run) = some (name, r) → r 0 s = .ok (cls, s₃) →
    s.fork? = some F → s₃.fork? = some G → Later F G → segAt? s = some a →
    formsIn (Readers.ofStates states) own piece run s = true →
    (∀ c ∈ cls, c.form.value Reading.gl (ledgerWorld own a rd G) = 0) →
    formsQ (Readers.ofStates states) own piece run s rd

/-- The statement at the merge's run. The state stands inside the head's link, with its ledger laid
and what the merge left; the flat text's row returns at that ledger, and the form is worth 0 in the
world of the ledger that it returns, at the mask row that the table's sentence reads and at some
entries; the form names no entry. Not proved here; a lemma's statement, none of the library's
goals. -/
def MergedBehind : Prop :=
  ∀ (own : List (ℕ × ℕ)) (s : S) (a : HeadOwn) (wo : WsForkOut)
    (a9 : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ) (ent : ℕ → ℕ → ℕ → Cb.Gl.E)
    (G : Fork) (p' : Psc),
    s.here = .head a → a.opened = true → a.wo = some wo → segAt? s = some a9 →
    (wo.p.rowForm wo.fvp {}).ents.toList = [] →
    Fl.pscRow wo.p wo.fvp {} a.F [] = some ((wo.p.rowForm wo.fvp {}, p'), G, []) →
    (wo.p.rowForm wo.fvp {}).value Reading.gl (G.worldOf Reading.gl (dataQ own a9 rd).mask ent) =
      0 →
    formsIn (Readers.ofStates (mergeStates "the merge")) own 8 "the merge" s = true →
    formsQ (Readers.ofStates (mergeStates "the merge")) own 8 "the merge" s rd

end Johnson.Desc.First.ForkMerge.Exchange
