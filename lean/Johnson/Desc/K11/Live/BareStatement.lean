-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Live/BareStatement.lean: THE CLAIM THAT THE RUN "the merge" STATES NAMES NO ENTRY
OF ANY ARRAY AND NO RUN OF ENTRIES: SLOTS AND A CONSTANT ALONE: WHERE THE START FORM OF WHAT THE
MERGE LEFT IS THE MERGE's OWN: one definition, and STATEMENTS: three definitions of propositions.
NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.
The texts are the description's (`headMergeDecide`, `headMergeClaim`,
Johnson/Desc/First/Fork/MergeKind.lean); no prover is named.

  `MergeBare s`            the state stands in the head's link; what the merge left is there; the
                           start form of its sumcheck is `wsForkStart` of some slots and factors
                           (OnBytes/Model/Merge.lean): a sum of slots
  `HeadMergeBareBehind`    behind a yes of the merge's decision: `MergeBare`
  `MergeBareHands`         from a state in the head's link to another whose field wo is the same:
                           `MergeBare` goes over
  `MergeRunBare`           where `MergeBare s` holds and the run returns z at s: each claim of z.1
                           has no entry in its form and no run of entries; and `MergeBare z.2`

Why the condition. The claim's form is `Psc.rowForm` (OnBytes/Model/Psc.lean), which adds the
sumcheck's target less its START under a factor: so the form's entries are the start's. AT A STATE
MADE BY HAND, WHOSE START NAMES AN ENTRY, THE CLAIM NAMES IT TOO: without a condition on the start
the last statement is false [by reading; no example is typed].

How the condition comes from behind the merge to the run. It reads of the state the head's own field
wo alone: `MergeBareHands` is the one step of that road. The run is called by the batching, behind
other kinds' runs: THAT NONE OF THESE WRITES THAT FIELD IS NOT SAID HERE: it is each run's author's.
(The condition `MergeLive`, RunStatement.lean of this folder, reads the same field; by that author's
own letter the batching's author carries it across these runs by a lemma of its own, whose premise
asks that the head's whole own part is the same.)

Limits. The yes, and that the run returns, are premises. Nothing on the slots that the form names
(RunStatement.lean has that). Nothing on any property.
-/
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Live
open OnBytes (E)
open OnBytes.Model (WsForkOut wsForkStart)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S HeadOwn)

/-- **The start form of what the merge left is the merge's own: a sum of slots.** -/
def MergeBare (s : S) : Prop :=
  ∃ (a : HeadOwn) (wo : WsForkOut) (sv : Array Nat) (rho : Array E),
    s.here = .head a ∧ a.wo = some wo ∧ wo.p.start = wsForkStart sv rho

/-- The statement behind the decision's yes. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeBareBehind : Prop :=
  ∀ (P : HeadMergeP) (s s' : S) (rs : List Fmt.RoundView), headMergeDecide P s rs = .ok s' → MergeBare s'

/-- The statement on a step that leaves the field. Not proved here; a lemma's statement, none of the
library's goals. -/
def MergeBareHands : Prop :=
  ∀ (u u' : S) (a a' : HeadOwn), u.here = .head a → u'.here = .head a' → a'.wo = a.wo →
    MergeBare u → MergeBare u'

/-- The statement on the run. n: the number of claims gathered so far, which the run does not read.
Not proved here; a lemma's statement, none of the library's goals. -/
def MergeRunBare : Prop :=
  ∀ (n : Nat) (s : S) (z : List Claim × S), MergeBare s → headMergeClaim n s = .ok z →
    (∀ cl ∈ z.1, cl.form.ents = #[] ∧ cl.runs = #[]) ∧ MergeBare z.2

end Johnson.Desc.First.ForkMerge.Live
