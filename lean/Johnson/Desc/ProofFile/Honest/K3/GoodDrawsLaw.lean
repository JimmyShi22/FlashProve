-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/GoodDrawsLaw.lean: the statement on the test of
Honest/K3/GoodDraws.lean, in the form in which the kinds' tests on their own samples are joined
(Johnson/Desc/K9/Honest/SlotsLive.lean: `liveAt_iff`, `plainAt`, `unnamedAt`). Two statements as
definitions, not proved in this file; five small theorems.

Terms. Honest/K3/GLOSSARY.md ("good samples", "sample", "window", "run (of claims): objects, guests,
planes, join"). In this file: the hearing is `hearV`, and `planesV` makes the three claims on the
planes (both Johnson/Desc/First/Look/Via/Rounds.lean).

What is defined and shown.
  `asClaims`: forms as claims that take their own numbers.
  `liveIn_eq`: the Boolean test `liveIn` on forms (GoodDraws.lean) is `liveAt` (SlotsLive.lean) on
    these claims. Proved here.
  `formsOf`: the forms of a run, made of what the hearing and `planesV` hand back.
  `canDraw`: the frame's own test on challenges, at the lookup's rounds.
  `GoodGives`: the statement. It is proved in Honest/K3/Good/Gives.lean (`goodGives`).
  `field_of`: the right side of `liveAt_iff`, word for word. Conditional on `GoodGives`. Proved
    here.
  `goodRun_of`: the whole test gives each run's test. Proved here.
  `plain_asClaims`: these claims are plain at every slot: each takes its own number. Proved here.
  `NamesOwn`: a second statement: the runs' forms name the lookup's own slots alone. It is proved in
    Honest/K3/Parts/NamesOwn.lean (`namesOwn`).
  `unnamed_of`: a slot outside the window is unnamed. Conditional on `NamesOwn`. Proved here.
The two conditional theorems without their conditions are `live_field` and `outside_unnamed`
(Honest/K3/Good/Paid.lean [not in this library]).

Hypotheses that remain.
  `H`: in `field_of`: `GoodGives`; in `unnamed_of`: `NamesOwn`.
  `hh`, `hp`: (in both) the hearing returns, and `planesV` returns behind it.
  `hd`, `hc`, `hg`, `hj`: (in `field_of`) the face has a level on the table side; `canDraw` accepts
    the rounds' samples; `goodRun f r` accepts them; the slot lies in the window of the run r.
  `hj`: (in `unnamed_of`) the slot lies below the ledger's next slot, or at or above it by the
    lookup's number of slots.
  `h`: (in `goodRun_of`) `goodK3` accepts.

The statement `GoodGives` in words. Let the face have a level on the table side. Let the rounds'
samples be such as the rounds can sample (`canDraw`: the frame's own test: above all, every word
below the prime). Let the hearing return on these rounds, from any ledger (so the face passes the
verifier's tests), and let `planesV` return behind it. Run by run: if `goodRun f r` accepts on these
rounds' samples, then each slot in the window of the run r is named, with a coefficient that is not
0, by a form of that run. So whoever states a run's claims at a place calls that run's test alone.

Why the hypothesis on the samples. The hearing's test "the sample of Y is not 0" judges the three
words. At a sample of Y whose words are (the prime, 0, 0) the hearing returns, no test on the spots
rejects, and the slots of Y in the hiding polynomial are named with the word 0: without the
hypothesis the statement is false. Honest/K3/GoodDrawsGuards.lean [not in this library] has that
run.

Is the statement empty? No: GoodDrawsGuards.lean [not in this library] (see above: not in the
library) has instances at four faces and three lists of samples each: the hearing returns, the test
accepts, and the conclusion holds there by evaluation. Can it fail? At each of the test's events,
set one by one, the conclusion fails there (but for one event at a face with few real planes).

Imported. Honest/Frame.lean lies beneath this file.

Users. `GoodGives` and `formsOf` stand in Honest/K3/Good/Gives.lean; `NamesOwn` and `formsOf` in
Honest/K3/Parts/NamesOwn.lean; `canDraw` in Honest/K3/Good/MarkEvents.lean and
Honest/K3/Good/MarkShare.lean; `liveIn_eq` is called in Honest/K3/Good/Coef.lean.

Limits. What the runs are. "objects" is the seated sub-protocol's own run. "planes" is read as
`planesV` makes it, which no seated sub-protocol calls: the seated text makes these claims of the
verifier program's structure; that both name the slots alike is not shown. "join" is the key side's
last form alone: the caller's claim scales it by factors of its own, which are the caller's to hold
away from 0. That at any two batching challenges a run's claims have the same keys needs no word on
these forms: the hearing and `planesV` are handed no batching challenge; they read of the ledger the
count of slots, what was shown and the list of debts. This is a remark by reading, not a theorem.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.GoodDraws
import Johnson.Desc.K9.Honest.SlotsLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.K3 (hearV planesV HeardV PlaneClaim)
open VerifiableInference.Desc.K9H (liveAt liveAt_iff slotCoef slotWord notZero)

/-- Forms as claims that take their own numbers. -/
def asClaims (l : List Aff) : List Claim := l.map fun a => { form := a }

/-- The Boolean test `liveIn` on forms is `liveAt` on these claims. -/
theorem liveIn_eq (l : List Aff) (j : Nat) : liveIn l j = liveAt (asClaims l) j := by
  unfold liveIn liveAt asClaims
  rw [List.any_map]
  rfl

/-- The forms of a run. -/
def formsOf (g : HeardV) (pl : List PlaneClaim) : Run → List Aff
  | .objects => g.rows.toList
  | .planes => pl.map (·.lead)
  | .join => g.keys.map (·.2)

/-- The samples are such as the lookup's rounds can sample: the frame's own test (`drawsFit`,
Honest/Frame.lean), at the rounds that the hearing goes by. Among its clauses: the counts; every
word of an element below the prime; a sample that the entry marks as never 0 is not 0. -/
def canDraw (f : LFace) (ds : List Fmt.Drawn) : Bool :=
  drawsFit ((VerifiableInference.Desc.K3.entriesV f).map fun e => { entry := e }) ds

/-- **The statement.** Proved in Honest/K3/Good/Gives.lean. -/
def GoodGives : Prop :=
  ∀ (f : LFace) (F G G' : Fork) (rs : List Fmt.RoundView) (g : HeardV) (pl : List PlaneClaim),
    1 ≤ f.d → canDraw f (rs.map (·.drawn)) = true →
    hearV f F rs = some (g, G) → planesV f g G = some (pl, G') →
    ∀ (r : Run), goodRun f r (rs.map (·.drawn)) = true →
      ∀ j ∈ windowOf f r, liveIn (formsOf g pl r) (F.next + j) = true

/-- On the field's side, in the form in which the kinds' tests are joined. Conditional on
`GoodGives`. -/
theorem field_of (H : GoodGives) (f : LFace) (F G G' : Fork) (rs : List Fmt.RoundView) (g : HeardV)
    (pl : List PlaneClaim) (hd : 1 ≤ f.d) (hc : canDraw f (rs.map (·.drawn)) = true)
    (hh : hearV f F rs = some (g, G)) (hp : planesV f g G = some (pl, G')) (r : Run)
    (hg : goodRun f r (rs.map (·.drawn)) = true) (j : Nat) (hj : j ∈ windowOf f r) :
    ∃ cl ∈ asClaims (formsOf g pl r), cl.eqFirst = none ∧
      slotCoef OnBytes.Model.Reading.gl cl (F.next + j) ≠ 0 :=
  (liveAt_iff _ _).1 ((liveIn_eq _ _).symm.trans (H f F G G' rs g pl hd hc hh hp r hg j hj))

/-- The whole test gives each run's test. -/
theorem goodRun_of (f : LFace) (ds : List Fmt.Drawn) (h : goodK3 f ds = true) (r : Run) :
    goodRun f r ds = true := by
  unfold goodK3 at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  cases r
  · exact h.1.1
  · exact h.1.2
  · exact h.2

/-- Every such claim takes its own number: so the list is plain at every slot. -/
theorem plain_asClaims (l : List Aff) (j : Nat) :
    VerifiableInference.Desc.K9H.plainAt (asClaims l) j = true := by
  unfold VerifiableInference.Desc.K9H.plainAt asClaims
  rw [List.all_map, List.all_eq_true]
  intro a _
  rfl

/-- **A second statement.** Proved in Honest/K3/Parts/NamesOwn.lean. The forms of the lookup's runs
name slots of the lookup's own window alone: so they leave every other slot, the merge's among them,
unnamed. -/
def NamesOwn : Prop :=
  ∀ (f : LFace) (F G G' : Fork) (rs : List Fmt.RoundView) (g : HeardV) (pl : List PlaneClaim),
    hearV f F rs = some (g, G) → planesV f g G = some (pl, G') →
    ∀ (r : Run), ∀ a ∈ formsOf g pl r, ∀ x ∈ a.slots.toList, F.next ≤ x.1 ∧ x.1 < F.next + f.slots

/-- A slot outside the lookup's window is named by no claim of its runs. Conditional on `NamesOwn`.
-/
theorem unnamed_of (H : NamesOwn) (f : LFace) (F G G' : Fork) (rs : List Fmt.RoundView) (g : HeardV)
    (pl : List PlaneClaim) (hh : hearV f F rs = some (g, G)) (hp : planesV f g G = some (pl, G'))
    (r : Run) (j : Nat) (hj : j < F.next ∨ F.next + f.slots ≤ j) :
    VerifiableInference.Desc.K9H.unnamedAt (asClaims (formsOf g pl r)) j = true := by
  unfold VerifiableInference.Desc.K9H.unnamedAt asClaims
  rw [List.all_map, List.all_eq_true]
  intro a ha
  show (a.slots.toList.all fun x => x.1 != j) = true
  rw [List.all_eq_true]
  intro x hx
  have h := H f F G G' rs g pl hh hp r a ha x hx
  have hne : x.1 ≠ j := by omega
  simpa using hne

#print axioms liveIn_eq
#print axioms field_of
#print axioms goodRun_of
#print axioms plain_asClaims
#print axioms unnamed_of

end ProofFile.Honest.K3
