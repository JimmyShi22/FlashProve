-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/QuietRides.lean: «THE TABLE's PROMISE AND "NO MARK" RIDE OVER A BLOCK's
YES» (`onT … k a` gives `onT … (k + 1) b`), AT A ROW THAT CLOSES AND OPENS NO CLASS OF ROWS AND NO
PIN, PARTED IN TWO LISTS: WHAT IS ASKED OF THE TWO RECORDS, AND WHAT IS ASKED OF THE MEANING's
LETTERS. Two lists and a theorem: a call of Johnson/Desc/Sound/PromiseRidesQ.lean's
`onQ_step_quiet`.

Why. With the four conditions of a link's pieces closed at the table's own promise
(LinkTiedAt.lean), the law's premises «a yes hands the condition on» are this sentence. Three of the
batching kind's and the frame's four blocks in a link have such a row: the batching, the frame's
block behind it, the shutting.

What is said.
  `RecRides links pl Nm k a b`: of the records: the mark, the statement and the book are as they
    were; the record behind has the shape that the table asks at the next boundary; the plan counts
    as many trees and messages at the two places. `MgRides …`: of the meaning's letters, each at the
    two records: «decodes», «in order», the public items (those that the row makes among them), what
    they say beside their Bool, «held», «shown», «no collision» (the last three and «decodes» read
    the oracles in front and behind: that these blocks send none is not spent here). `onT_rides`:
    **the two lists give the sentence.**

Limits. A RULE: it pays nothing by itself. `MgRides` can be paid only at a filling of the table's
letters. At the one equation's row (it opens a class of rows): nothing. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTiedAt
import Johnson.Desc.Sound.PromiseRidesQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start rowOf openSets pubSets pubRowM
  pubStep stepOpen quietRow shapeAt pubHeld sampledIn bookAt)

variable {P W : Type} {F : Frame}

/-- **WHAT IS ASKED OF THE TWO RECORDS.** -/
structure RecRides (Nm : Numbers) (links : List ModelPart) (pl : List Place) (k : ℕ)
    (a b : S × F.E.Str) : Prop where
  /-- the mark is as it was: so a mark stays, and no new mark is laid -/
  failed : b.1.failed = a.1.failed
  /-- the statement is as it was -/
  st : b.1.st = a.1.st
  /-- the book is as it was -/
  book : b.1.book = a.1.book
  /-- the record behind has the shape that the table asks at the next boundary -/
  shape : shapeAt links pl[k + 1]? b.1 = true
  /-- the plan counts as many trees at the two places -/
  trees : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?
  /-- and as many messages -/
  msgs : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?

/-- **WHAT IS ASKED OF THE MEANING's LETTERS**, at the two records, beside the public part z. -/
structure MgRides (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k : ℕ) (p : Place) (a b : S × F.E.Str) : Prop where
  dec : Mg.decodes (z, a.1) (strsOf F a.2) → Mg.decodes (z, b.1) (strsOf F b.2)
  inOrder : Mg.inOrder (z, a.1) = true → Mg.inOrder (z, b.1) = true
  pub : pubHeld Mg ((openSets links pl (start links))[k]?.getD [])
      ((pubSets Mg.more links pl)[k]?.getD []) (z, a.1) = true →
    pubHeld Mg (stepOpen ((openSets links pl (start links))[k]?.getD []) (rowOf links p))
      (pubStep ((pubSets Mg.more links pl)[k]?.getD []) (pubRowM Mg.more links p)) (z, b.1) = true
  pubP : (∀ q ∈ (pubSets Mg.more links pl)[k]?.getD [], Mg.pubP q (z, a.1)) →
    ∀ q ∈ pubStep ((pubSets Mg.more links pl)[k]?.getD []) (pubRowM Mg.more links p),
      Mg.pubP q (z, b.1)
  held : ∀ x ∈ sampledIn Nm ((openSets links pl (start links))[k]?.getD []),
    Mg.held x.1 x.2 (z, a.1) = true → Mg.held x.1 x.2 (z, b.1) = true
  shown : ∀ x ∈ sampledIn Nm ((openSets links pl (start links))[k]?.getD []),
    Mg.shown x.1 x.2 (strsOf F a.2) → Mg.shown x.1 x.2 (strsOf F b.2)
  noColl : ∀ x ∈ sampledIn Nm ((openSets links pl (start links))[k]?.getD []),
    Mg.noColl x.1 x.2 (z, a.1) (strsOf F a.2) → Mg.noColl x.1 x.2 (z, b.1) (strsOf F b.2)

/-- **THE PROMISE AND «NO MARK» RIDE OVER A QUIET ROW.** -/
theorem onT_rides (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k : ℕ) (p : Place) (hp : pl[k]? = some p) (hq : quietRow (rowOf links p) = true)
    (a b : S × F.E.Str) (R : RecRides Nm links pl k a b) (M : MgRides Nm Mg links pl z k p a b)
    (ha : onT Nm Mg links pl (fun s : S => (z, s)) k a) :
    onT Nm Mg links pl (fun s : S => (z, s)) (k + 1) b := by
  refine ⟨onQ_step_quiet Nm Mg links pl (fun s : S => (z, s)) k p hp hq a b ha.1 ?_ M.dec
    (fun _ => R.shape) ?_ ?_ M.inOrder (fun _ => M.pub) (fun _ hb => ?_) (fun _ => M.pubP) M.held
    M.shown M.noColl, ?_⟩
  · intro h
    show b.1.failed ≠ none
    rw [R.failed]
    exact h
  · show b.1.st.groups = a.1.st.groups
    rw [R.st]
  · show b.1.book.place = a.1.book.place
    rw [R.book]
  · have hb' : bookAt Nm pl[k]? a.1 = true := hb
    show bookAt Nm pl[k + 1]? b.1 = true
    unfold bookAt at hb' ⊢
    rw [R.book, R.st, R.trees, R.msgs]
    exact hb'
  · show ¬ b.1.failed ≠ none
    rw [R.failed]
    exact ha.2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.onT_rides
