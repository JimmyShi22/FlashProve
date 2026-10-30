-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PromiseRidesQ.lean: THE SECOND TIE AT A QUIET ROW, BY SORT OF CLAUSE: the rule of
Johnson/Desc/First/PromiseRides.lean said of the table's own promises `onQ k` and `onQ (k + 1)`. Two
theorems. A file BESIDE the table: it turns nothing of it.

Why. A block's second tie to the table (Johnson/Desc/Sound/ChainOfPromises.lean, `TiedAt`: t2) asks
the WHOLE promise behind the block. At a row that closes and opens no class of rows and no pin with
a sample it follows from the promise in front and a sentence a sort of clause.

What is said. `onQ_step_held`: ps[k]? = some p, the row at p is quiet, `onQ k a`, and: a mark stays;
"decodes" rides; the book-keeping behind; `rowsHeld` and `membersHeld` at the open set in front
ride; "in order" rides; the public items behind (at the open sets one step on); held rides, shown
and no collision ride as a pair, at the open pins' tenants: then `onQ (k + 1) b`. `onQ_step_quiet`:
the same under stronger premises (the statement's groups and the book's places whole; shown and no
collision each alone).

Limits. A rule over letters: it pays nothing by itself. The premises on the meaning's letters can be
paid only at a filling. At a row that is not quiet: nothing.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.First.PromiseRides
import Johnson.Desc.First.BordersSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers rowOf start openSets pubSets pubRowM
  pubStep stepOpen quietRow shapeAt pubHeld sampledIn rowsHeld membersHeld bookAt)

/-- **The promise one border on, at a quiet row: the least that the proof spends.** -/
theorem onQ_step_held {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k : ℕ) (p : Place)
    (hp : ps[k]? = some p) (hq : quietRow (rowOf links p) = true) (a b : A × Fr.E.Str)
    (ha : onQ N Mg links ps get k a)
    (hMark : (get a.1).2.failed ≠ none → (get b.1).2.failed ≠ none)
    (hDec : Mg.decodes (get a.1) (strsOf Fr a.2) → Mg.decodes (get b.1) (strsOf Fr b.2))
    (hShape : (get a.1).2.failed = none → (get b.1).2.failed = none →
      shapeAt links ps[k + 1]? (get b.1).2 = true)
    (hR : (get a.1).2.failed = none → (get b.1).2.failed = none →
      rowsHeld N ((openSets links ps (start links))[k]?.getD []) (get a.1).2 = true →
      rowsHeld N ((openSets links ps (start links))[k]?.getD []) (get b.1).2 = true)
    (hM : (get a.1).2.failed = none → (get b.1).2.failed = none →
      membersHeld N ((openSets links ps (start links))[k]?.getD []) (get a.1).2 = true →
      membersHeld N ((openSets links ps (start links))[k]?.getD []) (get b.1).2 = true)
    (hIn : (get a.1).2.failed = none → (get b.1).2.failed = none →
      Mg.inOrder (get a.1) = true → Mg.inOrder (get b.1) = true)
    (hPub : (get a.1).2.failed = none → (get b.1).2.failed = none →
      pubHeld Mg ((openSets links ps (start links))[k]?.getD [])
        ((pubSets Mg.more links ps)[k]?.getD []) (get a.1) = true →
      pubHeld Mg (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links p))
        (pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links p))
        (get b.1) = true)
    (hBook : (get a.1).2.failed = none → (get b.1).2.failed = none →
      bookAt N ps[k]? (get a.1).2 = true → bookAt N ps[k + 1]? (get b.1).2 = true)
    (hPP : (get a.1).2.failed = none → (get b.1).2.failed = none →
      (∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pubP q (get a.1)) →
      ∀ q ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links p),
        Mg.pubP q (get b.1))
    (hHeld : (get a.1).2.failed = none → (get b.1).2.failed = none →
      ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
        Mg.held x.1 x.2 (get a.1) = true → Mg.held x.1 x.2 (get b.1) = true)
    (hSN : (get a.1).2.failed = none → (get b.1).2.failed = none →
      ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
        Mg.shown x.1 x.2 (strsOf Fr a.2) ∧ Mg.noColl x.1 x.2 (get a.1) (strsOf Fr a.2) →
        Mg.shown x.1 x.2 (strsOf Fr b.2) ∧ Mg.noColl x.1 x.2 (get b.1) (strsOf Fr b.2)) :
    onQ N Mg links ps get (k + 1) b := by
  unfold onQ at ha ⊢
  rw [First.openSets_succ links ps (start links) k p hp,
    First.pubSets_succ Mg.more links ps k p hp]
  exact First.onAt_step_held N Mg links ps[k]? ps[k + 1]? _ _ _ (rowOf links p) (get a.1)
    (get b.1) _ _ hq ha hMark hDec hShape hR hM hIn hPub hBook hPP hHeld hSN

/-- The same under stronger premises: the statement's groups and the book's places are as they were,
whole; "shown" and "no collision" ride each alone. -/
theorem onQ_step_quiet {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k : ℕ) (p : Place)
    (hp : ps[k]? = some p) (hq : quietRow (rowOf links p) = true) (a b : A × Fr.E.Str)
    (ha : onQ N Mg links ps get k a)
    (hMark : (get a.1).2.failed ≠ none → (get b.1).2.failed ≠ none)
    (hDec : Mg.decodes (get a.1) (strsOf Fr a.2) → Mg.decodes (get b.1) (strsOf Fr b.2))
    (hShape : (get a.1).2.failed = none → shapeAt links ps[k + 1]? (get b.1).2 = true)
    (hG : (get b.1).2.st.groups = (get a.1).2.st.groups)
    (hB : (get b.1).2.book.place = (get a.1).2.book.place)
    (hIn : Mg.inOrder (get a.1) = true → Mg.inOrder (get b.1) = true)
    (hPub : (get a.1).2.failed = none →
      pubHeld Mg ((openSets links ps (start links))[k]?.getD [])
        ((pubSets Mg.more links ps)[k]?.getD []) (get a.1) = true →
      pubHeld Mg (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links p))
        (pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links p))
        (get b.1) = true)
    (hBook : (get a.1).2.failed = none → bookAt N ps[k]? (get a.1).2 = true →
      bookAt N ps[k + 1]? (get b.1).2 = true)
    (hPP : (get a.1).2.failed = none →
      (∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pubP q (get a.1)) →
      ∀ q ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links p),
        Mg.pubP q (get b.1))
    (hHeld : ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
      Mg.held x.1 x.2 (get a.1) = true → Mg.held x.1 x.2 (get b.1) = true)
    (hSh : ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
      Mg.shown x.1 x.2 (strsOf Fr a.2) → Mg.shown x.1 x.2 (strsOf Fr b.2))
    (hNc : ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
      Mg.noColl x.1 x.2 (get a.1) (strsOf Fr a.2) → Mg.noColl x.1 x.2 (get b.1) (strsOf Fr b.2)) :
    onQ N Mg links ps get (k + 1) b := by
  unfold onQ at ha ⊢
  rw [First.openSets_succ links ps (start links) k p hp, First.pubSets_succ Mg.more links ps k p hp]
  exact First.onAt_step_quiet N Mg links ps[k]? ps[k + 1]? _ _ _ (rowOf links p) (get a.1)
    (get b.1) _ _ hq ha hMark hDec hShape hG hB hIn hPub hBook hPP hHeld hSh hNc

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.onQ_step_held
#print axioms VerifiableInference.Desc.Sound.onQ_step_quiet
