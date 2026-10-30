-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/AtSLens.lean
(kind K9's soundness lemma): THEOREM: THE LENS's LAW AT THE REAL STATE: the lens
atS (Batch/AtS.lean) of the state S that the proof file's first chain carries
(Johnson/Desc/First/State.lean) meets every law of a lens that these files ask.
  atS_reads   wherever atS reads a part at all: behind a writing, it reads a part again, whose
              ledger, segment's record and statement are those written.
So the hypotheses "lens" of Law/BatchAdds.lean (Fits), Hout, GoodInEq, DoorFacts, Carry and Row3 are
paid at the real state.

-/
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.First.Batch.Law.Measure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS usedOf owedOf)
open VerifiableInference.Desc.First (S)

/-- **The lens's law at the real state.** -/
theorem atS_reads (s : S) (a : K9.Part) (h : (atS.get? s).isSome = true) :
    ∃ a', atS.get? (atS.set s a) = some a' ∧ a'.F = a.F ∧ a'.L = a.L ∧ a'.d.st = a.d.st := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => exact ⟨_, rfl, rfl, rfl, rfl⟩
  | att x => exact ⟨_, rfl, rfl, rfl, rfl⟩
  | head x =>
    by_cases ho : x.opened = true
    · cases hs : x.slot with
      | none => simp [atS, S.link?, S.fork?, S.tl?, usedOf, ho, hs] at h
      | some n => simp [atS, S.putLink, S.putFork, S.link?, S.fork?, S.tl?, usedOf, ho, hs]
    · simp [atS, S.link?, ho] at h
  | between => simp [atS, S.link?] at h
  | fin x => simp [atS, S.link?] at h
  | mem x => simp [atS, S.link?] at h

/-- The lens's own words for the indices that the smallness test's equations take, against the
function `equationsLaidF`. -/
theorem laidOf_eq (tl : HTailF2) : K9.laidOf tl = tl.equationsLaidF := rfl

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.atS_reads
#print axioms VerifiableInference.Desc.K9L.laidOf_eq
