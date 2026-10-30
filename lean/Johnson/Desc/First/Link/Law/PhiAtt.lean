-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/PhiAtt.lean: WHAT ATTENTION's KIND ASKS OF THE SHARED LETTERS FOR ITS
RUNS «first», «keys», «second» (Johnson/Desc/First/Link/Law/StillRun.lean): a reader of φ, a clause
of «goes on», and what the batching's lens reads at an attention link. Small theorems.

What is said.
  `psiAtt`: a letter ψ: at an attention link what the lookup on the calls returned and what
    attention's own rounds heard, both or nothing. `psiAtt_at`: it reads them. `rests_att`: **it
    rests under the writings behind the draw** (`PhiAll.Rests`): so it may stand in the one φ's free
    field (PhiMore.lean: `rests_pair`, `more_is`).
  `goesOn_K`: **a part that goes on from a snapshot has the snapshot's width at every array.**
    `get_att`: at an attention link the ledger that the batching's lens reads is that link's own.

Limits. Tools. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.PhiMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.PhiAll
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (GoesOn Pub9 goesOn_widths)
open VerifiableInference.Desc.First (S AttOwn)

/-- What attention's runs read beside the ledger. -/
def psiAtt (s : S) : Option (Forest.Heard × First.Att.P.Heard) :=
  match s.here with
  | .att a => a.g.bind fun g => a.heard5.map fun h => (g, h)
  | _ => none

theorem psiAtt_at (s : S) (a : AttOwn) (h : s.here = .att a) :
    psiAtt s = a.g.bind fun g => a.heard5.map fun h => (g, h) := by
  unfold psiAtt
  rw [h]

/-- **It rests under the writings behind the draw.** -/
theorem rests_att (u : HTailF2) : Rests u psiAtt where
  fork := fun s F => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [psiAtt, S.putFork, ho]
    | _ => rfl
  set := fun s a => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [psiAtt, atS, S.putLink, S.putFork, ho]
    | _ => rfl
  tl := fun s _ tl' _ _ => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [psiAtt, S.putTl, ho]
    | _ => rfl
  wrote := fun s a G s' h => by
    obtain ⟨h1, rfl⟩ := h
    unfold psiAtt
    rw [h1]
  head := fun s a G h => by
    unfold psiAtt
    rw [h]

/-- **A part that goes on from a snapshot has the snapshot's width at every array.** -/
theorem goesOn_K {u : Pub9} {b : K9.Part} (h : GoesOn u b) (k : ℕ) :
    (b.F.trees[k]?).map (·.K) = (u.F.trees[k]?).map (·.K) := by
  have e := congrArg (fun (x : Array ℕ) => x[k]?) (goesOn_widths h)
  simpa using e

/-- At an attention link the ledger that the batching's lens reads is that link's own. -/
theorem get_att (e : S) (b : K9.Part) (a : AttOwn) (hb : atS.get? e = some b)
    (h : e.here = .att a) : b.F = a.F := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  obtain rfl : here = .att a := h
  simp only [atS, S.link?, S.fork?, S.tl?, K9.usedOf, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at hb
  rw [← hb]

end VerifiableInference.Desc.PhiAll

#print axioms VerifiableInference.Desc.PhiAll.psiAtt_at
#print axioms VerifiableInference.Desc.PhiAll.rests_att
#print axioms VerifiableInference.Desc.PhiAll.goesOn_K
#print axioms VerifiableInference.Desc.PhiAll.get_att
