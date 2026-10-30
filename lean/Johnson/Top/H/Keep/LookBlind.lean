--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Keep/LookBlind.lean: WHAT THE LOOKUP ON A LINK's CALLS HAS HEARD IS NOT SEEN BY FIVE
WRITINGS OF THE CARRIED RECORD; and what the lookup on the digits has heard can be read off the
smallness test's record behind any map that keeps that record's field "heard". Statements and
proofs.

OBJECT: S.lookHeard? and S.tl? (Johnson/Desc/First/State.lean); the writings S.putFork, S.putTl, the
  lens atS's set (Johnson/Desc/First/Batch/AtS.lean), and two record updates written out.
USER: nobody yet. They are typed for a record of five laws that a shared "what is fixed before the
  batching's draw" asks of a further reader of the carried record.
LETTERS: the reader fun s => s.lookHeard?; every s, F, tl, part, link's record.

Main names:
  look_putFork, look_set, look_putTl, look_lay, look_head: the five.
  digits_off: (s.tl?.map f).bind (·.heard) = s.tl?.bind (·.heard), where f keeps "heard".
  digits_putTl_not: THE CONTROL: the reader fun s => s.tl?.bind (·.heard) DOES see S.putTl: inside
    an attention link, a record with another "heard" turns it.

Limits. On the record's text alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S LayOwn AttOwn HeadOwn)
open VerifiableInference.Desc.K9 (atS)

theorem look_putFork (s : S) (G : Fork) : (s.putFork G).lookHeard? = s.lookHeard? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, S.lookHeard?, ho]
  | _ => rfl

theorem look_putLink (s : S) (L : LinkCtx) : (s.putLink L).lookHeard? = s.lookHeard? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putLink, S.lookHeard?, ho]
  | _ => rfl

theorem look_putTl (s : S) (tl : HTailF2) : (s.putTl tl).lookHeard? = s.lookHeard? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putTl, S.lookHeard?, ho]
  | _ => rfl

theorem look_set (s : S) (a : Desc.K9.Part) : (atS.set s a).lookHeard? = s.lookHeard? := by
  show ({ (s.putLink a.L).putFork a.F with st := a.d.st, rowsOwed := a.owed } : S).lookHeard? = _
  exact (look_putFork (s.putLink a.L) a.F).trans (look_putLink s a.L)

theorem look_lay (s : S) (a : LayOwn) (G : Fork) (r : Option Nat) (h : s.here = .lay a) :
    ({ s with here := .lay { a with F := G }, rowsOwed := r } : S).lookHeard? = s.lookHeard? := by
  unfold S.lookHeard?
  rw [h]

theorem look_head (s : S) (a : HeadOwn) (G : Fork) (h : s.here = .head a) :
    ({ s with here := .head { a with F := G } } : S).lookHeard? = s.lookHeard? := by
  unfold S.lookHeard?
  rw [h]

/-- What the digits' lookup has heard, off the smallness test's record behind a map. -/
theorem digits_off (f : HTailF2 → HTailF2) (hf : ∀ t, (f t).heard = t.heard) (s : S) :
    (s.tl?.map f).bind (·.heard) = s.tl?.bind (·.heard) := by
  cases s.tl? with
  | none => rfl
  | some t => exact hf t

/-- **THE CONTROL**: the digits' reader sees S.putTl. -/
theorem digits_putTl_not (s : S) (a : AttOwn) (tl : HTailF2) (h : s.here = .att a)
    (hne : tl.heard ≠ a.tl.heard) :
    (s.putTl tl).tl?.bind (·.heard) ≠ s.tl?.bind (·.heard) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .att a := h
  exact hne

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.look_set
#print axioms VerifiableInference.OnPublicFiles.look_lay
#print axioms VerifiableInference.OnPublicFiles.look_head
#print axioms VerifiableInference.OnPublicFiles.digits_off
#print axioms VerifiableInference.OnPublicFiles.digits_putTl_not
