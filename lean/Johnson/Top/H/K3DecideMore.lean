-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3DecideMore.lean: the kind "lookup" (K3): three small things that a reader of the law
`K3DecideHears` (Johnson/Top/H/K3DecideHearsAt.lean) found owed and paid by nobody. Statements and
proofs.

Main names:
  `decide_next`, `decide_first`: decide TESTS that the ledger's next free slot is the place's public
    number `p.first`; the law did not hand that on. Here it is: so the number jLK = F.next, at which
    the proved block's layout lays the lookup's mask entries, is a number of the plan.
  `calls_keeps_digits`, `digits_keeps_calls`: a link has two places of the kind, each with a seat of
    its own. What one seat's `put` lays leaves what the OTHER seat's `heard` reads as it was: so
    what was heard at the lookup on the calls outlives the lookup on the digits, and the other way
    round.
  `mark_keeps_calls`, `mark_keeps_digits`: the same of `mark`, by which the runs of claims lay a
    ledger.

Limits. On the two seats of Johnson/Desc/First/Look/K3Seat.lean and the carried record of
Johnson/Desc/First/State.lean alone. Nothing is said of any other block's steps between the two
places: that these leave what was heard is the link's frame's. Ties: no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3DecideHearsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)

/-! ## The ledger's count is the plan's number -/

/-- decide's yes: a ledger is open, its next free slot is the place's public number, and nothing is
heard yet. -/
theorem decide_next {T Cl : Type} (seat : Seat T Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest T Cl))
    (s s' : T) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ F, seat.fork s = some F ∧ F.next = p.first ∧ seat.heard s = none := by
  simp only [Desc.K3.block] at h
  rw [named_bind_ok] at h
  obtain ⟨F, hF, h⟩ := h
  rw [need_bind_ok] at h
  obtain ⟨hn, h⟩ := h
  rw [need_bind_ok] at h
  obtain ⟨-, h⟩ := h
  rw [need_bind_ok] at h
  obtain ⟨hx, -⟩ := h
  exact ⟨F, hF, by simpa using hx, Option.isNone_iff_eq_none.mp hn⟩

/-- The same, of whichever ledger the seat reads in front. -/
theorem decide_first {T Cl : Type} (seat : Seat T Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest T Cl))
    (s s' : T) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64))) (F : Fork)
    (hF : seat.fork s = some F)
    (h : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    F.next = p.first := by
  obtain ⟨F', hF', hn, -⟩ := decide_next seat piece laid before p guests s s' rs cols h
  rw [hF] at hF'
  rw [Option.some.inj hF']
  exact hn

/-! ## What a step of the record leaves -/

theorem tl_mark (s : S) (n : String) : (s.mark n).tl? = s.tl? := by
  simp only [S.tl?, Desc.K3.mark_here]

theorem lookHeard_mark (s : S) (n : String) : (s.mark n).lookHeard? = s.lookHeard? := by
  simp only [S.lookHeard?, Desc.K3.mark_here]

theorem tl_hearLook (s : S) (g : Forest.Heard) : (s.hearLook g).tl? = s.tl? := by
  cases hh : s.here with
  | between => simp [S.hearLook, hh, tl_mark]
  | fin _ => simp [S.hearLook, hh, tl_mark]
  | mem _ => simp [S.hearLook, hh, tl_mark]
  | lay a =>
    cases hl : a.lookHeard with
    | some _ => simp [S.hearLook, hh, hl, tl_mark]
    | none => simp [S.hearLook, S.tl?, hh, hl]
  | att a =>
    cases hl : a.lookHeard with
    | some _ => simp [S.hearLook, hh, hl, tl_mark]
    | none => simp [S.hearLook, S.tl?, hh, hl]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.hearLook, hh, ho, tl_mark]
    | true =>
      cases hl : a.lookHeard with
      | some _ => simp [S.hearLook, hh, ho, hl, tl_mark]
      | none => simp [S.hearLook, S.tl?, hh, ho, hl]

theorem lookHeard_putTl (s : S) (tl : HTailF2) : (s.putTl tl).lookHeard? = s.lookHeard? := by
  cases hh : s.here with
  | between => simp [S.putTl, hh]
  | fin _ => simp [S.putTl, hh]
  | mem _ => simp [S.putTl, hh]
  | lay a => simp [S.putTl, S.lookHeard?, hh]
  | att a => simp [S.putTl, S.lookHeard?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.putTl, hh, ho]
    | true => simp [S.putTl, S.lookHeard?, hh, ho]

/-! ## The two seats leave each other's hearing -/

/-- What the seat on a link's calls lays leaves what the seat on the digits reads as heard. -/
theorem calls_keeps_digits {Cl Cl' : Type} (claim : Aff → Cl) (claim' : Aff → Cl') (s : S)
    (g : Forest.Heard) (G : Fork) :
    (seatDigits claim').heard ((seatCalls claim).put s g G) = (seatDigits claim').heard s := by
  show ((s.putFork G).hearLook g).tl?.bind (·.heard) = s.tl?.bind (·.heard)
  rw [tl_hearLook, tl_putFork]

/-- What the seat on the digits lays leaves what the seat on a link's calls reads as heard. -/
theorem digits_keeps_calls {Cl Cl' : Type} (claim : Aff → Cl) (claim' : Aff → Cl') (s : S)
    (g : Forest.Heard) (G : Fork) :
    (seatCalls claim').heard ((seatDigits claim).put s g G) = (seatCalls claim').heard s := by
  show ((seatDigits claim).put s g G).lookHeard? = s.lookHeard?
  simp only [seatDigits]
  split
  · rw [lookHeard_putFork, lookHeard_putTl]
  · exact lookHeard_mark _ _

/-- A ledger that a run of claims lays, at either seat, leaves what the seat on the calls reads. -/
theorem mark_keeps_calls {Cl : Type} (claim : Aff → Cl) (s : S) (G : Fork) :
    (seatCalls claim).heard (s.putFork G) = (seatCalls claim).heard s :=
  lookHeard_putFork s G

/-- And what the seat on the digits reads. -/
theorem mark_keeps_digits {Cl : Type} (claim : Aff → Cl) (s : S) (G : Fork) :
    (seatDigits claim).heard (s.putFork G) = (seatDigits claim).heard s :=
  congrArg (fun x : Option HTailF2 => x.bind (·.heard)) (tl_putFork s G)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.decide_next
#print axioms VerifiableInference.OnPublicFiles.decide_first
#print axioms VerifiableInference.OnPublicFiles.calls_keeps_digits
#print axioms VerifiableInference.OnPublicFiles.digits_keeps_calls
