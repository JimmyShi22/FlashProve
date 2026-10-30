-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3QuietLaws.lean: WHAT A YES OF THE STEPS BEHIND A LOOKUP SAYS
(Johnson/Desc/First/Look/K3Whole.lean: `quietLook`, `quietDigits`, `quietHead`). Small lemmas with
their proofs; without Mathlib.

Why. A place of the kind "lookup" can hold, behind the kind's rounds, a step that hears nothing. The
rule that carries the kind's law to the whole place (Johnson/Desc/Sound/MergeQuiet.lean) asks of the
step: where it returns t from s', what is promised at s' gives what is promised at t, and a witness
at t is one at s'. These lemmas say what t is.

Main names:
  `quietLook_ok`: it returns the record itself; something was heard, with the layout's seven
    numbers.
  `quietDigits_ok`: a ledger F is open, its count of slots is the planned one, and the record behind
    is the record with F's planned number of claims laid: no other field of the ledger turns.
  `quietHead_ok`: the head's link is open; the record behind is the record with the link's field
    `claim` laid: no other field turns.
  `quietDigits_fork`: the ledger behind IS F with the planned number of claims laid.
  `quietHead_claim`: which claim: `weightsClaim` at the run made of the covered positions (which
    `S.covered` returns at this record), what the head heard and its tables; the plan has one claim.
  `quietLook_failed`, `quietDigits_failed`, `quietHead_failed`: all three leave the mark as it is.

Limits: `weightsClaim`'s own text is not opened: `quietHead_claim` names its call. `putFork` drops
the value in silence where no ledger is open: not met here (`fork? = some F`): `quietDigits_fork`
says what the ledger behind is. Nothing on soundness; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Whole
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.Model

private theorem need_eq_ok (n : String) (b : Bool) (u : Unit) : need n b = .ok u ↔ b = true := by
  unfold need
  cases b <;> simp

/-- Behind the lookup on a layers' link's calls: a test alone. -/
theorem quietLook_ok (fs : Forest.Shape) (s t : First.S) (h : quietLook fs s = .ok t) :
    t = s ∧ ∃ g, s.lookHeard? = some g ∧ First.Look.sameShape g.shape fs = true := by
  have h' : (named "K3 quiet: nothing was heard" s.lookHeard?).bind (fun g =>
      (need "K3 quiet: the shape is the layout's" (First.Look.sameShape g.shape fs)).bind
        fun _ => .ok s) = .ok t := h
  obtain ⟨g, hg, h2⟩ := (Except.bind_eq_ok _ _ _).1 h'
  obtain ⟨u, hu, h3⟩ := (Except.bind_eq_ok _ _ _).1 h2
  exact ⟨(Except.ok.inj h3).symm, g, (named_eq_ok _ _ _).1 hg, (need_eq_ok _ _ _).1 hu⟩

theorem quietLook_failed (fs : Forest.Shape) (s t : First.S) (h : quietLook fs s = .ok t) :
    t.failed = s.failed := by
  rw [(quietLook_ok fs s t h).1]

/-- Behind the lookup on the digits, at a layers' or an attention link. -/
theorem quietDigits_ok (used claims : Nat) (s t : First.S) (h : quietDigits used claims s = .ok t) :
    ∃ F, s.fork? = some F ∧ F.next = used ∧ t = s.putFork { F with planClaimsF := claims } := by
  have h' : (named "K3 quiet: no sub-proof is open" s.fork?).bind (fun F =>
      (named "K3 quiet: the planned slots are taken" (First.Look.slotsTaken used claims F)).bind
        fun G => .ok (s.putFork G)) = .ok t := h
  obtain ⟨F, hF, h2⟩ := (Except.bind_eq_ok _ _ _).1 h'
  obtain ⟨G, hG, h3⟩ := (Except.bind_eq_ok _ _ _).1 h2
  have hG' := (named_eq_ok _ _ _).1 hG
  unfold First.Look.slotsTaken at hG'
  split at hG'
  · rename_i hn
    have e : G = { F with planClaimsF := claims } := (Option.some.inj hG').symm
    subst e
    exact ⟨F, (named_eq_ok _ _ _).1 hF, by simpa using hn, (Except.ok.inj h3).symm⟩
  · cases hG'

/-- `putFork` writes the link's own part alone. (The like for what it lays, `fork_put` below, stands
as `S.fork_putFork` in Johnson/Desc/First/StateLedger.lean, over a wider import.) -/
theorem putFork_failed (s : First.S) (G : Fork) : (s.putFork G).failed = s.failed := by
  unfold First.S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

private theorem fork_put (s : First.S) (F G : Fork) (h : s.fork? = some F) :
    (s.putFork G).fork? = some G := by
  unfold First.S.fork? at h
  unfold First.S.putFork
  split at h
  · simp [First.S.fork?]
  · simp [First.S.fork?]
  · split at h
    · rename_i ho
      simp [ho, First.S.fork?]
    · cases h
  · cases h

theorem quietDigits_failed (used claims : Nat) (s t : First.S)
    (h : quietDigits used claims s = .ok t) : t.failed = s.failed := by
  obtain ⟨F, -, -, rfl⟩ := quietDigits_ok used claims s t h
  exact putFork_failed s _

theorem quietDigits_fork (used claims : Nat) (s t : First.S)
    (h : quietDigits used claims s = .ok t) :
    ∃ F, s.fork? = some F ∧ t.fork? = some { F with planClaimsF := claims } := by
  obtain ⟨F, hF, -, rfl⟩ := quietDigits_ok used claims s t h
  exact ⟨F, hF, fork_put s F _ hF⟩

/-- Behind the lookup on the digits, at the head's link. -/
theorem quietHead_ok (X : Verify.Public) (s t : First.S) (h : quietHead X s = .ok t) :
    ∃ a claim, s.here = .head a ∧ a.opened = true ∧
      t = { s with here := .head { a with claim := some claim } } := by
  unfold quietHead at h
  split at h
  · rename_i a ha
    obtain ⟨u, hu, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    obtain ⟨cov, -, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    obtain ⟨x, -, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    obtain ⟨t', -, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    obtain ⟨claim, -, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    obtain ⟨u2, -, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    exact ⟨a, claim, ha, (need_eq_ok _ _ _).1 hu, (Except.ok.inj h).symm⟩
  · cases h

/-- Which claim the step at the head's link lays. -/
theorem quietHead_claim (X : Verify.Public) (s t : First.S) (h : quietHead X s = .ok t) :
    ∃ a cov x t' claim, s.here = .head a ∧ s.covered X.T X.P.h.V = .ok cov ∧ a.x = some x ∧
      a.t = some t' ∧
      First.Look.weightsClaim
        { h := X.hS, L := X.HLy, b := Verify.borderOf X.y, hp := X.H, cov := cov, x := x, t := t'
          iU3 := (X.H.tl.ix.U.getD 2 none).getD 0 } X.layers.wsLay = .ok claim ∧
      (X.H.NCL == 1) = true ∧ t = { s with here := .head { a with claim := some claim } } := by
  unfold quietHead at h
  split at h
  · rename_i a ha
    obtain ⟨u, -, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    obtain ⟨cov, hc, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    obtain ⟨x, hx, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    obtain ⟨t', ht, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    obtain ⟨claim, hcl, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    obtain ⟨u2, hn, h⟩ := (Except.bind_eq_ok _ _ _).1 h
    exact ⟨a, cov, x, t', claim, ha, hc, (named_eq_ok _ _ _).1 hx, (named_eq_ok _ _ _).1 ht, hcl,
      (need_eq_ok _ _ _).1 hn, (Except.ok.inj h).symm⟩
  · cases h

theorem quietHead_failed (X : Verify.Public) (s t : First.S) (h : quietHead X s = .ok t) :
    t.failed = s.failed := by
  obtain ⟨a, claim, -, -, rfl⟩ := quietHead_ok X s t h
  rfl

#print axioms putFork_failed
#print axioms quietHead_ok
#print axioms quietHead_claim
#print axioms quietDigits_fork
#print axioms quietDigits_failed
#print axioms quietLook_failed
#print axioms quietHead_failed
#print axioms quietLook_ok
#print axioms quietDigits_ok

end VerifiableInference.Desc.K3
