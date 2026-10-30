-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/BehindHands.lean: what the state that the member leaves holds.
The sentence `OneQ` (Honest/K3/Law/MemberOne.lean) speaks of what was heard and the ledger at the
state s' that the seated decision leaves; the member leaves the state t behind the step without a
round. Here: what the seat reads at t. Conditional on `QuietBehind` or `OneQ`. Theorems.

Terms. Honest/K3/GLOSSARY.md ("heard structure", "ledger", "member", "seat", "step without a
round").

What is shown.
  `putFork_fork`, `putFork_tl`, `putFork_lookHeard`: writing a ledger: the ledger is read back; the
    two structures of what was heard stay. (`putFork_tl` is the first half of the library's theorem
    of that short name, Johnson/Desc/K1/Law/TlAtRecord.lean.)
  `heard_congr`: what a seat reads as heard depends on these two structures alone.
  `quietDigits_spec`: an acceptance by the step behind the digits: the ledger with the plan's number
    of claims written in.
  `quietHead_hands`: an acceptance by the step behind the head's digits changes neither the ledger
    nor what was heard.
  `behind_hands`: so at t the seat reads what it read as heard at s', and the ledger that it read at
    s' but for the plan's number of claims.
  `oneQ_hands`: `OneQ`, said of t.

Hypotheses that remain. `hB`: `QuietBehind` (in `behind_hands`, with `a2`: the seat reads a ledger
at s'); `hQ`: `OneQ` (in `oneQ_hands`); both are defined in MemberOne.lean. `h`: the state has a
ledger (in `putFork_fork`); the step without a round accepts (in `quietDigits_spec`,
`quietHead_hands`). `h1`, `h2`: (in `heard_congr`) the two structures are the same at the two
states.

Users. This file is imported by Honest/K3/Law/Thread/MemberBack.lean,
Honest/K3/Law/Thread/OutSite.lean and Honest/K3/Law/Thread/StandsBehind.lean.

Limits. Nothing is said on whether a step accepts.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.K3 (HeardV toHeard toHeardG quietAt quietHead quietLook quietDigits)
open VerifiableInference.Desc.First.Look (slotsTaken)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## Writing a ledger -/

/-- Where a ledger is open, the ledger that is written is read back. Conditional on an open ledger.
-/
theorem putFork_fork (s : FS) {F : Fork} (G : Fork) (h : s.fork? = some F) :
    (s.putFork G).fork? = some G := by
  unfold VerifiableInference.Desc.First.S.fork? at h
  cases hh : s.here with
  | lay a => simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.fork?,
    hh]
  | att a => simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.fork?,
    hh]
  | head a =>
    rw [hh] at h
    by_cases ho : a.opened = true
    · simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.fork?, hh,
        ho]
    · simp [ho] at h
  | between => rw [hh] at h; cases h
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

/-- Writing a ledger leaves the structure of the smallness test as it is. -/
theorem putFork_tl (s : FS) (G : Fork) : (s.putFork G).tl? = s.tl? := by
  cases hh : s.here with
  | head a =>
    by_cases ho : a.opened = true <;>
      simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.tl?, hh, ho]
  | _ => simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.tl?, hh]

/-- Writing a ledger leaves what the lookup on the calls heard as it is. -/
theorem putFork_lookHeard (s : FS) (G : Fork) : (s.putFork G).lookHeard? = s.lookHeard? := by
  cases hh : s.here with
  | head a =>
    by_cases ho : a.opened = true <;>
      simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.lookHeard?,
        hh, ho]
  | _ =>
    simp [VerifiableInference.Desc.First.S.putFork, VerifiableInference.Desc.First.S.lookHeard?, hh]

/-! ## The steps without a round -/

/-- **An acceptance by the step behind the digits.** Conditional on that acceptance. -/
theorem quietDigits_spec (used claims : Nat) (s t : FS) (h : quietDigits used claims s = .ok t) :
    ∃ G, s.fork? = some G ∧ G.next = used ∧ t = s.putFork { G with planClaimsF := claims } := by
  unfold quietDigits at h
  cases hF : s.fork? with
  | none => simp [hF, named, bind, Except.bind] at h
  | some F =>
    by_cases hn : (F.next == used) = true
    · simp [hF, hn, slotsTaken, named, bind, Except.bind, pure, Except.pure] at h
      exact ⟨F, rfl, by simpa using hn, h.symm⟩
    · simp [hF, hn, slotsTaken, named, bind, Except.bind] at h

/-- **An acceptance by the step behind the head's digits changes neither the ledger nor what was
heard.** Conditional on that acceptance. -/
theorem quietHead_hands (X : OnBytes.Model.Verify.Public) (s t : FS) (h : quietHead X s = .ok t) :
    t.fork? = s.fork? ∧ t.tl? = s.tl? ∧ t.lookHeard? = s.lookHeard? := by
  unfold quietHead at h
  split at h
  · rename_i a ha
    simp only [bind, Except.bind] at h
    repeat' split at h
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq] at h
         rw [← h]
         simp [VerifiableInference.Desc.First.S.fork?, VerifiableInference.Desc.First.S.tl?,
           VerifiableInference.Desc.First.S.lookHeard?, ha])
      | cases h
  · cases h

/-! ## At the state that the member leaves -/

/-- What a seat reads as heard depends on the two structures alone.
Conditional on the two structures being the same. -/
theorem heard_congr {Cl : Type} (claim : Aff → Cl) (d : Bool) {s t : FS} (h1 : t.tl? = s.tl?)
    (h2 : t.lookHeard? = s.lookHeard?) : (seatOf claim d).heard t = (seatOf claim d).heard s := by
  cases d with
  | false => exact h2
  | true =>
    show t.tl?.bind (·.heard) = s.tl?.bind (·.heard)
    rw [h1]

/-- **At the state behind the step without a round the seat reads the same as heard, and the same
ledger but for the plan's number of claims.** Conditional on `QuietBehind` and on the ledger that
the seat reads in front of the step. -/
theorem behind_hands {Cl : Type} (claim : Aff → Cl) {X : OnBytes.Model.Verify.Public} {i : Nat}
    {d : Bool}
    {s' t : FS} {G : Fork} (hB : QuietBehind X i d s' t) (a2 : (seatOf claim d).fork s' = some G) :
    (seatOf claim d).heard t = (seatOf claim d).heard s' ∧
      ∃ c, (seatOf claim d).fork t = some { G with planClaimsF := c } := by
  have a2' : s'.fork? = some G := by cases d <;> exact a2
  have key : t.tl? = s'.tl? ∧ t.lookHeard? = s'.lookHeard? ∧
      ∃ c, t.fork? = some { G with planClaimsF := c } := by
    unfold QuietBehind at hB
    cases hq : quietAt X i d with
    | none =>
      rw [hq] at hB
      have e : t = s' := hB
      rw [e]
      exact ⟨rfl, rfl, G.planClaimsF, a2'⟩
    | some f =>
      rw [hq] at hB
      have hB' : f s' = .ok t := hB
      have dig : ∀ used claims, f = quietDigits used claims →
          t.tl? = s'.tl? ∧ t.lookHeard? = s'.lookHeard? ∧
            ∃ c, t.fork? = some { G with planClaimsF := c } := by
        intro used claims e
        rw [e] at hB'
        obtain ⟨G1, g1, _, rfl⟩ := quietDigits_spec _ _ s' t hB'
        obtain rfl : G1 = G := Option.some.inj (g1.symm.trans a2')
        exact ⟨putFork_tl _ _, putFork_lookHeard _ _, _, putFork_fork s' _ a2'⟩
      unfold quietAt at hq
      dsimp only at hq
      by_cases hH : VerifiableInference.Desc.K3.isHead X i = true
      · rw [if_pos hH] at hq
        cases d with
        | false =>
          rw [if_neg (by simp)] at hq
          cases hq
        | true =>
          rw [if_pos rfl] at hq
          obtain rfl := Option.some.inj hq
          obtain ⟨k1, k2, k3⟩ := quietHead_hands X s' t hB'
          exact ⟨k2, k3, G.planClaimsF, k1.trans a2'⟩
      · rw [if_neg hH] at hq
        generalize (if X.p4 = true then 2 else 1) = st at hq
        by_cases hm : (i % st == 0) = true
        · rw [if_pos hm] at hq
          cases d with
          | true =>
            rw [if_pos rfl] at hq
            obtain ⟨hp, _, e⟩ := Option.map_eq_some_iff.1 hq
            exact dig _ _ e.symm
          | false =>
            rw [if_neg (by simp)] at hq
            obtain rfl := Option.some.inj hq
            rw [quietLook_keeps _ s' t hB']
            exact ⟨rfl, rfl, G.planClaimsF, a2'⟩
        · rw [if_neg hm] at hq
          cases d with
          | true =>
            rw [if_pos rfl] at hq
            obtain ⟨a, _, e⟩ := Option.map_eq_some_iff.1 hq
            exact dig _ _ e.symm
          | false =>
            rw [if_neg (by simp)] at hq
            cases hq
  obtain ⟨k1, k2, c, k3⟩ := key
  refine ⟨heard_congr claim d k1 k2, c, ?_⟩
  cases d <;> exact k3

/-- **`OneQ`, said of the state t that the member leaves**: the seat reads there the
program's structure of what was heard, and the ledger behind the hearing but for the plan's number
of claims; and t bears the mark that stood in front. Conditional on `OneQ`. -/
theorem oneQ_hands {Cl : Type} (claim : Aff → Cl) {X : OnBytes.Model.Verify.Public} {i : Nat}
    {d : Bool}
    {h : Shape} {s t : FS} {g : HeardV} {G : Fork} (hQ : OneQ claim X i d h s t g G) :
    ∃ g' c, toHeard h (toHeardG g) = some g' ∧ (seatOf claim d).heard t = some g' ∧
      (seatOf claim d).fork t = some { G with planClaimsF := c } ∧ t.failed = s.failed := by
  obtain ⟨g', s', hg, a1, a2, a3, hB⟩ := hQ
  obtain ⟨k1, c, k2⟩ := behind_hands claim hB a2
  exact ⟨g', c, hg, k1.trans a1, k2, (behind_keeps hB).2.trans a3⟩

#print axioms ProofFile.Honest.K3.Law.putFork_fork
#print axioms ProofFile.Honest.K3.Law.putFork_tl
#print axioms ProofFile.Honest.K3.Law.putFork_lookHeard
#print axioms ProofFile.Honest.K3.Law.quietDigits_spec
#print axioms ProofFile.Honest.K3.Law.quietHead_hands
#print axioms ProofFile.Honest.K3.Law.heard_congr
#print axioms ProofFile.Honest.K3.Law.behind_hands
#print axioms ProofFile.Honest.K3.Law.oneQ_hands

end ProofFile.Honest.K3.Law
