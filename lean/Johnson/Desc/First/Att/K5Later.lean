-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5Later.lean: the law of kind K5 at a later ledger. A form over slots is
worth the
sum of c_j (shown_j - factor_j · mask_j), and what was shown and the factor stand in the ledger: so
a
claim is judged at the ledger as it stands when the claims are gathered, behind other kinds' steps.

Main names:
  `Said.mono`: all that the hearing's law says of the ledger behind the hearing it says of every
    ledger
    in which what is filled has stayed (Stays).
  `later_stays`: the library's Later gives Stays.
  `runs_leave`: the kind's three runs of claims "first", "keys", "second" hand the carried record
    back
    unturned where they return. (The fourth, "join": Att/K5Join.lean.)

Sources: OnBytes/Tie/Pv/Psc/PscLater.lean (Later); PscFork.lean (Filled).
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Psc.PscLater
import Johnson.Desc.First.Att.K5SaidAll
import Johnson.Desc.First.Att.RunsK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (named)

/-- **What the hearing's law says of the ledger behind the hearing, it says of every later ledger.**
-/
theorem Said.mono {x : Params.AttentionRounds} {h : Heard} {G G' : Fork} {L : Lists} (a : Said x h G L)
    (s : Stays G G') : Said x h G' L :=
  { a with
    planes := a.planes.mono s, units := a.units.mono s, p5 := a.p5.mono s, pI := a.pI.mono s, p2 := a.p2.mono s
    sE := a.sE.mono s, pC := a.pC.mono s, sM := a.sM.mono s, sVD := a.sVD.mono s, pM := a.pM.mono s
    sF := a.sF.mono s, sD := a.sD.mono s, sH := a.sH.mono s }

theorem later_stays {F G : Fork} (h : OnBytes.PscRun.Later F G) : Stays F G := fun j y f p => by
  obtain ⟨a1, a2, a3⟩ := h.keep j p.1
  exact ⟨a1, by rw [a2]; exact p.2.1, by rw [a3]; exact p.2.2⟩

/-- **K5's runs of claims leave the carried record.** -/
theorem runs_leave {S : Type} (seat : SeatC S) (c : ParC) (name : String)
    (run : Nat → S → Except String (List Aff × S)) (hm : (name, run) ∈ runsK seat c) (n : Nat) (s s' : S)
    (l : List Aff) (h : run n s = .ok (l, s')) : s' = s := by
  simp only [runsK, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hm
  rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · simp only [firstK, Option.bind_eq_bind] at h
    cases h1 : inOf seat c s with
    | none => simp [h1, named] at h
    | some i =>
      cases h2 : Runs.firstRun i.1 i.2 with
      | none => simp [h1, h2, named] at h
      | some q =>
        simp [h1, h2, named] at h
        exact h.2.symm
  · simp only [keysK] at h
    cases h1 : keysOfK seat c s with
    | none => simp [h1, named] at h
    | some i =>
      simp [h1, named] at h
      exact h.2.symm
  · simp only [secondK, Option.bind_eq_bind] at h
    cases h1 : inOf seat c s with
    | none => simp [h1, named] at h
    | some i =>
      cases h2 : Runs.secondRun i.1 i.2 with
      | none => simp [h1, h2, named] at h
      | some q =>
        simp [h1, h2, named] at h
        exact h.2.symm

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.Said.mono
#print axioms VerifiableInference.Desc.First.Att.P.later_stays
#print axioms VerifiableInference.Desc.First.Att.P.runs_leave
