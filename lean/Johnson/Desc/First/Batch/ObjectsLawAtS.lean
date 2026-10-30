-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/ObjectsLawAtS.lean: THE REAL LENS KEEPS THE TWO LAWS THAT
Johnson/Desc/First/Batch/ObjectsLaw.lean's JOINT WANTS: so the hypothesis `LensOk` of
`adds_is_madeThen` is met at the lens of the state that the proof file's first chain carries
(Johnson/Desc/First/State.lean: S; Johnson/Desc/First/Batch/AtS.lean: atS). No Mathlib.
  `addAll_next`: an adding does not turn the ledger's next free slot (at an attention segment the
      lens reads "the slots taken" off that number).
  `atS_ok : LensOk atS`.
Limits: two laws on one lens. Nothing on any run. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.ObjectsLaw
import Johnson.Desc.First.Batch.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

theorem bind_some {α β : Type} {o : Option α} {f : α → Option β} {b : β}
    (h : o.bind f = some b) : ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl, h⟩

theorem map_some {α β : Type} {o : Option α} {f : α → β} {b : β}
    (h : o.map f = some b) : ∃ a, o = some a ∧ f a = b := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl, by simpa using h⟩

theorem kapTake_next (F : Fork) (c : Nat) (x : E × Fork) (h : F.kapTake c = some x) :
    x.2.next = F.next := by
  unfold Fork.kapTake at h
  split at h
  · simp at h
  · split at h
    · obtain ⟨k, _, hk⟩ := map_some h
      rw [← hk]
    · split at h
      · obtain ⟨k, _, hk⟩ := map_some h
        rw [← hk]
      · simp at h

theorem kap_next (F : Fork) (x : E × Fork) (h : F.kap = some x) : x.2.next = F.next := by
  unfold Fork.kap at h
  obtain ⟨y, hy, hx⟩ := map_some h
  rw [← hx]
  exact kapTake_next F F.nClaim y hy

theorem push_next (F G : Fork) (w : E) (a : Aff) (h : F.push w a = some G) : G.next = F.next := by
  unfold Fork.push at h
  split at h
  · simp at h
  · simp only at h
    split at h
    · injection h with h'
      rw [← h']
    · simp at h

theorem pushRuns_next (F G : Fork) (k : E) (runs : Array Run2) (h : F.pushRuns k runs = some G) :
    G.next = F.next := by
  unfold Fork.pushRuns at h
  obtain ⟨tr, _, hG⟩ := map_some h
  rw [← hG]

theorem addClaim_next (F G : Fork) (cl : Claim) (h : addClaim F cl = some G) :
    G.next = F.next := by
  unfold addClaim at h
  obtain ⟨x, hx, h1⟩ := bind_some h
  obtain ⟨k, _, h2⟩ := bind_some h1
  obtain ⟨P, hP, h3⟩ := bind_some h2
  rw [pushRuns_next P G k cl.runs h3, push_next x.2 P k cl.form hP, kap_next F x hx]

theorem addAll_next : ∀ (cs : List Claim) (F G : Fork), addAll F cs = some G → G.next = F.next := by
  intro cs
  induction cs with
  | nil =>
    intro F G h
    simp [addAll, pure] at h
    rw [h]
  | cons c l ih =>
    intro F G h
    unfold addAll at h
    rw [List.foldlM_cons] at h
    obtain ⟨H, hH, hl⟩ := bind_some h
    rw [ih H G hl, addClaim_next F H c hH]

/-- What is owed, as the lens reads it, is never "some 0": read a second time it is the same. -/
theorem owedOf_idem (s : S) (x : S) (h : x.rowsOwed = owedOf s) : owedOf x = owedOf s := by
  unfold owedOf at *
  rw [h]
  cases hs : s.rowsOwed with
  | none => rfl
  | some n =>
    cases n with
    | zero => rfl
    | succ m => rfl

/-- **The real lens keeps the two laws.** -/
theorem atS_ok : LensOk atS where
  getSet := by
    intro t s cs G hs hG
    have hn := addAll_next cs s.F G hG
    cases hh : t.here with
    | between => simp [atS, S.link?, hh] at hs
    | fin a => simp [atS, S.link?, hh] at hs
    | mem a => simp [atS, S.link?, hh] at hs
    | lay a =>
      simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at hs
      subst hs
      simp [atS, S.link?, S.fork?, S.tl?, usedOf, S.putLink, S.putFork, hh, owedOf_idem t]
    | att a =>
      simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at hs
      subst hs
      simp at hn
      simp [atS, S.link?, S.fork?, S.tl?, usedOf, S.putLink, S.putFork, hh, owedOf_idem t, hn]
    | head a =>
      cases ho : a.opened with
      | false => simp [atS, S.link?, hh, ho] at hs
      | true =>
        cases hsl : a.slot with
        | none => simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh, ho, hsl] at hs
        | some n =>
          simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh, ho, hsl] at hs
          subst hs
          simp [atS, S.link?, S.fork?, S.tl?, usedOf, S.putLink, S.putFork, hh, ho, hsl,
            owedOf_idem t]
  setSet := by
    intro t s G H _
    cases hh : t.here with
    | between => simp [atS, S.putLink, S.putFork, hh]
    | fin a => simp [atS, S.putLink, S.putFork, hh]
    | mem a => simp [atS, S.putLink, S.putFork, hh]
    | lay a => simp [atS, S.putLink, S.putFork, hh]
    | att a => simp [atS, S.putLink, S.putFork, hh]
    | head a =>
      cases ho : a.opened with
      | false => simp [atS, S.putLink, S.putFork, hh, ho]
      | true => simp [atS, S.putLink, S.putFork, hh, ho]

end VerifiableInference.Desc.K9
