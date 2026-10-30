-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/KeepsSlots.lean: a commitment of the kind K1 leaves the slots of the sub-proof's
ledger and what lies under them as they are: behind a yes the engine has the same next free slot,
number of slots, shown scalars, factors and marks (PscRun.SlotsSame,
OnBytes/Tie/Pv/Psc/PscLater.lean). So the ledger behind is a later one (SlotsSame.later).

It is Johnson/Desc/K1/KeepsNext.lean, lemma for lemma and proof for proof, with SlotsSame in the
place of "the next free slot is what it was" (which is SlotsSame's first clause): the one thing that
a commitment writes into the engine is Fork.rootTaken, which turns the field trees alone
(rootTaken_slots).

Main names: commitOne_slots, commitAll_slots, commitBehind_slots, commitStep_slots,
commitOwn_slots, commitAtS_slots.
IS IT EMPTY HERE? Where a block refuses nothing is said. That a commitment ever says yes is not
shown here.
What is not claimed. That S.fork? of the next record returns that engine
(Johnson/Desc/First/StateLedger.lean has the puts' laws). Nothing on the arrays (trees). Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.AtS
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

theorem commitOne_slots {L : LinkCtx} {F F' : Fork} {t : Nat} (h : L3.commitOne L F t = .ok F') :
    PscRun.SlotsSame F F' := by
  simp only [L3.commitOne] at h
  split at h <;> split at h <;> first
    | (injection h with h; subst h; exact PscRun.rootTaken_slots _ _ _)
    | cases h

theorem commitAll_slots {L : LinkCtx} : ∀ (ts : List Nat) (F F' : Fork),
    ts.foldlM (L3.commitOne L) F = .ok F' → PscRun.SlotsSame F F'
  | [], F, F', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact PscRun.SlotsSame.refl _
  | t :: ts, F, F', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases h1 : L3.commitOne L F t with
    | error e => simp [h1] at h
    | ok F₁ =>
      simp only [h1] at h
      exact (commitOne_slots h1).trans (commitAll_slots ts F₁ F' h)

theorem commitBehind_slots {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List Nat}
    (h : L3.commitBehind L check F ts = .ok (L', F')) : PscRun.SlotsSame F F' := by
  simp only [L3.commitBehind, bind, Except.bind] at h
  cases h1 : ts.foldlM (L3.commitOne L) F with
  | error e => simp [h1] at h
  | ok F₁ =>
    simp only [h1] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact commitAll_slots ts F F₁ h1
    · cases h

theorem commitStep_slots {W : Type} {send : L3.Send W} {ts : List Nat} {s s' : L3.St W}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') : PscRun.SlotsSame s.F s'.F := by
  simp only [L3.commitStep, bind, Except.bind] at h
  cases h0 : L3.commitFront s.L with
  | error e => simp [h0] at h
  | ok u =>
    simp only [h0] at h
    cases h1 : send s.L.check s.w rs with
    | error e => simp [h1] at h
    | ok x =>
      simp only [h1] at h
      cases h2 : L3.commitBehind s.L x.1 s.F ts with
      | error e => simp [h2] at h
      | ok y =>
        simp only [h2, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact commitBehind_slots (L' := y.1) (F' := y.2) h2

/-- **The kind's own block of a segment's later moment leaves the slots.** -/
theorem commitOwn_slots {Cl : Type} {P : Par} {link moment : Nat} {arrays : Option (List Nat)}
    {x y : Owing (L3.St (DState Unit))} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (commitOwn (Cl := Cl) P link moment arrays).decide x rs gs = .ok y) :
    PscRun.SlotsSame x.held.F y.held.F := by
  simp only [commitOwn] at h
  split at h
  · split at h
    · cases h
    · rename_i ts
      cases h1 : L3.commitStep (laterOwn P x.owed) ts x.held rs with
      | error e => simp [h1, Except.map] at h
      | ok z =>
        simp only [h1, Except.map, Except.ok.injEq] at h
        subst h
        exact commitStep_slots h1
  · cases h

/-- **The same at the carried record.** -/
theorem commitAtS_slots {Cl : Type} {P : Par} {link moment : Nat} {arrays : Option (List Nat)}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (commitAtS (Cl := Cl) P link moment arrays).decide s rs gs = .ok s') :
    ∃ L F tl y, s.link? = some L ∧ s.fork? = some F ∧ s.tl? = some tl ∧
      s' = ((laid s (y : L3.St (DState Unit)).w).putLink y.L).putFork y.F ∧
      PscRun.SlotsSame F y.F := by
  simp only [commitAtS] at h
  split at h
  · rename_i L F tl hL hF ht
    cases h1 : (commitOwn (Cl := Cl) P link moment arrays).decide
        { owed := owedOf s, held := { L := L, F := F, tl := tl, w := stateOf s () } } rs gs with
    | error e => simp [h1, Except.map] at h
    | ok y =>
      simp only [h1, Except.map, Except.ok.injEq] at h
      exact ⟨L, F, tl, y.held, hL, hF, ht, h.symm, commitOwn_slots h1⟩
  · cases h

end VerifiableInference.Desc.K1
