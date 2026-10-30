-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/KeepsNext.lean: a commitment of the kind K1 takes no slot of the sub-proof's ledger:
behind a yes the engine's next free slot (Fork.next) is what it was.

The one thing that a commitment writes into the engine is, for each array named, Fork.rootTaken
(OnBytes/Model/Hide.lean), by the frame of a commitment (Johnson/Top/H0/L3/Frame.lean: commitOne,
commitBehind, commitStep); and that function turns the field trees alone.

Main names:
  commitOne_next, commitAll_next, commitBehind_next, commitStep_next: on the frame's functions, at
    any sending.
  commitOwn_next: on the kind's own block of a segment's later moment.
  commitAtS_next: on that block at the carried record: a yes says that a link was open, with its
    engine F; and the next record is written out, with an engine whose next free slot is F's.

What is not claimed. That S.fork? of the next record returns that engine: that is a law of the
carried record's readers and puts (Johnson/Desc/First/State.lean), not shown here. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

theorem commitOne_next {L : LinkCtx} {F F' : Fork} {t : Nat} (h : L3.commitOne L F t = .ok F') :
    F'.next = F.next := by
  simp only [L3.commitOne] at h
  split at h <;> split at h <;> first
    | (injection h with h; subst h; rfl)
    | cases h

theorem commitAll_next {L : LinkCtx} : ∀ (ts : List Nat) (F F' : Fork),
    ts.foldlM (L3.commitOne L) F = .ok F' → F'.next = F.next
  | [], F, F', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | t :: ts, F, F', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases h1 : L3.commitOne L F t with
    | error e => simp [h1] at h
    | ok F₁ =>
      simp only [h1] at h
      exact (commitAll_next ts F₁ F' h).trans (commitOne_next h1)

theorem commitBehind_next {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List Nat}
    (h : L3.commitBehind L check F ts = .ok (L', F')) : F'.next = F.next := by
  simp only [L3.commitBehind, bind, Except.bind] at h
  cases h1 : ts.foldlM (L3.commitOne L) F with
  | error e => simp [h1] at h
  | ok F₁ =>
    simp only [h1] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact commitAll_next ts F F₁ h1
    · cases h

theorem commitStep_next {W : Type} {send : L3.Send W} {ts : List Nat} {s s' : L3.St W}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') : s'.F.next = s.F.next := by
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
        exact commitBehind_next (L' := y.1) (F' := y.2) h2

/-- **The kind's own block of a segment's later moment takes no slot.** -/
theorem commitOwn_next {Cl : Type} {P : Par} {link moment : Nat} {arrays : Option (List Nat)}
    {x y : Owing (L3.St (DState Unit))} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (commitOwn (Cl := Cl) P link moment arrays).decide x rs gs = .ok y) :
    y.held.F.next = x.held.F.next := by
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
        exact commitStep_next h1
  · cases h

/-- **The same at the carried record.** -/
theorem commitAtS_next {Cl : Type} {P : Par} {link moment : Nat} {arrays : Option (List Nat)}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (commitAtS (Cl := Cl) P link moment arrays).decide s rs gs = .ok s') :
    ∃ L F tl y, s.link? = some L ∧ s.fork? = some F ∧ s.tl? = some tl ∧
      s' = ((laid s (y : L3.St (DState Unit)).w).putLink y.L).putFork y.F ∧ y.F.next = F.next := by
  simp only [commitAtS] at h
  split at h
  · rename_i L F tl hL hF ht
    cases h1 : (commitOwn (Cl := Cl) P link moment arrays).decide
        { owed := owedOf s, held := { L := L, F := F, tl := tl, w := stateOf s () } } rs gs with
    | error e => simp [h1, Except.map] at h
    | ok y =>
      simp only [h1, Except.map, Except.ok.injEq] at h
      exact ⟨L, F, tl, y.held, hL, hF, ht, h.symm, commitOwn_next h1⟩
  · cases h

end VerifiableInference.Desc.K1
