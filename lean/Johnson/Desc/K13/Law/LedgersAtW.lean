--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Law/LedgersAtW.lean: AT W's COMMITMENT NO MASK ENTRY IS TAKEN.

  addRowP_ledStay, addRowsP_ledStay   a row laid on a group turns no message.
  rows_ledStay     behind W's commitment (K13.rows, Johnson/Desc/K13/Text.lean): a new group, the
                   joinings, the one row on W: LedStay (Johnson/Desc/K13/Law/LedgersStay.lean).
  atM4_ledStay     so the whole block, where the sending in it takes nothing.
  atM4_send_ledStay   at K1's sending of W.

It follows rows_keeps, rowsB_keeps and atM4_keeps (Johnson/Desc/K13/Keeps.lean) line by line: these
call, of the structure that they take, the new group, the joining and the laying of a row alone; the
structure has a field for a take too, which "the numbers stay" cannot fill.

What is not claimed. Of kind K13's batching, which takes entries. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K13.Law.LedgersStay
import Johnson.Desc.K13.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc.ChainEnd (bind_ok)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.First (S)

variable {L Cl : Type}

theorem addRowP_ledStay (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') : LedStay d.st d'.st := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ x hx => ⟨x, hx, LedSame.refl x⟩⟩
  · cases h

theorem addRowsFrom_ledStay (g : Nat) (rows : List OnBytes.Row) : ∀ (d d' : DState L),
    addRowsFrom g rows d = some d' → LedStay d.st d'.st := by
  induction rows with
  | nil =>
    intro d d' h
    simp only [addRowsFrom, Option.some.injEq] at h
    subst h
    exact LedStay.refl _
  | cons row l ih =>
    intro d d' h
    simp only [addRowsFrom] at h
    cases h1 : addRowP d g row with
    | none => simp [h1] at h
    | some e =>
      simp only [h1, Option.bind_some] at h
      exact (addRowP_ledStay d e g row h1).trans (ih e d' h)

theorem addRowsP_ledStay (d d' : DState L) (g : Nat) (rows : List OnBytes.Row)
    (h : addRowsP d g rows = some d') : LedStay d.st d'.st := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_ledStay g rows d d' h
  · cases h

/-- Messages join a group, one behind the other. -/
theorem joinAllW_ledStay (g : Nat) (l : List Nat) : ∀ (d d' : St),
    joinAll g l d = .ok d' → LedStay d.st d'.st := by
  induction l with
  | nil =>
    intro d d' h
    have := pure_ok h
    subst this
    exact LedStay.refl _
  | cons o l ih =>
    intro d d' h
    unfold joinAll at h
    obtain ⟨e, he, h⟩ := bind_ok h
    exact (joinP_ledStay d e g o false (there_ok he)).trans (ih e d' h)

/-- **Behind W's commitment**: a new group, joinings, one row: nothing is taken. -/
theorem rows_ledStay (Sh : LinShape) (claim : LinClaim) (ids : Array Nat) (d : St)
    (y : LinFirst × St) (h : rows Sh claim ids d = .ok y) : LedStay d.st y.2.st := by
  unfold rows at h
  obtain ⟨w, _, h⟩ := bind_ok h
  obtain ⟨b, hb, h⟩ := bind_ok h
  obtain ⟨d₁, h1, h⟩ := bind_ok h
  obtain ⟨d₂, h2, h⟩ := bind_ok h
  obtain ⟨split, _, h⟩ := bind_ok h
  obtain ⟨d₃, h3, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨row, _, h⟩ := bind_ok h
  obtain ⟨d₄, h4, h⟩ := bind_ok h
  have := pure_ok h
  subst this
  have g3 : LedStay d₂.st d₃.st := by
    have h3' := there_ok h3
    split at h3'
    · exact joinP_ledStay d₂ d₃ b.1 split false h3'
    · cases h3'; exact LedStay.refl _
  exact (((newGroupP_ledStay d b.2 _ _ b.1 (there_ok hb)).trans
    (joinAllW_ledStay _ _ _ _ h1)).trans (joinP_ledStay d₁ d₂ b.1 w false (there_ok h2))).trans
    (g3.trans (addRowsP_ledStay d₃ d₄ b.1 [row] (there_ok h4)))

/-- The block that lays the rows. -/
theorem rowsB_ledStay (p : Where) :
    Decides (By LedStay fun s : S => s.st) (rowsB (Cl := Cl) atS p) := by
  intro t _ _ t' h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨o, ho, h⟩ := bind_ok h
  have := pure_ok h
  subst this
  show LedStay t.st (atS.set t _).st
  rw [atS_lensSt.set t s _ (part_ok hs), ← atS_lensSt.get t s (part_ok hs)]
  exact rows_ledStay _ _ _ _ _ ho

/-- **W's commitment with the own group and the row on W behind it.** -/
theorem atM4_ledStay (p : Where) (commitW : Block S Cl)
    (hW : Decides (By LedStay fun s : S => s.st) commitW) :
    Decides (By LedStay fun s : S => s.st) (atM4 p commitW) :=
  Keeps.andThen_decides (By LedStay fun s : S => s.st) (fun _ _ _ h k => LedStay.trans h k) _ _ _ hW
    (rowsB_ledStay p)

/-- At K1's sending of W. -/
theorem atM4_send_ledStay (p : Where) (P' : K1.Par) :
    Decides (By LedStay fun s : S => s.st) (atM4 (Cl := Cl) p (K1.sendAtS P')) :=
  atM4_ledStay p _ (sendAtS_ledStay P')

end VerifiableInference.Desc.K13.Law
