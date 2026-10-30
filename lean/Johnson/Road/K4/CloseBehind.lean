-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseBehind.lean: WHAT THE ROW OF K4 OPENS (`Behind`,
Johnson/Desc/Plain/K04Plain.lean), AT THE RECORD BEHIND A YES OF K4's BLOCK (`behindOf`,
Johnson/Road/K4/CarriageHeard.lean), TAKEN APART: the two runs start from what the hearing itself
returned. A record and one theorem. Bookkeeping.

  `SeatOk L s`: the seat's two laws at a record s: behind the three setters, in the order in which
    K4's block calls them, `L.own` finds what was laid and `L.fork` the ledger that was laid.
  `forms_of_behind`: under `SeatOk L a.1`: `Behind L Sm Lt par (behindOf L pc a τ o G) w` gives: the
    letter ctx there · lists fs₁, fs₂ and ledgers F₁, F₂ with `frontRun par o G = some (fs₁, F₁)`,
    `formsBack o F₁ = some (fs₂, F₂)`, every form of fs₁ there at F₁ and worth 0 in F₁'s world,
    every form of fs₂ there at F₂ and worth 0 in F₂'s world (`AllZero`) · the letter wo there.

Limits. `SeatOk` is a premise: at the seat `seatS` of the first chain's record it holds inside a
layers' link alone (Johnson/Desc/First/K4/SeatS.lean). Nothing is said of the letters.
-/
import Johnson.Road.K4.CarriageHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Iop
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Fork)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par Seat formsBack)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind AllZero frontRun)

variable {T Wt Cl : Type} {Fr : Frame}

/-- The seat's two laws at a record. -/
structure SeatOk (L : Seat T) (s : T) : Prop where
  own : ∀ F o, L.own (L.setOwed (L.setOwn (L.setFork s F) o) none) = some o
  fork : ∀ F o, L.fork (L.setOwed (L.setOwn (L.setFork s F) o) none) = F

/-- **What the row opens, at the record behind a yes, taken apart.** -/
theorem forms_of_behind (L : Seat T) (Sm : Sem Wt) (Lt : Letters T Wt Fr) (par : Par)
    (pc : Piece (ckP .two) Fr T Cl Wt) (a : T × Fr.E.Str) (τ : Tr (uLT (ckP .two) pc.ds))
    (o : Own) (G : Fork) (w : Wt) (hL : SeatOk L a.1)
    (hB : Behind L Sm Lt par (behindOf L pc a τ o G) w) :
    Lt.ctx (behindOf L pc a τ o G) w ∧
      (∃ fs₁ F₁ fs₂ F₂, frontRun par o G = some (fs₁, F₁) ∧ formsBack o F₁ = some (fs₂, F₂) ∧
        AllZero Sm o fs₁ F₁ w ∧ AllZero Sm o fs₂ F₂ w) ∧
      Lt.wo (behindOf L pc a τ o G) w := by
  obtain ⟨hc, ⟨o', fs₁, F₁, fs₂, F₂, ho, h1, h2, z1, z2⟩, hw⟩ := hB
  have e : o' = o := Option.some.inj (ho.symm.trans (hL.own G o))
  subst e
  have h1' : frontRun par o' G = some (fs₁, F₁) := by
    have q := h1
    rw [show L.fork (behindOf L pc a τ o' G).1 = G from hL.fork G o'] at q
    exact q
  exact ⟨hc, ⟨fs₁, F₁, fs₂, F₂, h1', h2, z1, z2⟩, hw⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.forms_of_behind
