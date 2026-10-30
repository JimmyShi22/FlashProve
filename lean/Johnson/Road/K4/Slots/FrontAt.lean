-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Slots/FrontAt.lean: `hs_front` AND `front_there` WITH THEIR THREE PREMISES ON THE
LOOKUP's RECORD SAID WHERE THE LOOKUP's FILES CAN PAY THEM: at the record fo that K4's hearing is
handed, at the ledger F at which the hearing is called, and in the library's own word `Fo.FilledA`
(OnBytes/Tie/Pv/Lookup/Forest/FoEv.lean: every slot that the form names is there and filled).
Statements and proofs: HearFills.lean and RunsThere.lean called; `own_fo`;
`hearFl_later` (OnBytes/Desc/First/K4/HearGrows.lean).

  `LookFilled rows fo F`: the three premises: the lookup's own claims (if they are listed), the slot
    of its bit, its leaves' sumcheck's start form: each `Fo.FilledA F`.
  `hs_front_at`: `hs_front` under `LookFilled rows fo F`.
  `front_there_at`: `front_there` under `LookFilled rows fo F`.

Limits. `LookFilled` IS A PREMISE: nothing here shows it. (As reported, not shown here,
`PadNames fo F'` at the ledger F' behind the lookup's hearing has these three among its four fields
and passes to every later ledger; PadNamed.lean is not imported here, and that fo and F are what the
lookup's block left is the description's wiring: not said here.) One direction. Nothing on
soundness.
-/
import Johnson.Road.K4.Slots.RunsThere

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.PscRun (Sized Filled)

/-- The three premises on the lookup's record, at a ledger. -/
structure LookFilled (rows : Bool) (fo : Forest.Heard) (F : Fork) : Prop where
  rows : rows = true → ∀ f ∈ fo.rows.toList, _root_.Fo.FilledA F f
  sBit : _root_.Fo.FilledA F (Aff.slot fo.sBit)
  start : _root_.Fo.FilledA F fo.leaves.start

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G U Gr F₁ : Fork}
  {t0 u : Tape} {rows : Bool}

/-- What is filled where the hearing is called is filled where it ends. -/
theorem hear_keeps (h : hear engFl P hp g fo F t0 = some (o, G, u)) :
    ∀ j, Filled F j → Filled G j := fun j hj =>
  ((hearFl_later (P := P) (hp := hp) (g := g) (fo := fo) h).keep j hj).1

/-- The three premises of `hs_front`, at a ledger that keeps what F has filled. -/
theorem LookFilled.at_ (N : LookFilled rows fo F) (e : o.H.fo = fo)
    (hU : ∀ j, Filled F j → Filled U j) :
    (rows = true → ∀ f ∈ o.H.fo.rows.toList, SlotsIn (Filled U) f) ∧ Filled U o.H.fo.sBit ∧
      SlotsIn (Filled U) o.H.fo.leaves.start := by
  rw [e]
  refine ⟨fun hr f hf x hx => hU _ (N.rows hr f hf x hx).2, hU _ ?_,
    fun x hx => hU _ (N.start x hx).2⟩
  exact (N.sBit (fo.sBit, oneE) (by simp [Aff.slot])).2

/-- **`hs_front`, its premises at the handed record and the ledger in front.** -/
theorem hs_front_at (hF : Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hU : ∀ j, Filled G j → Filled U j) (N : LookFilled rows fo F) (sh : Array E)
    {pp : Aff × List Aff} (hpp : planesParts o.v o.H.fo = some pp) {l : List Aff}
    (hl : front rows P g o (o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {})
      (o.H.fo.leaves.rowForm oneE pp.1) = some l) :
    ∀ f ∈ l, ∀ x ∈ f.slots.toList, SFront o U x.1 := by
  obtain ⟨a, b, c⟩ := N.at_ (own_fo h) fun j hj => hU j (hear_keeps h j hj)
  exact hs_front hF h hU a b c sh hpp hl

/-- **`front_there`, its premises at the handed record and the ledger in front.** -/
theorem front_there_at (hF : Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hG : ∀ j, Filled G j → Filled Gr j) (sG : Sized Gr) {fs : Array Aff}
    (hr : formsFrontWith rows P g o Gr = some (fs, F₁)) (N : LookFilled rows fo F) :
    ∀ f ∈ fs.toList, SlotsIn (Filled F₁) f := by
  obtain ⟨a, b, c⟩ := N.at_ (own_fo h) fun j hj => hG j (hear_keeps h j hj)
  exact front_there hF h hG sG hr a b c

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.hs_front_at
#print axioms OnBytes.Desc.First.K4.Slots.front_there_at
