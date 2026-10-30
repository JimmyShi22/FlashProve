-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/FrontBack.lean: WHICH SLOTS THE FORMS OF K4's TWO RUNS OF CLAIMS NAME: every
slot that a form of "front" or of "back" names has S, IF S HOLDS OF THE SLOTS THAT K4's TEXT NAMES
BY NUMBER AND OF THOSE OF THE SUB-FORMS THAT THE HEARING HANDS ON. Two records of these premises,
and four theorems. The structure alone: Johnson/Road/K4/Slots/Groups.lean laid together.

  `FrontOk S rows P g o`: THE PREMISES FOR "front", by name: `k3` (the lookup's own claims, if they
    are listed) · `wplRow`, `wplL`, `wplR` (the squares' layer) · `tVCl`, `tVEnd`, `tVWin`,
    `tVStart` (the row products' token sumcheck: its claimed sum; its end values; ITS WINDOW; its
    start form) · `sPvB`, `sPv7`, `sW` (the products' stretch, twice: ledNP · NI at P.y for the
    batch, 7 · NI at o.v.y for the rows' lines; the sums' stretch) · `tT` (the second token
    sumcheck's end values) · `hdRow`, `hdL`, `hdR`, `hd2` (the gated products' two layers) · `sBit`,
    `lvWin`, `lvStart` (the lookup's bit; its leaves' sumcheck's WINDOW and start form) · `sVE` (in
    the first group: the embedding's value).
  `BackOk S o`: THE PREMISES FOR "back": `rowS` (the batched sumcheck's own claim) · `sA0`, `sB0` ·
    `Alin`, `Blin` · `mWin`, `mStart` (the merge's WINDOW and start form).
  `front_slots`: every form of `front rows P g o rowV rowL`, at the two own claims as
    `formsFrontWith` makes them (at ANY shown values sh).
  `formsFront_slots`: so every form that `formsFrontWith rows P g o F` returns.
  `back_slots`: every form of `back o rowM` at the merge's own claim.
  `formsBack_slots`: so every form that `formsBack o F` returns.

What it is for: at S j := (j lies in one of the run's windows) ∨ (j is filled in a ledger U): the
premises hs of «link for proof file»'s K4Values.lean (`back_values`, `front_values`); at
S j := (j is filled in the ledger behind the run): the slots' half of K04Plain.lean's `thereAt`.

Limits. `FrontOk` AND `BackOk` ARE PREMISES: NOTHING HERE SHOWS THAT A SLOT IS FILLED. One
direction: the forms may name fewer slots. Nothing on entries (Johnson/Road/K4/Reads/). Nothing on
soundness.
-/
import Johnson.Road.K4.Slots.Groups
import OnBytes.Desc.First.K4.ClaimsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.Model.Layer

/-- **The premises for the run "front".** -/
structure FrontOk (S : ℕ → Prop) (rows : Bool) (P : Pub) (g : ℕ) (o : Own) : Prop where
  k3 : rows = true → ∀ f ∈ o.H.fo.rows.toList, SlotsIn S f
  wplRow : SlotsIn S o.H.wpl.row
  wplL : S o.H.wpl.sL
  wplR : S o.H.wpl.sR
  tVCl : S o.H.tV.sCl
  tVEnd : ∀ j, o.H.tV.sEnd ≤ j → j < o.H.tV.sEnd + 4 * o.v.y.NI → S j
  tVWin : ∀ i, i < o.H.tV.p.walk.1.length → S (o.H.tV.p.first + i)
  tVStart : SlotsIn S o.H.tV.p.start
  sPvB : ∀ j, o.H.sPv ≤ j → j < o.H.sPv + ledNP P.y.h.xl * P.y.NI → S j
  sPv7 : ∀ j, o.H.sPv ≤ j → j < o.H.sPv + 7 * o.v.y.NI → S j
  sW : ∀ j, o.H.sW ≤ j → j < o.H.sW + 9 * o.v.y.NI → S j
  tT : ∀ tT, o.H.tT = some tT → ∀ j, tT.sEnd ≤ j →
    j < tT.sEnd + (o.v.y.NN * o.v.y.Lam + o.v.y.LamM + o.v.y.LamM * o.v.y.h.NE) → S j
  hdRow : SlotsIn S o.hd.row
  hdL : S o.hd.sL
  hdR : S o.hd.sR
  hd2 : ∀ x, o.hd2 = some x → SlotsIn S x.row ∧ S x.sL ∧ S x.sR
  sBit : S o.H.fo.sBit
  lvWin : ∀ i, i < o.H.fo.leaves.walk.1.length → S (o.H.fo.leaves.first + i)
  lvStart : SlotsIn S o.H.fo.leaves.start
  sVE : (g == 0) = true → S o.sVE

/-- **The premises for the run "back".** -/
structure BackOk (S : ℕ → Prop) (o : Own) : Prop where
  rowS : SlotsIn S o.K.rowS
  sA0 : S o.K.sA0
  sB0 : S o.K.sB0
  Alin : SlotsIn S o.K.fin.Alin
  Blin : SlotsIn S o.K.fin.Blin
  mWin : ∀ i, i < o.wo.toWsMerged.p.walk.1.length → S (o.wo.toWsMerged.p.first + i)
  mStart : SlotsIn S o.wo.toWsMerged.p.start

variable {S : ℕ → Prop}

/-- **The list of "front".** sh: any shown values. -/
theorem front_slots {rows : Bool} {P : Pub} {g : ℕ} {o : Own} (K : FrontOk S rows P g o)
    (sh : Array E) {pp : Aff × List Aff} (hpp : planesParts o.v o.H.fo = some pp) {l : List Aff}
    (h : front rows P g o (o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {})
      (o.H.fo.leaves.rowForm oneE pp.1) = some l) : ∀ f ∈ l, SlotsIn S f := by
  obtain ⟨g2, g46, g7, g89, g10, g11, g12, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := front_some h
  have hp1 := (planesParts_slots (S := S) hpp).1
  have hq2 := (planesParts_slots b6).2 K.sBit
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_append.mp hf with hf | hf
      · rcases List.mem_append.mp hf with hf | hf
        · rcases List.mem_append.mp hf with hf | hf
          · rcases List.mem_append.mp hf with hf | hf
            · rcases List.mem_append.mp hf with hf | hf
              · rcases List.mem_append.mp hf with hf | hf
                · cases rows with
                  | true => exact K.k3 rfl f hf
                  | false => cases hf
                · exact normsForms_slots b1 K.wplRow K.wplL K.wplR f hf
              · rcases List.mem_cons.mp hf with rfl | hf
                · exact rowBatchForm_slots _ _ K.tVCl K.sPvB
                rcases List.mem_cons.mp hf with rfl | hf
                · exact slotsIn_rowForm _ _ K.tVWin K.tVStart slotsIn_empty
                cases hf
            · exact rowsForms_slots b2 K.tVEnd K.sW K.sPv7 f hf
          · exact termsForms_slots b3 K.tT f hf
        · exact gatedForms_slots b4 K.hdRow K.hdL K.hdR K.hd2 f hf
      · exact oneHotForms_slots b5 f hf
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact slotsIn_rowForm _ _ K.lvWin K.lvStart hp1
      · exact hq2 f hf
  · by_cases hg : (g == 0) = true
    · rw [if_pos hg] at b7
      obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.mp b7
      have e' : [x] = g12 := e
      subst e'
      rw [List.mem_singleton.mp hf]
      exact embeddingForm_slots hx (K.sVE hg)
    · rw [if_neg hg] at b7
      cases b7
      cases hf

/-- **Every form that the run "front" returns.** -/
theorem formsFront_slots {rows : Bool} {P : Pub} {g : ℕ} {o : Own} (K : FrontOk S rows P g o)
    {F G : Fork} {fs : Array Aff} (h : formsFrontWith rows P g o F = some (fs, G)) :
    ∀ f ∈ fs.toList, SlotsIn S f := by
  obtain ⟨sh, pp, l, _, _, _, a2, a3, rfl, _, _, _⟩ := formsFrontWith_some h
  rw [List.toList_toArray]
  exact front_slots K sh a2 a3

/-- **The list of "back".** -/
theorem back_slots {o : Own} (K : BackOk S o) :
    ∀ f ∈ back o (o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {}), SlotsIn S f := by
  intro f hf
  unfold back at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact K.rowS
  · exact slotsIn_sub (slotsIn_slot K.sA0) K.Alin
  · exact slotsIn_sub (slotsIn_slot K.sB0) K.Blin
  · exact slotsIn_rowForm _ _ K.mWin K.mStart slotsIn_empty

/-- **Every form that the run "back" returns.** -/
theorem formsBack_slots {o : Own} (K : BackOk S o) {F G : Fork} {fs : Array Aff}
    (h : formsBack o F = some (fs, G)) : ∀ f ∈ fs.toList, SlotsIn S f := by
  obtain ⟨_, rfl, _, _⟩ := formsBack_some h
  rw [List.toList_toArray]
  exact back_slots K

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.front_slots
#print axioms OnBytes.Desc.First.K4.Slots.formsFront_slots
#print axioms OnBytes.Desc.First.K4.Slots.back_slots
#print axioms OnBytes.Desc.First.K4.Slots.formsBack_slots
