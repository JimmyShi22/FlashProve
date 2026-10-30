-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/HvalOf.lean: CONDITIONAL.

What is here. The hypothesis hval of PassOf.lean, TokFitsOf.lean and JoinPub.lean («the honest value
of each of a panel's own forms is the form's value in the world»), paid IN EVERY WORLD WHOSE ENTRIES
ARE THE TRUE ONES, whatever it holds under its slots. So the world of the panels' ties can be the
world of the start form itself. Three laws that lay ready are called: a panel's forms name no slot
(the library's `panelsT_ok`, Johnson/Road/K4/Slots/Panels.lean); they name entries in front of the
tables of the lookup's planes alone (`panelsT_low`, Johnson/Road/K4/C/PanelsBelow.lean, with
`hG_of_lt`, C/OffPlanes.lean); a form's value on the honest reads is its value at the true entries
(`valAff_true`, C/ValAff.lean).

  `form_ok`, `form_low`   a panel's own form names no slot; its entries lie in front of the planes'
     tables
  `hval_true`   **the honest value of a panel's own form is the form's value**

Limits. At the reading `Reading.gl`. HYPOTHESES, as in C/ValAff.lean and C/PanelsBelow.lean: the
honest reads, the laying of the tables and the verifier's list of tables return, at lists of points
of which the honest one is a part; the sub-proof's list of matrices is the plan's; on every matrix
but that of the lookup's planes the matrices Mm hold the honest input's cells (`CellsAre`); the
environment's list of places is the one that the laying returns and has the family "b-bits-0"; the
panels are the verifier's list at that environment, placed. The reads and the tables may stand at
any named points: so it serves a token's corner too. Of the hypotheses together no sample is known
at the full size.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PanelShare
import Johnson.Road.K4.C.PanelsBelow
import Johnson.Road.K4.C.OffPlanes
import Johnson.Road.K4.C.ValAff
import Johnson.Road.K4.C.TermsOpen
import Johnson.Road.K4.Slots.Panels

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff World HFun HTailF2)
open OnBytes.Model.Layer (SBlk Env PanelEnv Panels panelsA panelsT placePanels TableAsk TableAt
  layTables tableAsks funsOf matIx)
open OnBytes.Road (Mats)
open OnBytes.Road.K4 (entryOf)
open OnBytes.Road.K4.C (PanLow panLow_empty panelsA_low panelsT_low placePanels_low Below
  tabFront_of_lay hG_of_lt valAff_true valAffQ_some CellsAre PtsPart)
open OnBytes.Desc.First.K4.Slots (PanOk panOk_empty panelsA_ok panelsT_ok placePanels_ok SlotsIn
  core)
open OnBytes.Desc.First.K4.Honest

/-- A panel's core stands in the list of the cores. -/
theorem core_mem {bl : Array SBlk} {b : SBlk} (hb : b ∈ bl.toList) :
    core b ∈ (bl.map core).toList := by
  rw [Array.toList_map]
  exact List.mem_map_of_mem hb

/-- **A panel's own form names slots with S alone**, where the list of panels does. -/
theorem form_ok {S : ℕ → Prop} {bl : Array SBlk} (h : PanOk S bl) {b : SBlk}
    (hb : b ∈ bl.toList) {a : Aff} (ha : FormOf b a) : SlotsIn S a := by
  obtain ⟨hA, hB, hx⟩ := h (core b) (core_mem hb)
  rcases ha with ⟨yv, _, rfl⟩ | ⟨A, i, yv, h1, h2⟩ | ⟨B, i, yv, h1, h2⟩
  · exact hx yv
  · exact hA A h1 i yv a h2
  · exact hB B h1 i yv a h2

/-- **A panel's own form names entries in front of the place tB0 alone**, where the list of panels
does. -/
theorem form_low {v : Env} {tB0 : ℕ} {bl : Array SBlk} (h : PanLow v tB0 bl) {b : SBlk}
    (hb : b ∈ bl.toList) {a : Aff} (ha : FormOf b a) : Below v tB0 a := by
  obtain ⟨hA, hB, hx⟩ := h (core b) (core_mem hb)
  rcases ha with ⟨yv, _, rfl⟩ | ⟨A, i, yv, h1, h2⟩ | ⟨B, i, yv, h1, h2⟩
  · exact hx yv
  · exact hA A h1 i yv a h2
  · exact hB B h1 i yv a h2

/-- **THE HONEST VALUE OF A PANEL's OWN FORM IS THE FORM's VALUE, IN EVERY WORLD WITH THE TRUE
ENTRIES.** CONDITIONAL: on every hypothesis named. pe: the panels' environment; W's slots are free.
-/
theorem hval_true {Q : K4Pub} {w : K4In} {fo fo' : OnBytes.Model.Forest.Heard}
    {pt pts : List (String × Array E)} {R : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {Mm : Mats Cb.Gl.E}
    {funs : Array HFun} (hR : readsAt Q w fo pt = some R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) (hp : PtsPart pt pts)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size)
    (hC : CellsAre Q w Mm) {pe : PanelEnv} (hv : pe.v.tab = r.1) {tB0 : ℕ}
    (hB : pe.v.tabAt "b-bits-0" = some tB0) {TS : List ℕ} {pans : Panels}
    (hpan : panelsT pe TS (panelsA pe {}) = some pans) {W : World Cb.Gl.E}
    (hW : W.entry = entryOf Reading.gl tl funs pe.v.iU3 pe.v.K3 Mm) :
    ∀ b ∈ (placePanels pans.bl).1.toList, ∀ a, FormOf b a → ∀ y,
      valAff? pe.v R (fun _ => zeroE) a = some y → Reading.gl.val y = a.value Reading.gl W := by
  intro b hb a ha y hy
  have F := tabFront_of_lay hl hv hB
  have L : PanLow pe.v tB0 (placePanels pans.bl).1 :=
    placePanels_low (panelsT_low pe F TS (panelsA_low pe F panLow_empty) pans hpan)
  have O : PanOk (fun _ => False) (placePanels pans.bl).1 :=
    placePanels_ok (panelsT_ok pe TS (panelsA_ok pe panOk_empty) pans hpan)
  obtain ⟨hfit, rfl⟩ := (valAffQ_some pe.v R _ a y).mp hy
  exact valAff_true hR hl hf hp (Or.inl fun _ h => h) hm hNM hC hfit hW
    (fun x hx => (form_ok O hb ha x hx).elim) (hG_of_lt hl hf hv hB (form_low L hb ha))

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.core_mem
#print axioms ProofFile.Honest.K4.form_ok
#print axioms ProofFile.Honest.K4.form_low
#print axioms ProofFile.Honest.K4.hval_true
