-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StackSidesOf.lean: CONDITIONAL.

Not shown here. That the maker of the batched sumcheck's data returns, and its end values (hD, h).
THAT THE VERIFIER's CALL OF stackEnd, AT THE HONEST SIDE's PANELS, CHALLENGES AND WEIGHTS, RETURNS
WHAT THE VERIFIER HOLDS (hfin). That the points which the honest side has heard stand in the
verifier's list (hp). That layTables and funsOf return; the sizes of the smallness test's list of
matrices; CellsAre; that the world's entries are the true ones. No example is known.
No property is claimed.

THE TWO SIDES' END VALUES OF THE BATCHED SUMCHECK ARE THE WORTHS OF THE VERIFIER's TWO FORMS:
sides_read (StackSides.lean) at the data that the honest side's own maker returns, with six of its
premises paid: the reads are the maker's (stack_open); the two forms name no slot (the library's
stackEnd_slots); their entries lie off the matrix of the lookup's planes (sides_off,
PanelsBelow.lean, over stack_panels_at, StackPanelsAt.lean); nothing is asked of the two looks.

  envOf_tab      the honest structure of the forms has layTables' list of places.
  tabAt_planes   the family "b-bits-0" is found in that list.
  stack_open     what the maker lays into the data: what the two jobs share, the reads, the weights.
  sides_read_of  the two end values.
-/
import Johnson.Road.K4.C.StackSides
import Johnson.Road.K4.C.PanelsBelow
import Johnson.Road.K4.C.StackPanelsAt
import Johnson.Road.K4.C.TermsAtOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env StackEnd stackEnd TableAsk TableAt layTables tableAsks funsOf matIx)
open OnBytes.Road.K4 (entryOf)
open OnBytes.Desc.First.K4.Slots (EndOk stackEnd_slots placePanels_ok panelsT_ok panelsA_ok
  panOk_empty)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts Sides StackData matsOf envOf readsAt namedPts
  stackData stackDataOn)

variable {Q : K4Pub} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- The honest structure of the forms has layTables' list of places. -/
theorem envOf_tab {p : Pts} {v : Env} (hv : envOf Q p = some v)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) : v.tab = r.1 := by
  unfold envOf at hv
  obtain ⟨iU3, _, h⟩ := Option.bind_eq_some_iff.mp hv
  obtain ⟨⟨tab, a, b⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  obtain rfl : r = (tab, a, b) := Option.some.inj (hl.symm.trans ht)
  rfl

/-- The family "b-bits-0" is found in layTables' list of places. -/
theorem tabAt_planes (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) {v : Env}
    (hv : v.tab = r.1) : ∃ tB0, v.tabAt "b-bits-0" = some tB0 := by
  have hl' : layTables (matsOf Q) (Fo.preAsks Q.P.y Q.P.rd Q.g ++ Fo.planeAsk Q.P.y "b-bits-0" ::
      [Fo.planeAsk Q.P.y "b-bits-1", Fo.planeAsk Q.P.y "b-pin"]) 0 = some (r.1, r.2.1, r.2.2) := hl
  obtain ⟨tB0, hB0, -⟩ := Fo.lay_find (matsOf Q) (Fo.planeAsk Q.P.y "b-bits-0") rfl _ _ 0 _ _ _
    (fun b hb => Fo.ask_ne hb "b-bits-0" (by decide)) hl'
  refine ⟨tB0, ?_⟩
  unfold Env.tabAt
  rw [hv]
  exact hB0

/-- **What the maker lays into the data.** -/
theorem stack_open {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) :
    Sides.of Q w p = some SD.S ∧ readsAt Q w p.fo (namedPts Q p) = some SD.R ∧ SD.om = p.om := by
  unfold stackData at h
  obtain ⟨S, hS, h⟩ := Option.bind_eq_some_iff.1 h
  unfold stackDataOn at h
  obtain ⟨R, hR, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨bl, places⟩, _, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at h
  by_cases hc : (ceilLog2 places != S.Q.hp.lamS || p.om.size != 2 ||
      S.opens.size != S.Q.hp.NCL - (if (S.Q.g == 0) = true then 1 else 0)) = true
  · rw [if_pos hc] at h
    simp at h
  · rw [if_neg hc] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨sides, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    obtain ⟨eQ, ew, ef, -, -⟩ := sides_fields hS
    rw [eQ, ew, ef] at hR
    exact ⟨hS, hR, rfl⟩

/-- **The two sides' end values, at the data that the honest side's maker returns.** l: the end
values at the challenges rs; fin: what the verifier's call of stackEnd returns at any shown values
H1, V, a, b. -/
theorem sides_read_of {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (hD : stackData Q w p shownT = some SD)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) {fo' : Forest.Heard}
    {pts : List (String × Array E)} {tl : HTailF2} {Mm : Mats Cb.Gl.E} {funs : Array HFun}
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) (hp : PtsPart (namedPts Q p) pts)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size)
    (C : CellsAre Q w Mm) {rs : Array E} {l : List E} (h : SD.endsAt rs = some l)
    {H1 V : Array E} {a b : E} {fin : StackEnd}
    (hfin : stackEnd SD.S.v.y SD.bl rs SD.S.Q.hp.lamS SD.om H1 V a b = some fin)
    {W : World Cb.Gl.E} (hW : W.entry = entryOf Reading.gl tl funs SD.S.v.iU3 SD.S.v.K3 Mm) :
    Reading.gl.val (l.getD 0 zeroE) = fin.Alin.value Reading.gl W ∧
      Reading.gl.val (l.getD (2 + SD.S.v.y.LamM) zeroE) = fin.Blin.value Reading.gl W := by
  obtain ⟨hS, hR, -⟩ := stack_open hD
  obtain ⟨-, -, -, hv0, -⟩ := sides_fields hS
  have hv : SD.S.v.tab = r.1 := envOf_tab hv0 hl
  obtain ⟨pans, hpn, hbl, -⟩ := stack_panels_at hD
  have hfin' := hfin
  rw [hbl] at hfin'
  obtain ⟨tB0, hB⟩ := tabAt_planes hl hv
  obtain ⟨gA, gB⟩ := sides_off (tl := tl) hl hf (pe := sidesEnv SD.S shownT) hv hB hpn hfin'
  have ok : EndOk (fun _ => False) fin :=
    stackEnd_slots (placePanels_ok (panelsT_ok _ _ (panelsA_ok _ panOk_empty) pans hpn)) hfin'
  exact sides_read (G := (· ≠ (matIx Q.P.y).iB)) hR hl hf hp (Or.inl fun _ h => h) hm hNM C h hfin
    hW (fun s hs => ok.1 s hs) (fun s hs => ok.2 s hs) gA gB

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.envOf_tab
#print axioms OnBytes.Road.K4.C.tabAt_planes
#print axioms OnBytes.Road.K4.C.stack_open
#print axioms OnBytes.Road.K4.C.sides_read_of
