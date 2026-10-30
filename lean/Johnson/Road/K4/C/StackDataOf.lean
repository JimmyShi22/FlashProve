-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StackDataOf.lean: CONDITIONAL.

What is here. The honest side's function that makes the data of the batched sumcheck returns
(`stackDataOn_returns`; `stackDataOn`: Johnson/Desc/K4/Honest/Stack.lean), and what it returns is
written out: its two long tables are longTabs of the tables that panelTabs makes of each panel; a
conjunct of its own says so. It returns wherever: the verifier's laying of the tables returns; the
honest side's list of placed panels returns; its three tests on numbers answer yes; the verifier's
end of that sumcheck returns over these panels at some values; and the three points zt, rt and Y
stand whole in the honest side's list of points. Each panel's two tables are made
(Johnson/Road/K4/C/PanelTabsOf.lean) because each form that a panel holds is valued: it names
entries of tables at these three points alone (EntsAt.lean), and there the honest reads hold the
weights (PtsHave.lean). The same holds of the two forms that the verifier's end leaves
(`end_valued`, over EndAt.lean).

  `panels_opened`   the honest side's list of placed panels, opened.
  `valued_of_inTest`   a form that names such entries alone is valued (valAff?, at any slots).
  `panels_valued`   the panels' forms, and a first weight claim or a B side at each panel.
  `stackDataOn_returns`   the data are made.
  `end_valued`   the two forms of the verifier's end are valued.

Not shown here. EVERY RETURN AND TEST NAMED ABOVE IS A HYPOTHESIS: hl, ht, hPan, hc, hom, ho, hE,
H3; readsOf's return, T = 2 ^ lt and ls + lt = la are asked as they are spent (all three follow from
K4Plan). That they hold together: no example is laid here; they are met inside `stack_fit`
(Law/W/FitStack.lean), whose head says who has its hypotheses together. What the entries of the two
long tables are worth is not shown. panels_opened IS Law/TokSig.lean's panels_open TYPED AGAIN, in a
file that imports nothing of the honest prover's frame, and ends in both halves of the pair where
that one ends in the first: that one follows from this one. Nothing on soundness, on completeness
or on any other property. No property is claimed.
-/
import Johnson.Road.K4.C.PanelTabsOf
import Johnson.Road.K4.C.PtsHave
import Johnson.Road.K4.C.EndAt
import Johnson.Road.K4.C.PanVB
import Johnson.Road.K4.C.StackPanelsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env SBlk Panels StackEnd TableAsk TableAt layTables tableAsks readsOf
  panelsA panelsT placePanels stackEnd)
open OnBytes.Desc.First.K4.Slots (core)
open OnBytes.Desc.First.K4.Honest (Sides Pts StackData matsOf readsAt namedPts valAff? affFits
  panelTabs longTabs stackDataOn)

/-- **The honest side's list of placed panels, opened.** CONDITIONAL: on the return. -/
theorem panels_opened {S : Sides} {shownT : Array E} {x : Array SBlk × ℕ}
    (h : S.panels shownT = some x) :
    ∃ pans : Panels,
      panelsT (sidesEnv S shownT) S.TS (panelsA (sidesEnv S shownT) {}) = some pans ∧
      x = placePanels pans.bl := by
  unfold Sides.panels at h
  obtain ⟨pans, hp, h⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨pans, hp, ?_⟩
  split at h
  · cases h
  · exact (Option.some.inj h).symm

/-- A form that names only entries whose weights the honest reads hold is valued. -/
theorem valued_of_inTest {v : Env} {R : OnBytes.Desc.First.K4.Honest.Reads} {f : Aff}
    (I : InTest v (fun e => R.has e = true) f) (slot : ℕ → E) :
    (valAff? v R slot f).isSome = true := by
  unfold valAff?
  rw [if_pos (affFits_of_inTest I)]
  rfl

variable {S : Sides} {p : Pts} {shownT : Array E} {x : Array SBlk × ℕ}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  {R : OnBytes.Desc.First.K4.Honest.Reads}

/-- **The panels' forms name entries whose weights the honest reads hold; each panel has a first
weight claim or a B side.** CONDITIONAL: on every hypothesis named. -/
theorem panels_valued (hrd : readsOf S.Q.P.y = .ok S.Q.P.rd)
    (hl : layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r)
    (hT : S.Q.P.y.T = 2 ^ S.Q.P.y.h.lt) (hla : S.Q.P.y.ls + S.Q.P.y.h.lt = S.Q.P.y.h.la)
    (ht : S.v.tab = r.1) (hPan : S.panels shownT = some x)
    (hR : readsAt S.Q S.w S.fo (namedPts S.Q { p with fo := S.fo }) = some R)
    (H3 : PtIn S.Q.P.y (namedPts S.Q { p with fo := S.fo }) "zt" ∧
      PtIn S.Q.P.y (namedPts S.Q { p with fo := S.fo }) "rt" ∧
      PtIn S.Q.P.y (namedPts S.Q { p with fo := S.fo }) "Y") :
    PanAt S.v (fun e => R.has e = true) x.1 ∧ PanVB x.1 := by
  obtain ⟨pans, hp, rfl⟩ := panels_opened hPan
  have H := ptAt_has hrd hl hR hT hla ht
  exact ⟨placePanels_at (panelsT_at (sidesEnv S shownT) H H3.2.1 H3.2.2 S.TS
      (panelsA_at (sidesEnv S shownT) H H3.1 panAt_empty) pans hp),
    placePanels_vb (panelsT_vb (sidesEnv S shownT) S.TS
      (panelsA_vb (sidesEnv S shownT) panVB_empty) pans hp)⟩

/-- **THE DATA OF THE BATCHED SUMCHECK ARE MADE.** CONDITIONAL: on every hypothesis named. -/
theorem stackDataOn_returns (hrd : readsOf S.Q.P.y = .ok S.Q.P.rd)
    (hl : layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r)
    (hT : S.Q.P.y.T = 2 ^ S.Q.P.y.h.lt) (hla : S.Q.P.y.ls + S.Q.P.y.h.lt = S.Q.P.y.h.la)
    (ht : S.v.tab = r.1) (hPan : S.panels shownT = some x)
    (hc : ceilLog2 x.2 = S.Q.hp.lamS) (hom : p.om.size = 2)
    (ho : S.opens.size = S.Q.hp.NCL - (if S.Q.g == 0 then 1 else 0))
    {y : Layer.Lay} {rs om H1 V : Array E} {lam : ℕ} {a b : E} {fin : StackEnd}
    (hE : stackEnd y x.1 rs lam om H1 V a b = some fin)
    (H3 : PtIn S.Q.P.y (namedPts S.Q { p with fo := S.fo }) "zt" ∧
      PtIn S.Q.P.y (namedPts S.Q { p with fo := S.fo }) "rt" ∧
      PtIn S.Q.P.y (namedPts S.Q { p with fo := S.fo }) "Y") :
    ∃ R sides, readsAt S.Q S.w S.fo (namedPts S.Q { p with fo := S.fo }) = some R ∧
      x.1.mapM (panelTabs S (fun a => valAff? S.v R (fun _ => zeroE) a) p.om
        (S.weights (eqTab p.rt)) (S.gatedUnder (eqTab S.zt)) (S.gatedUnder (eqTab p.rt))) =
          some sides ∧
      stackDataOn S p shownT = some
        { S := S, R := R, bl := x.1, om := p.om, F := S.weights (eqTab p.rt)
          hZ := S.gatedUnder (eqTab S.zt), hR := S.gatedUnder (eqTab p.rt)
          SA := (longTabs S.Q.hp.lamS x.1 sides).1, SB := (longTabs S.Q.hp.lamS x.1 sides).2 } := by
  obtain ⟨R, hR⟩ := readsAt_of_lay hl S.w S.fo (namedPts S.Q { p with fo := S.fo })
  obtain ⟨PA, PV⟩ := panels_valued hrd hl hT hla ht hPan hR H3
  obtain ⟨sides, hs⟩ := amapM_there
    (g := panelTabs S (fun a => valAff? S.v R (fun _ => zeroE) a) p.om (S.weights (eqTab p.rt))
      (S.gatedUnder (eqTab S.zt)) (S.gatedUnder (eqTab p.rt))) x.1 (fun b hb => by
    obtain ⟨s1, s2, h1⟩ := stackEnd_each hE b hb
    obtain ⟨cA, cB, cX⟩ := PA (core b) (by rw [Array.toList_map]; exact List.mem_map_of_mem hb)
    obtain ⟨z, hz⟩ := panelTabs_there S (fun a => valAff? S.v R (fun _ => zeroE) a) p.om
      (S.weights (eqTab p.rt)) (S.gatedUnder (eqTab S.zt)) (S.gatedUnder (eqTab p.rt))
      (there_of_end (panVB_mem PV hb) h1) (fun yv => valued_of_inTest (cX yv) _)
      (fun A i yv f eA ef => valued_of_inTest (cA A eA i yv f ef) _)
      (fun B i yv f eB ef => valued_of_inTest (cB B eB i yv f ef) _)
    rw [hz]
    rfl)
  refine ⟨R, sides, hR, hs, ?_⟩
  obtain ⟨bl, places⟩ := x
  have c0 : (ceilLog2 places != S.Q.hp.lamS || p.om.size != 2 ||
      S.opens.size != S.Q.hp.NCL - (if S.Q.g == 0 then 1 else 0)) = false := by
    have hc' : ceilLog2 places = S.Q.hp.lamS := hc
    rw [hc', hom, ← ho]
    simp
  unfold stackDataOn
  dsimp only
  rw [hR, hPan]
  simp only [Option.bind_eq_bind, Option.bind_some, c0, Bool.false_eq_true, if_false,
    Option.pure_def]
  rw [hs]
  rfl

/-- **The two forms of the verifier's end are valued.** CONDITIONAL: on every hypothesis named. -/
theorem end_valued (hrd : readsOf S.Q.P.y = .ok S.Q.P.rd)
    (hl : layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r)
    (hT : S.Q.P.y.T = 2 ^ S.Q.P.y.h.lt) (hla : S.Q.P.y.ls + S.Q.P.y.h.lt = S.Q.P.y.h.la)
    (ht : S.v.tab = r.1) (hPan : S.panels shownT = some x)
    (hR : readsAt S.Q S.w S.fo (namedPts S.Q { p with fo := S.fo }) = some R)
    (H3 : PtIn S.Q.P.y (namedPts S.Q { p with fo := S.fo }) "zt" ∧
      PtIn S.Q.P.y (namedPts S.Q { p with fo := S.fo }) "rt" ∧
      PtIn S.Q.P.y (namedPts S.Q { p with fo := S.fo }) "Y")
    {y : Layer.Lay} {rs om H1 V : Array E} {lam : ℕ} {a b : E} {fin : StackEnd}
    (hE : stackEnd y x.1 rs lam om H1 V a b = some fin) :
    affFits S.v R fin.Alin = true ∧ affFits S.v R fin.Blin = true := by
  obtain ⟨PA, _⟩ := panels_valued hrd hl hT hla ht hPan hR H3
  obtain ⟨e1, e2⟩ := stackEnd_at PA hE
  exact ⟨affFits_of_inTest e1, affFits_of_inTest e2⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.panels_opened
#print axioms OnBytes.Road.K4.C.valued_of_inTest
#print axioms OnBytes.Road.K4.C.panels_valued
#print axioms OnBytes.Road.K4.C.stackDataOn_returns
#print axioms OnBytes.Road.K4.C.end_valued
