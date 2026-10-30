-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StackPanelsAt.lean: CONDITIONAL.

Not shown here. THAT THE FUNCTION WHICH MAKES THE BATCHED SUMCHECK's DATA RETURNS: a hypothesis, of
which no example is known here. Nothing on what a panel's sides hold; nothing says that the five
letters of the panels' environment are the verifier's. Nothing on soundness, on completeness or on
any other property. No property is claimed.

The panels in the data of the batched sumcheck's job (`stackData`,
Johnson/Desc/K4/Honest/Stack.lean) are the verifier's own list, placed, AT AN ENVIRONMENT WRITTEN
OUT: `stack_panels` (C/DownPanel.lean) says of that environment its field v alone; a statement that
holds the honest side's panels against the verifier's wants all five fields.

  `sidesEnv S shownT`   the environment: five fields.
  `stack_panels_at`   the list, at that environment; the number of its weight claims.
-/
import Johnson.Road.K4.C.DownPanel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (placePanels Panels PanelEnv panelsA panelsT stubO)
open OnBytes.Desc.First.K4.Honest

/-- The panels' environment as the honest side lays it. shownT: what stands in the place of the
values that the second token sumcheck has shown. -/
def sidesEnv (S : Sides) (shownT : Array E) : PanelEnv :=
  { v := S.v, e := S.fo.e, shownT := shownT, zt := S.zt, stubO := stubO S.v.y }

/-- **The panels in the job's data, with their environment written out.** CONDITIONAL: on the
return. -/
theorem stack_panels_at {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) :
    ∃ pans : Panels,
      panelsT (sidesEnv SD.S shownT) SD.S.TS (panelsA (sidesEnv SD.S shownT) {}) = some pans ∧
      SD.bl = (placePanels pans.bl).1 ∧ ¬(pans.nextV != SD.S.opens.size) = true := by
  unfold stackData at h
  obtain ⟨S, _, h⟩ := Option.bind_eq_some_iff.1 h
  unfold stackDataOn at h
  obtain ⟨R, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨bl, places⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at h
  by_cases hc : (ceilLog2 places != S.Q.hp.lamS || p.om.size != 2 ||
      S.opens.size != S.Q.hp.NCL - (if (S.Q.g == 0) = true then 1 else 0)) = true
  · rw [if_pos hc] at h
    simp at h
  · rw [if_neg hc] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨sides, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    unfold Sides.panels at hp
    obtain ⟨pans, h1, hp⟩ := Option.bind_eq_some_iff.1 hp
    dsimp only at hp
    by_cases hn : (pans.nextV != S.opens.size) = true
    · rw [if_pos hn] at hp
      simp at hp
    · rw [if_neg hn] at hp
      obtain ⟨_, _, hp⟩ := Option.bind_eq_some_iff.1 hp
      have e := Option.some.inj hp
      exact ⟨pans, h1, (congrArg Prod.fst e).symm, hn⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.stack_panels_at
