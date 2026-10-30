-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/OpensOfUnits.lean: CONDITIONAL.

What is here. `OpensAt` (Johnson/Road/K4/C/MergedOf.lean: the honest side's open tables read as the
library's vectors of the verifier's weight claims, panel by panel, with 0 beyond a panel's rows and
columns) from the same law claim by claim (`opens_are`, Law/OpenTabs.lean) and public numbers. At
every place of a panel the claim's law gives the entry of the honest table; beyond the panel's
columns that entry is 0 by the guard of `at2`, since the extent of the group "kk" (`opens_kk`) is at
most the panel's number of columns; beyond its rows it is 0 by `opens_beyond`, since the extent of
the group "e" is at most the panel's number of rows.

  `ext0Of u n`   the extent of the group named n of the unit u; 0 if there is none.
  `PanelUnits SD lay cl`   the hypothesis: at each panel the claims' units: found; with the group
      "e" just where the panel has the selector; the bits of a column; the extents at most the
      panel's numbers.
  `opensAt_of_units`   OpensAt from PanelUnits.

Not shown here. PanelUnits: a hypothesis HERE. It reads five numbers of each panel (selector, first
claim, bits of a column, columns, rows), which unit each claim names, and that unit's groups: no
value of the witness. It is written over the panels inside the honest side's data, which are the
verifier's placed panels (stack_panels_at, Johnson/Road/K4/C/StackPanelsAt.lean).
Johnson/Road/K4/C/UnitsOfClaim.lean has it from the layout (panel_units). No member of it is
evaluated in Lean. It can hold only where the extents in the weights' layout are at most the panels'
(the widths of the query heads and of the feed-forward parts, the number of experts). That the
function which makes the batched sumcheck's data returns, that the verifier's list of weight claims
returns, that the weights' layout is one that wsLayOf returns for a model with routed experts:
hypotheses. That all of these hold together: no example is known. The import closure holds what
Law/OpenTabs.lean's holds, and Johnson/Road/K4/C/. Nothing on soundness, on completeness or on any
other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.OpenTabs
import Johnson.Road.K4.C.MergedOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE)
open OnBytes.Model (Reading WsLay WsUnit WsClaim WsShape wsLayOf)
open OnBytes.Model.Layer (ClaimEnv)
open OnBytes.Road (hasE wkOf wvOf)
open OnBytes.Road.K4.C (OpensAt)
open OnBytes.Desc.First.K4.Honest

/-- The extent of the group named n of the unit u; 0 if there is none. -/
def ext0Of (u : WsUnit) (n : String) : ℕ := ((u.g.find? fun g => g.name == n).map (·.R)).getD 0

/-- **At each panel, the claims' units.** This defines a hypothesis; the definition claims nothing.
-/
def PanelUnits (SD : StackData) (lay : WsLay) (cl : List WsClaim) : Prop :=
  ∀ b ∈ SD.bl.toList, ∀ v0, b.v0 = some v0 →
    (b.tri = true → ∃ x u, cl[v0]? = some x ∧ lay.U[x.ui]? = some u ∧ hasE u.g = true ∧
      wkOf u.g = b.wy ∧ ext0Of u "kk" ≤ b.ny ∧ ext0Of u "e" ≤ b.ni) ∧
    (b.tri = false → ∀ i, i < b.ni → ∃ x u, cl[v0 + i]? = some x ∧ lay.U[x.ui]? = some u ∧
      hasE u.g = false ∧ ext0Of u "kk" ≤ b.ny)

/-- **OpensAt FROM THE CLAIMS' LAW AND PUBLIC NUMBERS.** CONDITIONAL: on every hypothesis named. -/
theorem opensAt_of_units {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) {rs : Array E} {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay)
    (U : PanelUnits SD Q.P.wsLay cl) : OpensAt SD Q.P.wsLay (wmOf w.w) cl := by
  intro b hb v0 h0
  refine ⟨fun ht i _ yv hy => ?_, fun ht i hi yv _ => ?_⟩
  · obtain ⟨x, u, hx, hu, hE, hwk, hkk, he⟩ := (U b hb v0 h0).1 ht
    have r := opens_are h hcl hl v0 x u hx hu i yv (Or.inl ⟨hE, by rw [hwk]; exact hy⟩)
    rw [hwk] at r
    rw [← r]
    by_cases ci : i < b.ni
    · rw [if_pos ci]
      by_cases cy : yv < b.ny
      · rw [if_pos cy]
      · rw [if_neg cy]
        unfold at2
        rw [if_neg (by
          rw [opens_kk h hcl v0 x u hx hu]
          exact fun c => cy (Nat.lt_of_lt_of_le c hkk))]
        exact Reading.gl.zero
    · rw [if_neg ci, opens_beyond h hcl hl v0 x u hx hu hE i yv
        (Nat.le_trans he (Nat.le_of_not_lt ci))]
      exact Reading.gl.zero
  · obtain ⟨x, u, hx, hu, hE, hkk⟩ := (U b hb v0 h0).2 ht i hi
    have r := opens_are h hcl hl (v0 + i) x u hx hu 0 yv (Or.inr ⟨hE, rfl⟩)
    rw [Nat.zero_mul, Nat.zero_add] at r
    rw [← r]
    by_cases cy : yv < b.ny
    · rw [if_pos cy]
    · rw [if_neg cy]
      unfold at2
      rw [if_neg (by
        rw [opens_kk h hcl (v0 + i) x u hx hu]
        exact fun c => cy (Nat.lt_of_lt_of_le c hkk))]
      exact Reading.gl.zero

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.opensAt_of_units
