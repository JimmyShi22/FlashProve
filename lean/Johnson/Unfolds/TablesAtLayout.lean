-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/TablesAtLayout.lean: **the tables that `publicOfO` hands to its comparisons of
digests ARE the stored example's**, at every scan of a parameter file `VerifierAndGoals.policyFile v` and
every layout that `Layer.layout` returns of it; and so three of these comparisons return.
  `gates_of_base`, `gates_of_layout`: the layout's fields `silu` and `fs` are `gateTables` at the
    shape's numbers. (The proof's walk through `layoutBase` is that of `Meaning.P34.tables_of_base`,
    Johnson/Goal/Meaning/PadScope.lean, which says the like of the fields `tauFL` and `tauFS`.)
  `shape_of_scan`: the shape is the hand-written `hKF` but for three free numbers
    (`VerifierAndGoals.Lines.scan_closed`; `Meaning.P34.shape_of_closed`,
    Johnson/Goal/Meaning/Pub34Scope.lean).
  **`tables_at_scan`**: routed experts; `y.silu` and `y.fs` are `gateTables 8 4095 true true`'s;
    `ropeOf y.h` returns `ropeTable 12 500000 128 10`.
  **`silu_step`, `fs_step`, `rope_step`**: `tableHeldO secondHashFunction P …` returns at these
    (Johnson/Unfolds/TablesHeld.lean).
Limits. That the scan and the layout return are premises. The table of exponentials, which lies on
the attention's side, is not here (`exp_held`, TablesHeld.lean, takes it as a premise).

-/
import Johnson.Unfolds.TablesHeld
import Johnson.Goal.Meaning.PadScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Unfolds
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Road
open OnBytes.Model.Layer (Lay Shape layout layoutBase gateTables ropeTable ropeOf)
open OnBytes.Model.Verify (layerShape)
open VerifiableInference.PlanWritten
open VerifierAndGoals (FreeLines policyFile)
open VerifierAndGoals.Lines (scan_closed)

/-- The first half of the layout lays `silu` and `fs` so. -/
theorem gates_of_base {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) :
    y.silu = (gateTables h.eg h.smax h.p3 h.gcl).1 ∧
      y.fs = (gateTables h.eg h.smax h.p3 h.gcl).2 := by
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy ⊢
  obtain ⟨silu, fs⟩ := gt
  cases hy
  exact ⟨rfl, rfl⟩

/-- The second half keeps them. -/
theorem gates_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) :
    y.silu = (gateTables h.eg h.smax h.p3 h.gcl).1 ∧
      y.fs = (gateTables h.eg h.smax h.p3 h.gcl).2 := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  have L := gates_of_base h0
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  exact L

section
variable {v : FreeLines} {P : PolScan} (hs : polScan (policyFile v) = .ok P)
include hs

/-- The shape of a scan of `policyFile v`. -/
theorem shape_of_scan : layerShape P = { hKF with
    eps1 := P.h.eps.getD 0 0, eps2 := P.h.eps.getD 1 0, epsF := P.h.epsF } := by
  have e := scan_closed hs
  subst e
  exact Meaning.P34.shape_of_closed v

variable {y : Lay} (hy : layout (layerShape P) P.polCalls = .ok y)
include hy

/-- **The tables at a scan of `policyFile v`.** -/
theorem tables_at_scan :
    y.h.p3 = true ∧ y.silu = (gateTables 8 4095 true true).1 ∧
      y.fs = (gateTables 8 4095 true true).2 ∧
      ropeOf y.h = .ok (ropeTable 12 500000 128 10) := by
  have hh := layout_shape hy
  have g := gates_of_layout hy
  rw [shape_of_scan hs] at g hh
  refine ⟨by rw [hh]; rfl, g.1, g.2, ?_⟩
  rw [hh]
  rfl

theorem silu_step : tableHeldO secondHashFunction P .silu y.silu = .ok () := by
  rw [(tables_at_scan hs hy).2.1]
  exact silu_held hs true true

theorem fs_step : tableHeldO secondHashFunction P .sigmoid y.fs = .ok () := by
  rw [(tables_at_scan hs hy).2.2.1]
  exact fs_held hs

theorem rope_step : ∃ rope, ropeOf y.h = .ok rope ∧ tableHeldO secondHashFunction P .rope rope = .ok () :=
  ⟨_, (tables_at_scan hs hy).2.2.2, rope_held hs⟩

end

end Johnson.Unfolds

#print axioms Johnson.Unfolds.gates_of_base
#print axioms Johnson.Unfolds.gates_of_layout
#print axioms Johnson.Unfolds.shape_of_scan
#print axioms Johnson.Unfolds.tables_at_scan
#print axioms Johnson.Unfolds.silu_step
#print axioms Johnson.Unfolds.fs_step
#print axioms Johnson.Unfolds.rope_step
