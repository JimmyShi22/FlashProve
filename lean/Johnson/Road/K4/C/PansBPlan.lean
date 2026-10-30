-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PansBPlan.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the batched sumcheck's panels: THE TEST
pansB IS TRUE AT THE PLAN's OWN ARGUMENTS, as a theorem and without evaluation: at the structure of
forms with no point of the lookup (blankEnv), the plan's number of rounds and the plan's count of
the panels' weight claims (Johnson/Desc/First/K4/Returns/Pub/PansB.lean, Hear.lean). It joins
pansB_of (PansBOf.lean: the test from what the panels' sides read) with panRd_of (PanRdOf.lean:
what they read is there). So the test follows from the verifier's lines that make the layout, the
reads and the tables' places, with five facts on the plan. General in the sizes. A statement and
its proof.

  **`pansB_plan`**   pansB P (blankEnv P hp g iU3 r.1) hp.lamS (nclpOf hp g) = true.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. AT A LAYOUT
WHOSE EIGHT LINES OF CALLS ARE THE LIBRARY's, UNDER THE LIBRARY's ELEVEN SWITCHES ALONE, at profile
4. FIVE FACTS ON THE PLAN ARE HYPOTHESES: the reads' array has a column (hK); the row of the first
free entry behind the reads fits 32 bits (hb); the plan's rounds and weight claims are the functions
lamSOf and nclOf of the layout (h1, h2: the library's planG_sizes, Johnson/Road/K4/PlanSizes.lean,
has both where the plan is what planG returns); the rounds are at most 63 (h63). The tables' places
stand at the library's list of the matrices' sizes (matsR). Public data alone: numbers, and whether
a form IS THERE; nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.PansBOf
import Johnson.Road.K4.C.PanRdOf
import Johnson.Desc.First.K4.Returns.Pub.Hear

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Pub HPlan2 TableAsk TableAt layTables tableAsks layout readsOf lamSOf
  nclOf)
open OnBytes.Desc.First.K4.RtPub (pansB blankEnv nclpOf)

/-- **THE TEST pansB IS TRUE AT THE PLAN's OWN ARGUMENTS.** CONDITIONAL: on the verifier's lines,
the switches, profile 4, the eight lines and five facts on the plan (hK, hb, h1, h2, h63). -/
theorem pansB_plan {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {P : Pub}
    {hp : HPlan2} {g iU3 : ℕ} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hy : layout h pc = .ok P.y) (S : Switches h) (h4 : h.p4 = true) (hg : g < P.y.NGr)
    (hrd : readsOf P.y = .ok P.rd) (hN : LinesAre P.y)
    (hl : layTables (matsR P.y g) (tableAsks P.y P.rd g) 0 = some r)
    (hK : ((hp.Fp.trees[iU3]?).map (·.K)).getD 0 ≠ 0)
    (hb : r.2.2 / ((hp.Fp.trees[iU3]?).map (·.K)).getD 0 < 2 ^ 32)
    (h1 : hp.lamS = lamSOf P.y) (h2 : hp.NCL = nclOf P.y g) (h63 : hp.lamS ≤ 63) :
    pansB P (blankEnv P hp g iU3 r.1) hp.lamS (nclpOf hp g) = true := by
  have h3 : P.y.h.p3 = true := by
    rw [(admitted_of_layout hy S.p3).shape]
    exact S.p3
  refine pansB_of (v₀ := blankEnv P hp g iU3 r.1) rfl hy S h4 hrd hN
    (panRd_of (v := blankEnv P hp g iU3 r.1) hy S h4 hg hrd hl rfl hK hb) h1 ?_ h63
  unfold nclpOf
  rw [h2]
  unfold nclOf
  rw [if_pos h3]
  split_ifs <;> omega

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.pansB_plan
