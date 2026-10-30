-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PansWalkA.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the batched sumcheck's panels: the
verifier's first walk over the segments (panelsA, OnBytes/Model/LayerPanels.lean) reads the
segments' names alone; at the library's eight lines it appends six panels, for the segments G, U,
O, D, V and LR in this order; and the summary of that list (Sm, PansSum.lean). One definition of a
hypothesis; statements and proofs. General in the sizes.

  `PanRd v`       what the panels' sides read: entries at the two token points, the residual stream
                  at the point Y.
  `walkA_call`    the walk over one call's segments is the walk over the line's names.
  `panelsA_six`   the six panels.
  **`sm_panelsA`**  the summary behind the first walk.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. AT A
LAYOUT WHOSE EIGHT LINES OF CALLS ARE THE LIBRARY's, at profile 4. Public data alone: numbers, and
whether a form IS THERE; nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.PansSum
import Johnson.Road.K4.C.PointReturn
import Johnson.Road.FormsKeysPans
import Johnson.Road.FormsKeysW
import Johnson.Road.FormsKeysEarly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Panels PanelEnv panelA panelsA)
open Inst.Model.FFSeg (fams)

/-- **What the panels' sides read.** odd: a layer with routed experts is a layer of the group. This
defines a hypothesis; the definition claims nothing. -/
structure PanRd (v : Env) : Prop where
  m_zt : ∀ lam, lam < v.y.Lam → Short v "m" "zt" lam v.y.h.d
  a_zt : ∀ lam, lam < v.y.Lam → Short v "a" "zt" lam v.y.h.d
  o_zt : ∀ lam, lam < v.y.Lam → Short v "o" "zt" lam v.y.dq
  a_rt : ∀ lam, lam < v.y.Lam → Short v "a" "rt" lam v.y.h.d
  m_rt : ∀ lam, lam < v.y.Lam → Short v "m" "rt" lam v.y.h.d
  lr_rt : ∀ lm, lm < v.y.LamM → Short v "lr" "rt" lm v.y.h.NE
  xr_rt : ∀ lm, lm < v.y.LamM → Short v "xr" "rt" lm v.y.h.d
  strY : ∀ sg, sg < v.y.NW * v.y.Lam → StrmP v "Y" sg
  odd : ∀ i, i < v.y.LamM → 2 * i + 1 < v.y.Lam

variable {p : PanelEnv}

/-- The walk over one call's segments is the walk over the line's names. -/
theorem walkA_call (hN : LinesAre p.v.y) (q : Fin 8) (ec : E) (el : Array E) (s : Panels) :
    (p.v.y.calls.getD q.val default).segs.foldl (fun s g => panelA p ec el g.name s) s =
      ((fams q).map segName).foldl (fun s n => panelA p ec el n s) s := by
  rw [← line_at hN q, List.foldl_map]

/-- **The six panels of the first walk.** -/
theorem panelsA_six (hN : LinesAre p.v.y) (s : Panels) :
    panelsA p s =
      panelA p (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) "LR"
        (panelA p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) "V"
          (panelA p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) "D"
            (panelA p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) "O"
              (panelA p (p.e.getD 0 zeroE) (eqTab (p.v.zl 0)) "U"
                (panelA p (p.e.getD 0 zeroE) (eqTab (p.v.zl 0)) "G" s))))) := by
  have e0 : ∀ s, (p.v.y.calls.getD 0 default).segs.foldl
      (fun s g => panelA p (p.e.getD 0 zeroE) (eqTab (p.v.zl 0)) g.name s) s =
      panelA p (p.e.getD 0 zeroE) (eqTab (p.v.zl 0)) "U"
        (panelA p (p.e.getD 0 zeroE) (eqTab (p.v.zl 0)) "G" s) :=
    fun s => walkA_call hN 0 _ _ s
  have e1 : ∀ s, (p.v.y.calls.getD 1 default).segs.foldl
      (fun s g => panelA p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) g.name s) s =
      panelA p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) "V"
        (panelA p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) "D"
          (panelA p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) "O" s)) :=
    fun s => walkA_call hN 1 _ _ s
  have e2 : ∀ s, (p.v.y.calls.getD 2 default).segs.foldl
      (fun s g => panelA p (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) g.name s) s =
      panelA p (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) "LR" s :=
    fun s => walkA_call hN 2 _ _ s
  unfold panelsA
  rw [callsAC_of_lines hN]
  show (p.v.y.calls.getD 2 default).segs.foldl
      (fun s g => panelA p (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) g.name s)
      ((p.v.y.calls.getD 1 default).segs.foldl
        (fun s g => panelA p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) g.name s)
        ((p.v.y.calls.getD 0 default).segs.foldl
          (fun s g => panelA p (p.e.getD 0 zeroE) (eqTab (p.v.zl 0)) g.name s) s)) = _
  rw [e0, e1, e2]

/-- **THE SUMMARY BEHIND THE FIRST WALK**: the places of six panels; five times the group's layers
and once the layers with routed experts as weight claims; the walk has taken the bits of the down
product's panel. CONDITIONAL: on the eight lines, on R and on profile 4. -/
theorem sm_panelsA (hN : LinesAre p.v.y) (R : PanRd p.v) (h4 : p.v.y.h.p4 = true) :
    Sm p.v.y (panelsA p {})
      (0 + 2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 p.v.y.h.d) +
        2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 p.v.y.h.d) +
        2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 p.v.y.dq) +
        2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 p.v.y.h.f) +
        2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 p.v.y.h.d) +
        2 ^ (ceilLog2 p.v.y.LamM + ceilLog2 p.v.y.h.d))
      (0 + p.v.y.Lam + p.v.y.Lam + p.v.y.Lam + p.v.y.Lam + p.v.y.Lam + p.v.y.LamM)
      (ceilLog2 p.v.y.Lam + ceilLog2 p.v.y.h.f) := by
  rw [panelsA_six hN, panelA_LR_eq, panelA_V_eq, panelA_D_eq, panelA_O_eq, panelA_U_eq,
    panelA_G_eq]
  have sG := sm_weight (sm_empty p.v.y) (p.e.getD 0 zeroE) 0 false p.v.y.h.d
    (fun lam k2 => p.v.shIn (p.v.tensorAt "m" "zt") lam k2)
    (fun lam => mulE ((eqTab (p.v.zl 0)).getD lam zeroE)
      (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lkg))
    (fun i hi yv hyv => shA_some (R.m_zt i hi) hyv)
  have sU := sm_weight sG (p.e.getD 0 zeroE) 0 false p.v.y.h.d
    (fun lam k2 => p.v.shIn (p.v.tensorAt "m" "zt") lam k2)
    (fun lam => mulE ((eqTab (p.v.zl 0)).getD lam zeroE)
      (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lku))
    (fun i hi yv hyv => shA_some (R.m_zt i hi) hyv)
  have sO := sm_weight sU (p.e.getD 1 zeroE) 0 false p.v.y.dq
    (fun lam k2 => if p.v.y.h.p4 then p.v.shIn (p.v.tensorAt "o" "zt") lam k2
      else some (Model.Layer.stubAt p (Model.eqTab p.zt) lam k2))
    (fun lam => mulE ((eqTab (p.v.zl 1)).getD lam zeroE)
      (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lko))
    (fun i hi yv hyv => by
      show (if p.v.y.h.p4 = true then p.v.shIn (p.v.tensorAt "o" "zt") i yv
        else some (Model.Layer.stubAt p (Model.eqTab p.zt) i yv)).isSome = true
      rw [if_pos h4]
      exact shA_some (R.o_zt i hi) hyv)
  have sD := sm_virt sO (p.e.getD 1 zeroE) 0 false p.v.y.h.f
    (fun lam => mulE ((eqTab (p.v.zl 1)).getD lam zeroE)
      (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lkd)) 0
  have sV := sm_weight sD (p.e.getD 1 zeroE) 0 false p.v.y.h.d
    (fun lam k2 => p.v.shIn (p.v.tensorAt "a" "zt") lam k2)
    (fun lam => mulE ((eqTab (p.v.zl 1)).getD lam zeroE)
      (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lkv))
    (fun i hi yv hyv => shA_some (R.a_zt i hi) hyv)
  exact sm_weight sV (p.e.getD 2 zeroE) 0 true p.v.y.h.d
    (fun lam k2 => p.v.shIn (p.v.tensorAt "m" "zt") lam k2)
    (fun lam => mulE ((eqTab (p.v.zl 2)).getD lam zeroE)
      (Model.Layer.kTM p.v.sc (p.v.lay lam) 0))
    (fun i hi yv hyv => shA_some (R.m_zt (2 * i + 1) (R.odd i hi)) hyv)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.walkA_call
#print axioms OnBytes.Road.K4.C.panelsA_six
#print axioms OnBytes.Road.K4.C.sm_panelsA
