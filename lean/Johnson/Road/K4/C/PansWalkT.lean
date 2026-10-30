-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PansWalkT.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the batched sumcheck's panels: the
verifier's second walk over the segments (panelsT, OnBytes/Model/LayerPanels.lean), at the calls 0,
1, 2 and 5 of the library's eight lines: IT RETURNS, and the summary of the list behind it (Sm,
PansSum.lean). One definition; statements and proofs. General in the sizes.

  `stepCall`, `panelsT_eq`   the walk's step at one call.
  `callT0`, `callT1`, `callT2`, `callT5`   the four calls.
  **`sm_panelsT`**           the second walk returns; the summary behind it.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. AT A
LAYOUT WHOSE EIGHT LINES OF CALLS ARE THE LIBRARY's, WITH ROUTED EXPERTS. Public data alone:
numbers, and whether a form IS THERE; nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.PansStepsT

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Panels PanelEnv panelT panelsT)

/-- The second walk's step at call number q. -/
def stepCall (p : PanelEnv) (s : Panels) (q : ℕ) : Option Panels :=
  (p.v.y.calls.getD q default).segs.foldlM
    (fun s g => panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s) s

/-- The second walk is the walk of stepCall. -/
theorem panelsT_eq (p : PanelEnv) (TS : List ℕ) (s : Panels) :
    panelsT p TS s = TS.foldlM (stepCall p) s := rfl

variable {p : PanelEnv} {s : Panels} {pl nv wD : ℕ}

/-- Call 0: the segments G, U. -/
theorem callT0 (hN : LinesAre p.v.y) (h3 : p.v.y.h.p3 = true) (R : PanRd p.v)
    (hk : ceilLog2 p.v.y.h.fe = p.v.y.lfe) (H : Sm p.v.y s pl nv wD) :
    ∃ s', stepCall p s 0 = some s' ∧ Sm p.v.y s'
      (pl + p.v.y.LamM * 2 ^ (ceilLog2 (max p.v.y.h.NE 1) + ceilLog2 p.v.y.h.d) +
        p.v.y.LamM * 2 ^ (ceilLog2 (max p.v.y.h.NE 1) + ceilLog2 p.v.y.h.d))
      (nv + p.v.y.LamM + p.v.y.LamM) wD := by
  obtain ⟨s1, h1, H1⟩ := step_tri h3 R hk (p.e.getD 0 zeroE) (eqTab (p.v.zl 0))
    (sn := "G") (Or.inl rfl) H
  obtain ⟨s2, h2, H2⟩ := step_tri h3 R hk (p.e.getD 0 zeroE) (eqTab (p.v.zl 0))
    (sn := "U") (Or.inr (Or.inl rfl)) H1
  refine ⟨s2, (walkT_call hN 0 _ _ s).trans ?_, H2⟩
  show (["G", "U"].foldlM
    (fun s n => panelT p (p.e.getD 0 zeroE) (eqTab (p.v.zl 0)) n s) s) = some s2
  rw [foldlM_cons_some (f := fun s n => panelT p (p.e.getD 0 zeroE) (eqTab (p.v.zl 0)) n s) h1,
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 0 zeroE) (eqTab (p.v.zl 0)) n s) h2]
  rfl

/-- Call 1: the segments N1, N1H, N2, N2H, O, D, V. -/
theorem callT1 (hN : LinesAre p.v.y) (h3 : p.v.y.h.p3 = true) (hNW : p.v.y.NW = 2)
    (R : PanRd p.v) (hk : ceilLog2 p.v.y.h.fe = p.v.y.lfe) (g1 : HasSeg p.v.y "N1")
    (g2 : HasSeg p.v.y "N2") (H : Sm p.v.y s pl nv wD) :
    ∃ s', stepCall p s 1 = some s' ∧ Sm p.v.y s'
      (pl + 2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 1) + 2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 1) +
        p.v.y.LamM * 2 ^ (ceilLog2 (max p.v.y.h.NE 1) + ceilLog2 p.v.y.h.fe))
      (nv + p.v.y.LamM) wD := by
  obtain ⟨s1, h1, H1⟩ := step_norm hNW R (p.e.getD 1 zeroE) (eqTab (p.v.zl 1))
    (sn := "N1") (Or.inl rfl) g1 H
  obtain ⟨s2, h2, H2⟩ := step_norm hNW R (p.e.getD 1 zeroE) (eqTab (p.v.zl 1))
    (sn := "N2") (Or.inr rfl) g2 H1
  obtain ⟨s3, h3', H3⟩ := step_tri h3 R hk (p.e.getD 1 zeroE) (eqTab (p.v.zl 1))
    (sn := "D") (Or.inr (Or.inr rfl)) H2
  refine ⟨s3, (walkT_call hN 1 _ _ s).trans ?_, H3⟩
  show (["N1", "N1H", "N2", "N2H", "O", "D", "V"].foldlM
    (fun s n => panelT p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) n s) s) = some s3
  rw [foldlM_cons_some (f := fun s n => panelT p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) n s) h1,
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) n s)
      (panelT_N1H_skip _ _ s1),
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) n s) h2,
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) n s)
      (panelT_N2H_skip _ _ s2),
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) n s)
      (panelT_O_skip _ _ s2),
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) n s) h3',
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 1 zeroE) (eqTab (p.v.zl 1)) n s)
      (panelT_V_skip _ _ s3)]
  rfl

/-- Call 2: the segments QK, QKH, XR, LR, LT, DD. -/
theorem callT2 (hN : LinesAre p.v.y) (h3 : p.v.y.h.p3 = true) (R : PanRd p.v)
    (g1 : HasSeg p.v.y "XR") (g2 : HasSeg p.v.y "DD") (H : Sm p.v.y s pl nv wD) :
    ∃ s', stepCall p s 2 = some s' ∧ Sm p.v.y s'
      (pl + 2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 p.v.y.h.d) +
        2 ^ (ceilLog2 p.v.y.LamM + ceilLog2 1) +
        2 ^ (ceilLog2 p.v.y.LamM + ceilLog2 p.v.y.h.NE))
      (nv + p.v.y.Lam) wD := by
  obtain ⟨s1, h1, H1⟩ := step_QK R (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) H
  obtain ⟨s2, h2, H2⟩ := step_XR h3 R (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) g1 H1
  obtain ⟨s3, h3', H3⟩ := step_sel h3 R (p.e.getD 2 zeroE) (eqTab (p.v.zl 2))
    (sn := "DD") (Or.inl rfl) g2 H2
  refine ⟨s3, (walkT_call hN 2 _ _ s).trans ?_, H3⟩
  show (["QK", "QKH", "XR", "LR", "LT", "DD"].foldlM
    (fun s n => panelT p (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) n s) s) = some s3
  rw [foldlM_cons_some (f := fun s n => panelT p (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) n s) h1,
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) n s)
      (panelT_QKH_skip _ _ s1),
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) n s) h2,
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) n s)
      (panelT_LR_skip _ _ s2),
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) n s)
      (panelT_LT_skip _ _ s2),
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 2 zeroE) (eqTab (p.v.zl 2)) n s) h3']
  rfl

/-- Call 5: the segments MR, CG. -/
theorem callT5 (hN : LinesAre p.v.y) (h3 : p.v.y.h.p3 = true) (R : PanRd p.v)
    (g1 : HasSeg p.v.y "MR") (H : Sm p.v.y s pl nv wD) :
    ∃ s', stepCall p s 5 = some s' ∧ Sm p.v.y s'
      (pl + 2 ^ (ceilLog2 p.v.y.LamM + ceilLog2 p.v.y.h.NE)) nv wD := by
  obtain ⟨s1, h1, H1⟩ := step_sel h3 R (p.e.getD 5 zeroE) (eqTab (p.v.zl 5))
    (sn := "MR") (Or.inr rfl) g1 H
  refine ⟨s1, (walkT_call hN 5 _ _ s).trans ?_, H1⟩
  show (["MR", "CG"].foldlM
    (fun s n => panelT p (p.e.getD 5 zeroE) (eqTab (p.v.zl 5)) n s) s) = some s1
  rw [foldlM_cons_some (f := fun s n => panelT p (p.e.getD 5 zeroE) (eqTab (p.v.zl 5)) n s) h1,
    foldlM_cons_some (f := fun s n => panelT p (p.e.getD 5 zeroE) (eqTab (p.v.zl 5)) n s)
      (panelT_CG_skip _ _ s1)]
  rfl

/-- **THE SECOND WALK RETURNS, AND THE SUMMARY BEHIND IT.** CONDITIONAL: on the eight lines, routed
experts, two writes a layer (hNW), R, the bits of an expert's inner width (hk), and that the five
segments named are held by some call (hseg). -/
theorem sm_panelsT (hN : LinesAre p.v.y) (h3 : p.v.y.h.p3 = true) (hNW : p.v.y.NW = 2)
    (R : PanRd p.v) (hk : ceilLog2 p.v.y.h.fe = p.v.y.lfe)
    (hseg : ∀ n ∈ ["N1", "N2", "XR", "DD", "MR"], HasSeg p.v.y n) (H : Sm p.v.y s pl nv wD) :
    ∃ s', panelsT p [0, 1, 2, 5] s = some s' ∧ Sm p.v.y s'
      (pl + p.v.y.LamM * 2 ^ (ceilLog2 (max p.v.y.h.NE 1) + ceilLog2 p.v.y.h.d) +
        p.v.y.LamM * 2 ^ (ceilLog2 (max p.v.y.h.NE 1) + ceilLog2 p.v.y.h.d) +
        2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 1) + 2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 1) +
        p.v.y.LamM * 2 ^ (ceilLog2 (max p.v.y.h.NE 1) + ceilLog2 p.v.y.h.fe) +
        2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 p.v.y.h.d) +
        2 ^ (ceilLog2 p.v.y.LamM + ceilLog2 1) +
        2 ^ (ceilLog2 p.v.y.LamM + ceilLog2 p.v.y.h.NE) +
        2 ^ (ceilLog2 p.v.y.LamM + ceilLog2 p.v.y.h.NE))
      (nv + p.v.y.LamM + p.v.y.LamM + p.v.y.LamM + p.v.y.Lam) wD := by
  obtain ⟨s0, c0, H0⟩ := callT0 hN h3 R hk H
  obtain ⟨s1, c1, H1⟩ := callT1 hN h3 hNW R hk (hseg _ (by simp)) (hseg _ (by simp)) H0
  obtain ⟨s2, c2, H2⟩ := callT2 hN h3 R (hseg _ (by simp)) (hseg _ (by simp)) H1
  obtain ⟨s5, c5, H5⟩ := callT5 hN h3 R (hseg _ (by simp)) H2
  refine ⟨s5, ?_, H5⟩
  rw [panelsT_eq, foldlM_cons_some c0, foldlM_cons_some c1, foldlM_cons_some c2,
    foldlM_cons_some c5]
  rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.panelsT_eq
#print axioms OnBytes.Road.K4.C.callT0
#print axioms OnBytes.Road.K4.C.callT1
#print axioms OnBytes.Road.K4.C.callT2
#print axioms OnBytes.Road.K4.C.callT5
#print axioms OnBytes.Road.K4.C.sm_panelsT
