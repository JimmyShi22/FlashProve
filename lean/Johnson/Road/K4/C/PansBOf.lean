-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PansBOf.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the batched sumcheck's panels: THE TEST
pansB (Johnson/Desc/First/K4/Returns/Pub/PansB.lean) IS TRUE, as a theorem and without evaluation,
at a structure of forms whose layout is that of the public parameters. The test asks that the
verifier's two walks make the list of panels, that the panels' places and weight claims are as many
as the plan says, and that the end of the batched sumcheck returns. The road: the test is its
lighter form (pansB_eq_L, Pub/Light.lean); the calls of the second walk are 0, 1, 2, 5 (the
library's ts_of_lines, Johnson/Road/FormsKeysPansTS.lean); the two walks return with a summary of
three numbers (PansWalkA.lean, PansWalkT.lean); the three numbers are the plan's own formulas
lamSOf and nclOf (OnBytes/Model/LayerPlan.lean), term by term. General in the sizes. Statements and
proofs.

  `ceilLog2_pow`, `ceilLog2_max`   two facts on the rounded-up logarithm.
  `places_lamS`    the places of all panels add up to lamSOf's inner sum.
  **`pansB_of`**     pansB P v₀ lamS NCLp = true.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. AT A LAYOUT
WHOSE EIGHT LINES OF CALLS ARE THE LIBRARY's, UNDER THE LIBRARY's ELEVEN SWITCHES ALONE, at profile
4. WHAT THE PANELS' SIDES READ (R : PanRd v₀) IS A HYPOTHESIS HERE. That the plan's two numbers are
lamSOf and the panels' share of nclOf (h1, h2) and that the rounds are at most 63 (h63) are
hypotheses on the plan. Public data alone: numbers, and whether a form IS THERE; nothing on what a
form is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.PansWalkT
import Johnson.Road.FormsKeysPansTS
import Johnson.Road.K4.PlanSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Pub layout readsOf lamSOf callsTS stubO panelsA panelsT)
open OnBytes.Desc.First.K4.RtPub (pansB pansL pansB_eq_L stackEndL)

/-- The rounded-up logarithm of a power of two. -/
theorem ceilLog2_pow (k : ℕ) : ceilLog2 (2 ^ k) = k := by
  rw [ceilLog2_eq_clog]
  exact Nat.clog_pow 2 k (by norm_num)

/-- The rounded-up logarithm does not tell 0 from 1. -/
theorem ceilLog2_max (n : ℕ) : ceilLog2 (max n 1) = ceilLog2 n := by
  rcases Nat.eq_zero_or_pos n with e | e
  · subst e
    rfl
  · rw [Nat.max_eq_left e]

/-- **The places of all panels add up to lamSOf's inner sum.** -/
theorem places_lamS {y : Lay} (h3 : y.h.p3 = true) :
    ceilLog2 (0 + 2 ^ (ceilLog2 y.Lam + ceilLog2 y.h.d) + 2 ^ (ceilLog2 y.Lam + ceilLog2 y.h.d) +
        2 ^ (ceilLog2 y.Lam + ceilLog2 y.dq) + 2 ^ (ceilLog2 y.Lam + ceilLog2 y.h.f) +
        2 ^ (ceilLog2 y.Lam + ceilLog2 y.h.d) + 2 ^ (ceilLog2 y.LamM + ceilLog2 y.h.d) +
        y.LamM * 2 ^ (ceilLog2 (max y.h.NE 1) + ceilLog2 y.h.d) +
        y.LamM * 2 ^ (ceilLog2 (max y.h.NE 1) + ceilLog2 y.h.d) +
        2 ^ (ceilLog2 y.Lam + ceilLog2 1) + 2 ^ (ceilLog2 y.Lam + ceilLog2 1) +
        y.LamM * 2 ^ (ceilLog2 (max y.h.NE 1) + ceilLog2 y.h.fe) +
        2 ^ (ceilLog2 y.Lam + ceilLog2 y.h.d) + 2 ^ (ceilLog2 y.LamM + ceilLog2 1) +
        2 ^ (ceilLog2 y.LamM + ceilLog2 y.h.NE) + 2 ^ (ceilLog2 y.LamM + ceilLog2 y.h.NE)) =
      lamSOf y := by
  have c1 : ceilLog2 1 = 0 := rfl
  unfold lamSOf
  dsimp only
  rw [if_pos h3, ceilLog2_max, c1]
  congr 1
  simp only [Nat.add_zero]
  ring

/-- **THE TEST pansB IS TRUE.** CONDITIONAL: on the layout's and the reads' return, the switches,
profile 4, the eight lines, what the panels' sides read (R), and three facts on the plan's numbers
(h1, h2, h63). -/
theorem pansB_of {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {P : Pub} {v₀ : Env}
    {lamS NCLp : ℕ} (hv : v₀.y = P.y) (hy : layout h pc = .ok P.y) (S : Switches h)
    (h4 : h.p4 = true) (hrd : readsOf P.y = .ok P.rd) (hN : LinesAre P.y) (R : PanRd v₀)
    (h1 : lamS = lamSOf P.y) (h2 : NCLp = 6 * P.y.Lam + 4 * P.y.LamM) (h63 : lamS ≤ 63) :
    pansB P v₀ lamS NCLp = true := by
  have A := admitted_of_layout hy S.p3
  have Z := laySizes_of_layout hy
  have es := A.shape
  subst es
  have hy' : layout v₀.y.h pc = .ok v₀.y := by
    rw [hv]
    exact hy
  have hN' : LinesAre v₀.y := by
    rw [hv]
    exact hN
  have h3' : v₀.y.h.p3 = true := by
    rw [hv]
    exact S.p3
  have h4' : v₀.y.h.p4 = true := by
    rw [hv]
    exact h4
  have S' : Switches v₀.y.h := by
    rw [hv]
    exact S
  have hNW : v₀.y.NW = 2 := by
    rw [hv]
    exact A.laid.NW
  have hk : ceilLog2 v₀.y.h.fe = v₀.y.lfe := by
    rw [hv, Z.lfe, if_pos S.p3]
  have hseg : ∀ n ∈ ["N1", "N2", "XR", "DD", "MR"], HasSeg v₀.y n := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact hasSeg_of_layout hy' S' .N1
    · exact hasSeg_of_layout hy' S' .N2
    · exact hasSeg_of_layout hy' S' .XR
    · exact hasSeg_of_layout hy' S' .DD
    · exact hasSeg_of_layout hy' S' .MR
  obtain ⟨pans, hT, HT⟩ := sm_panelsT (p := ⟨v₀, #[], #[], #[], stubO P.y⟩) hN' h3' hNW R hk hseg
    (sm_panelsA (p := ⟨v₀, #[], #[], #[], stubO P.y⟩) hN' R h4')
  have hTS : callsTS P = some [0, 1, 2, 5] := ts_of_lines hy S.p3 hN hrd
  rw [pansB_eq_L]
  unfold pansL
  rw [hTS]
  dsimp only
  rw [hT]
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [HT.pl, beq_iff_eq, h1, ← hv]
    exact places_lamS h3'
  · rw [HT.nv, beq_iff_eq, h2, ← hv]
    show 0 + v₀.y.Lam + v₀.y.Lam + v₀.y.Lam + v₀.y.Lam + v₀.y.Lam + v₀.y.LamM + v₀.y.LamM +
      v₀.y.LamM + v₀.y.LamM + v₀.y.Lam = 6 * v₀.y.Lam + 4 * v₀.y.LamM
    omega
  · rw [List.all_eq_true]
    intro b _
    rw [decide_eq_true_eq]
    omega
  · unfold stackEndL
    have hst : pans.bl.toList.foldlM (OnBytes.Desc.First.K4.RtPub.endStepL P.y) 0 =
        some (ceilLog2 v₀.y.Lam + ceilLog2 v₀.y.h.f) := by
      rw [← hv]
      exact HT.st
    rw [hst]
    show (ceilLog2 v₀.y.Lam + ceilLog2 v₀.y.h.f == P.y.h.ll + P.y.lPf) = true
    rw [beq_iff_eq, hv, Z.Lam, ceilLog2_pow, Z.lPf]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.ceilLog2_pow
#print axioms OnBytes.Road.K4.C.ceilLog2_max
#print axioms OnBytes.Road.K4.C.places_lamS
#print axioms OnBytes.Road.K4.C.pansB_of
