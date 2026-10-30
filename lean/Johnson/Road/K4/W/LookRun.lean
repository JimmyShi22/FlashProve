-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/LookRun.lean: CONDITIONAL.

Not shown here. THAT THE PLANES' COLUMNS ARE AT MOST THE LAYOUT's kbm: a hypothesis of
cols_of_ground. Where K4Ground holds: the head of W/Ground.lean (it follows where a hearing returns,
from nine facts on the plan; these hold at a small synthetic plan, given an evaluation's return;
that a hearing returns there is shown by nothing). Of hc no example is known. Nothing on what the
planes' matrix holds. Nothing on soundness, on completeness or on any other property.
No property is claimed.

Two public clauses of `LookAsks` (W/LookAsks.lean), run and cols, from the public facts on the
layout (K4Ground, W/Ground.lean): in the smallness test's list the planes' matrix has 2 ^ lmb rows
and kbm columns, by the library's `tails_pairs` (Johnson/Road/FormsKeysTab.lean).

  `planes_sizes`   the rows and the columns of the planes' matrix in the list.
  `run_of_ground`   the rows are one run of 2 ^ lmb.
  `cols_of_ground`   the planes' columns fit, where they are at most kbm.
-/
import Johnson.Road.K4.W.Ground
import Johnson.Road.FormsKeysTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Reads Heard TableAsk TableAt matIx)
open Inst.Model.FFSeg (Dim)

variable {h : Layer.Shape} {pc : List (List String)} {v : Env} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {H : Heard} {hd : Level}
  {hd2 : Option Level} {pts : List (String × Array E)} {funs : Array HFun} {D : Dim}

/-- **The planes' matrix in the smallness test's list.** CONDITIONAL: on G. -/
theorem planes_sizes (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) :
    (tl.mats.getD (matIx v.y).iB {}).m = 2 ^ v.y.h.lmb ∧
      (tl.mats.getD (matIx v.y).iB {}).k = v.y.kbm := by
  have M : (tl.mats.map fun M => (M.m, M.k)) = (sizesTab v.y).toArray :=
    G.mats.trans (tails_pairs v.y G.grp)
  have hs : tl.mats.size = (sizesTab v.y).length := by
    have := congrArg Array.size M
    simpa using this
  have eB : (matIx v.y).iB = v.y.parts.getD 0 0 + v.y.parts.getD 1 0 + 1 := rfl
  have h1 : (matIx v.y).iB < (sizesTab v.y).length := by
    rw [sizesTab_length, eB]
    omega
  have e := getD_map_sizes tl.mats (i := (matIx v.y).iB) (by rw [hs]; exact h1)
  rw [M] at e
  have t3 : (sizesTab v.y).getD (matIx v.y).iB (0, 0) = (2 ^ v.y.h.lmb, v.y.kbm) := by
    rw [eB]
    exact (getD_three (v.y.parts.getD 0 0) (v.y.parts.getD 1 0) _ _ _ (0, 0)).2.2 1
  have e2 : (sizesTab v.y).toArray.getD (matIx v.y).iB (0, 0) = (2 ^ v.y.h.lmb, v.y.kbm) := by
    rw [← t3]
    simp [Array.getD, List.getD_eq_getElem?_getD, h1]
  rw [e2] at e
  exact ⟨(congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩

/-- The planes' matrix has its rows in one run. CONDITIONAL: on G. -/
theorem run_of_ground (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) :
    (tl.mats.getD (matIx v.y).iB {}).m / 2 ^ v.y.h.lmb = 1 := by
  rw [(planes_sizes G).1]
  exact Nat.div_self (Nat.two_pow_pos _)

/-- The planes' columns fit. CONDITIONAL: on G and hc. -/
theorem cols_of_ground (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) {n : ℕ}
    (hc : n ≤ v.y.kbm) : n ≤ (tl.mats.getD (matIx v.y).iB {}).k := by
  rw [(planes_sizes G).2]
  exact hc

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.planes_sizes
#print axioms OnBytes.Road.K4.W.run_of_ground
#print axioms OnBytes.Road.K4.W.cols_of_ground
