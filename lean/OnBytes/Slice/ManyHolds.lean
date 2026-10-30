-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyHolds.lean: the three standard ways to build a chain keep `Chain.Holds`, at radii
below a third of the stages' distances.

OnBytes/Slice/ManyDefs.lean defines a chain from a stage on and says by recursion what it means that
each of its blocks is taken off (`Chain.Holds`). It has three ways to build a chain with the
standard readings and the error counts for lists of one member: a base case (`Chain.lastStd`), a
step to a stage that is not the last (`Chain.stepMid`), a step to the last stage (`Chain.stepEnd`).
This file proves `Holds` for each of the three from facts on public sizes and rounds. The proofs put
together the three statements of OnBytes/Slice/ChainSem.lean on a fold, a code switch and the base
case with the numbers of OnBytes/Slice/Numbers.lean, FoldAt.lean and BaseAt.lean.

Main theorems.
 `Chain.holds_lastStd`   the base case. Asked: the stage's sizes are in order, 3 e < d, and the two
                         rounds send and draw what a base case's rounds do.
 `Chain.holds_stepMid`, `Chain.holds_stepEnd`   a step. Asked: both stages' sizes are in order;
                         3 e < d at the old stage; 2 e' < d' at the new stage, for the radius e'
                         with which the rest of the chain begins; the rounds are a fold's and a
                         code switch's; the rest of the chain holds.
Not claimed. Nothing at a third of a distance or beyond. Nothing on the sizes of the error counts.
Nothing on chains with other readings or other counts.

-/
import OnBytes.Slice.ManyDefs
import OnBytes.Slice.FoldAt
import OnBytes.Slice.BaseAt

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

namespace Chain

/-- The base case with the standard readings is taken off at a radius below a third of the stage's
distance. -/
theorem holds_lastStd {s : Sg} {e : ℕ} {dL dB : PQ.RD} {nL aL nB : ℕ} (hs : s.Sized)
    (h3 : 3 * e < s.d) (hL : SendsDraws dL nL 1 0 aL) (hB : SendsDraws dB nB 0 s.t s.C.a) :
    (lastStd s e dL dB).Holds :=
  baseSem_of s e (e + 1) 1 dL dB (baseCodes_third hs h3) hL hB

/-- The fold and the code switch of a step, at a radius e below a third of the old stage's distance
and a radius e' below half the new stage's distance. -/
private theorem step_blocks {s s' : Sg} (hf : CsFit s s') {e e' : ℕ} {dE dT dS dC : PQ.RD}
    (hs : s.Sized) (h3 : 3 * e < s.d) (hF : FoldRounds dE dT) (hC : CsRounds s s' dS dC)
    (hs' : s'.Sized) (h2 : 2 * e' < s'.d) :
    FoldSem s s.Z.l e dE dT
        (foldErr s dE dT (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1)) ∧
      CsSem hf e e' dS dC (csErr hf e 1 dS dC) :=
  ⟨foldSem_of s s.Z.l s.d e _ _ _ _ (Sg.codesOK hs (by omega)) (foldNums_third hs h3) dE dT hF,
    csSem_of hf e e' 1 (Sg.fit_cMid hs).laws (Sg.list_cIn hs' h2) dS dC hC⟩

/-- A step to a stage that is not the last holds if the rest of the chain does. -/
theorem holds_stepMid {s s' : Sg} (hf : CsFit s s') {e : ℕ} {dE dT dS dC : PQ.RD}
    {next : Chain s'} (hs : s.Sized) (h3 : 3 * e < s.d) (hF : FoldRounds dE dT)
    (hC : CsRounds s s' dS dC) (hs' : s'.Sized) (h2 : 2 * next.rad < s'.d) (hn : next.Holds) :
    (stepMid s s' hf e dE dT dS dC next).Holds :=
  have h := step_blocks hf hs h3 hF hC hs' h2
  show _ ∧ _ ∧ _ from ⟨h.1, h.2, hn⟩

/-- A step to the last stage holds if the rest of the chain does. -/
theorem holds_stepEnd {s s' : Sg} (hf : CsFit s s') {e : ℕ} {dE dT dS dC : PQ.RD}
    {next : Chain s'} (hs : s.Sized) (h3 : 3 * e < s.d) (hF : FoldRounds dE dT)
    (hC : CsRounds s s' dS dC) (hs' : s'.Sized) (h2 : 2 * next.rad < s'.d) (hn : next.Holds) :
    (stepEnd s s' hf e dE dT dS dC next).Holds :=
  have h := step_blocks hf hs h3 hF hC hs' h2
  show _ ∧ _ ∧ _ from ⟨h.1, h.2, hn⟩

end Chain

end OnBytes.Slice
