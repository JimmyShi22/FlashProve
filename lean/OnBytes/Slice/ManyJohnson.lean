-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyJohnson.lean: UNDER A NAMED, UNPROVED STATEMENT ON TWO CODES AT EACH STAGE: the
rounds of a proximity test after the batching, for any number of stages, at radii below the Johnson
radius.

This file gives three ways to build a chain of stages (`Chain`, OnBytes/Slice/ManyDefs.lean: the
rounds after the batching) at radii below the Johnson radius, and shows, under the hypothesis named
below, that each block of a chain so built is taken off (`Chain.Holds`).
The lists are the Johnson bound's (`Sg.lstJ`). The counts bC and
bZ of each stage are letters, and that they bound the exceptional points of a line is the named
hypothesis `Sg.CountsAt` of OnBytes/Slice/BlocksJohnson.lean, asked at every stage that is folded
and at the last. `chain_many` (OnBytes/Slice/ManySem.lean), which asks `Chain.Holds` alone, holds of
these chains. `closes_many` (OnBytes/Slice/ManyCloses.lean) sets a chain under the written link's
batching and asks that batching's statement; OnBytes/Slice/KeyExit.lean has the like `BatSemAt`
from a bound on the lists at the radius (`batSemAt_of`), and no theorem in this library states it
at the Johnson bound's lists. Every theorem that goes further (to the standard readings, a group,
a key or a file)
asks besides that twice the first radius be below the stage's distance (`closes_many_std` and its
like).

Main definitions: `Chain.lastJ`, `Chain.stepMidJ`, `Chain.stepEndJ`.
Main theorems.
 `foldSem_joh`, `baseSem_joh`   the two blocks in the form of OnBytes/Slice/ChainSem.lean.
 `Chain.holds_lastJ`, `Chain.holds_stepMidJ`, `Chain.holds_stepEndJ`   each way of building a chain
                gives a chain whose blocks are taken off.
 `fold_below_joh`, `base_below_joh`   every count of a block is small if those written out are.

Not claimed. THIS IS NO PROOF OF SOUNDNESS AT THE JOHNSON RADIUS. No statement on a proof, a file or
a verifier's yes follows from this file at a radius of half the distance or more. Nothing here on
the batching before the first fold. That `Sg.CountsAt` holds at a radius of half the distance or
more, at counts of any use, is not shown (see the head of OnBytes/Slice/BlocksJohnson.lean). No
chain is built here, and no number is stated at any file. That the planner's numbers under the rule
of the Johnson radius are these counts and lists is not shown. Nothing on a stored table, its
decoder, the link between two stored tables or a record. A whole chain's counts are the matter of
OnBytes/Slice/ManyJohnsonErr.lean: with lists of L members a code switch's first round has the count
(L choose 2) times the sample's number, which is 0 for lists of one member.

-/
import OnBytes.Slice.BlocksJohnson
import OnBytes.Slice.ManyBySource

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run
open scoped ENNReal

/-! ## The two blocks, in the form of ChainSem.lean -/

/-- A fold is taken off below the Johnson radius, under the named hypothesis. n0 is any number: the
counts do not read it. -/
theorem foldSem_joh (s : Sg) (n0 : ℕ) (hs : s.Sized) {e bC bZ : ℕ} (hj : s.InJ e)
    (hc : s.CountsAt e bC bZ) (dE dT : PQ.RD) (hF : FoldRounds dE dT) :
    FoldSem s n0 e dE dT
      (foldErr s dE dT (fun _ => s.lstJ e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ)) :=
  foldSem_of s n0 s.d e _ _ _ _ (Sg.codesOK hs hj.1) (foldNums_joh hs hj hc) dE dT hF

/-- The base case is taken off below the Johnson radius, under the named hypothesis. -/
theorem baseSem_joh (s : Sg) (hs : s.Sized) {e bC bZ : ℕ} (hj : s.InJ e)
    (hc : s.CountsAt e bC bZ) (dL dB : PQ.RD) {nL aL nB : ℕ} (hL : SendsDraws dL nL 1 0 aL)
    (hB : SendsDraws dB nB 0 s.t s.C.a) :
    BaseSem s e dL dB (baseErr s e (bC + bZ) (s.lstJ e) dL dB) :=
  baseSem_of s e (bC + bZ) (s.lstJ e) dL dB (baseCodes_joh hs hj hc) hL hB

/-! ## The counts are small if those written out are -/

/-- Every count of a fold with lists of L members, the count cC for the main rows and cZ for each of
the two tables of mask rows is at most εs as a share of its round's challenge values, if these are:
the count L in the first round; cC + 2 L in the repeated round; and, where the stage has mask
variables, cC + 2 cZ + 2 L in the repeated round. -/
theorem fold_below_joh (s : Sg) (dE dT : PQ.RD) (cC cZ L : ℕ) (εs : ℝ≥0∞)
    (hE : RoundBelow L dE εs) (hT : RoundBelow (cC + L * 2) dT εs)
    (hM : s.h ≠ 0 → RoundBelow (cC + (cZ + cZ) + L * 2) dT εs) :
    Err.Below (foldErr s dE dT (fun _ => L) (fun _ => cC) (fun _ => cZ) (fun _ => cZ)) εs := by
  by_cases h0 : s.h = 0
  · exact ⟨hE, foldT_below dT εs _ hT (s.h + s.g) _ fun i => by
      show cC + (if i + 1 ≤ s.h then cZ + cZ else 0) + L * 2 ≤ _
      rewrite [if_neg (by omega)]
      omega⟩
  · exact ⟨hE, foldT_below dT εs _ (hM h0) (s.h + s.g) _ fun i => by
      show cC + (if i + 1 ≤ s.h then cZ + cZ else 0) + L * 2 ≤ _
      split_ifs <;> omega⟩

/-- Both counts of the base case at the radius e, with lists of L members and the count exc for the
tables before the fold, are at most εs as shares of their rounds' challenge values, if these are:
exc + L in the first round, and in the second (n - e - 1)^t, with n the number of positions and t
the number of draws. -/
theorem base_below_joh (s : Sg) (e exc L : ℕ) (dL dB : PQ.RD) (εs : ℝ≥0∞)
    (hL : RoundBelow (exc + L) dL εs) (hB : RoundBelow ((2 ^ s.C.a - e - 1) ^ s.t) dB εs) :
    Err.Below (baseErr s e exc L dL dB) εs :=
  ⟨hL, hB, trivial⟩

namespace Chain

/-! ## The three ways to build a chain -/

/-- A base case with the standard readings, the counts bC and bZ and the Johnson bound's list. -/
def lastJ (s : Sg) (e bC bZ : ℕ) (dL dB : PQ.RD) : Chain s :=
  .last s e dL dB (fun m => lst (sentW dL m) 0) (fun m => shownW s (sentW dB m))
    (baseErr s e (bC + bZ) (s.lstJ e) dL dB)

/-- A step to a stage that is not the last, with the standard readings (`stepMid`), the counts bC
and bZ, and the Johnson bound's lists: this stage's in the fold, the next stage's, at the next
radius, in the code switch. n0 is s.Z.l. As there, nothing checks what next is. -/
noncomputable def stepMidJ (s s' : Sg) (hf : CsFit s s') (e bC bZ : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') : Chain s :=
  .step s s' hf s.Z.l e dE dT dS dC (fun m => wordIn s' (colSt s' dS m.1))
    (fun m => wordFr s' (colSt s' dS m.1)) (fun m => wordIn s' (colSt s' dS m.1))
    (foldErr s dE dT (fun _ => s.lstJ e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ))
    (csErr hf e (s'.lstJ next.rad) dS dC) next

/-- A step to the last stage, with the standard readings (`stepEnd`), the counts bC and bZ, and the
Johnson bound's lists as in `stepMidJ`. n0 is s.Z.l. As there, nothing checks what next is. -/
noncomputable def stepEndJ (s s' : Sg) (hf : CsFit s s') (e bC bZ : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') : Chain s :=
  .step s s' hf s.Z.l e dE dT dS dC (fun m => wordIn s' (lastColW dS m.1))
    (fun m => wordFr s' (lastColW dS m.1)) (fun m => wordMk s' (lastMk dS m.1))
    (foldErr s dE dT (fun _ => s.lstJ e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ))
    (csErr hf e (s'.lstJ next.rad) dS dC) next

/-- The base case is taken off below the Johnson radius, under the named hypothesis. -/
theorem holds_lastJ {s : Sg} {e bC bZ : ℕ} {dL dB : PQ.RD} {nL aL nB : ℕ} (hs : s.Sized)
    (hj : s.InJ e) (hc : s.CountsAt e bC bZ) (hL : SendsDraws dL nL 1 0 aL)
    (hB : SendsDraws dB nB 0 s.t s.C.a) : (lastJ s e bC bZ dL dB).Holds :=
  baseSem_joh s hs hj hc dL dB hL hB

/-- The fold and the code switch of a step, at radii below the two stages' Johnson radii. The named
hypothesis is asked of the stage that is folded. -/
private theorem step_blocks_joh {s s' : Sg} (hf : CsFit s s') {e e' bC bZ : ℕ}
    {dE dT dS dC : PQ.RD} (hs : s.Sized) (hj : s.InJ e) (hc : s.CountsAt e bC bZ)
    (hF : FoldRounds dE dT) (hC : CsRounds s s' dS dC) (hs' : s'.Sized) (hj' : s'.InJ e') :
    FoldSem s s.Z.l e dE dT (foldErr s dE dT (fun _ => s.lstJ e) (fun _ => bC) (fun _ => bZ)
        (fun _ => bZ)) ∧
      CsSem hf e e' dS dC (csErr hf e (s'.lstJ e') dS dC) :=
  ⟨foldSem_joh s s.Z.l hs hj hc dE dT hF,
    csSem_of hf e e' (s'.lstJ e') (Sg.fit_cMid hs).laws (Sg.listJ_of (Sg.fit_cIn hs') hj') dS dC hC⟩

/-- A step to a stage that is not the last holds if the rest of the chain does. -/
theorem holds_stepMidJ {s s' : Sg} (hf : CsFit s s') {e bC bZ : ℕ} {dE dT dS dC : PQ.RD}
    {next : Chain s'} (hs : s.Sized) (hj : s.InJ e) (hc : s.CountsAt e bC bZ)
    (hF : FoldRounds dE dT) (hC : CsRounds s s' dS dC) (hs' : s'.Sized) (hj' : s'.InJ next.rad)
    (hn : next.Holds) : (stepMidJ s s' hf e bC bZ dE dT dS dC next).Holds :=
  have h := step_blocks_joh hf hs hj hc hF hC hs' hj'
  show _ ∧ _ ∧ _ from ⟨h.1, h.2, hn⟩

/-- A step to the last stage holds if the rest of the chain does. -/
theorem holds_stepEndJ {s s' : Sg} (hf : CsFit s s') {e bC bZ : ℕ} {dE dT dS dC : PQ.RD}
    {next : Chain s'} (hs : s.Sized) (hj : s.InJ e) (hc : s.CountsAt e bC bZ)
    (hF : FoldRounds dE dT) (hC : CsRounds s s' dS dC) (hs' : s'.Sized) (hj' : s'.InJ next.rad)
    (hn : next.Holds) : (stepEndJ s s' hf e bC bZ dE dT dS dC next).Holds :=
  have h := step_blocks_joh hf hs hj hc hF hC hs' hj'
  show _ ∧ _ ∧ _ from ⟨h.1, h.2, hn⟩

end Chain

end OnBytes.Slice
