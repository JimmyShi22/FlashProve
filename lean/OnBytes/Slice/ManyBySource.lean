-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyBySource.lean: chains of any number of stages at radii below half the stages'
distances, with the counts by source.

OnBytes/Slice/ManyDefs.lean defines a chain from a stage on, with three standard ways to build one.
These carry the error counts that are proved at a radius e below a third of a stage's distance: in a
fold e + 1 for each of the three tables, in the base case e + 1 for the tables before the fold
together. OnBytes/Slice/ManyHolds.lean shows that each block of such a chain is taken off
(`Chain.Holds`), and OnBytes/Slice/ManyErr.lean that all its counts are small if a few that are
written out are (`Chain.err_below`). This file does the same at radii below half the stages'
distances, with the counts of OnBytes/Slice/BlocksBySource.lean: for each of a stage's two codes the
count e + 1 where 3 e is below that code's own distance, else 2^a, the number of the main code's
positions (`Sg.cntC`, `Sg.cntZ`). The readings, the rounds and the code switches' counts are those
of the standard ways.

Main definitions.
 `Chain.lastSrc`, `Chain.stepMidSrc`, `Chain.stepEndSrc`   a base case, a step to a stage that is
                not the last, a step to the last stage: the standard ones with the counts by source.
 `Chain.PlainSrc`   the chain's counts are those by source at each stage's radius.
 `Chain.EachSrc`, `Chain.SmallSrc`   the counts that are written out, and that each is small.
Main theorems.
 `foldSem_src`, `baseSem_src`   a fold and the base case are taken off, in the form of
                OnBytes/Slice/ChainSem.lean.
 `Chain.holds_lastSrc`   the base case. Asked: the stage's sizes are in order, each of its codes has
                a coefficient, 2 e < d, and the two rounds send and draw what a base case's rounds
                do.
 `Chain.holds_stepMidSrc`, `Chain.holds_stepEndSrc`   a step. Asked: both stages' sizes are in
                order; each code of the old stage has a coefficient; 2 e < d at the old stage;
                2 e' < d' at the new stage, for the radius e' with which the rest of the chain
                begins; the rounds are a fold's and a code switch's; the rest of the chain holds.
 `fold_below_src`, `base_below_src`   a fold's and a base case's counts are small if those written
                out are.
 `Chain.err_below_src`   every count of a chain with the counts by source is small if each count
                that is written out in `SmallSrc` is.
 `Chain.errL_below_bat_src`, `Chain.errL_below_bat_blocks`   the same with the batching's round in
                front, over the list of rounds: from `SmallSrc`; and, for any chain, from
                `Chain.BlocksBelow`.
 `Chain.stepMidSrc_heq`, `Chain.stepEndSrc_heq`   a step by source from a stage under two names.

Not claimed. Nothing at half a stage's distance or beyond. Nothing on the sizes of the counts: the
inequalities of `SmallSrc` are hypotheses. Where 3 e is below the stage's distance the counts by
source of a fold are the standard ones, which no theorem here says; the base case by source has
twice e + 1 where the standard one has e + 1 (OnBytes/Slice/BlocksBySource.lean). So below a third a
chain by source is not the standard chain. Nothing on what follows from `Chain.Holds` for a written
protocol. The theorems of the files with Many in their names that are stated for any chain
(`chain_many`, `closes_many`, `Chain.errL_below`, `Chain.below_of_blocks`) hold of these chains as
they stand. The theorems on a chain of OnBytes/Slice/ManyNum.lean,
which are stated under `Chain.Plain`, for `Chain.Small` or for the
standard ways, have no counterpart here. No chain of an example is
built here. Through OnBytes/Slice/NumbersHalf.lean this file
depends on the library's Code/Half.lean.

-/
import OnBytes.Slice.BlocksBySource
import OnBytes.Slice.ManyErr

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run
open scoped ENNReal

/-! ## The two blocks, in the form of ChainSem.lean -/

/-- A fold is taken off below half the stage's distance, with the counts by source. n0 is any
number: the counts do not read it. -/
theorem foldSem_src (s : Sg) (n0 : ℕ) (hs : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d)
    (dE dT : PQ.RD) (hF : FoldRounds dE dT) :
    FoldSem s n0 e dE dT
      (foldErr s dE dT (fun _ => 1) (fun _ => s.cntC e) (fun _ => s.cntZ e) (fun _ => s.cntZ e)) :=
  foldSem_of s n0 s.d e _ _ _ _ (Sg.codesOK hs (by omega)) (foldNums_src hs hp h2) dE dT hF

/-- The base case is taken off below half the stage's distance, with the counts by source. -/
theorem baseSem_src (s : Sg) (hs : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d)
    (dL dB : PQ.RD) {nL aL nB : ℕ} (hL : SendsDraws dL nL 1 0 aL)
    (hB : SendsDraws dB nB 0 s.t s.C.a) :
    BaseSem s e dL dB (baseErr s e (s.cntC e + s.cntZ e) 1 dL dB) :=
  baseSem_of s e (s.cntC e + s.cntZ e) 1 dL dB (baseCodes_src hs hp h2) hL hB

/-! ## The counts are small if those written out are -/

/-- Every count of a fold with lists of one member, the count cC for the main rows and cZ for each
of the two tables of mask rows is at most εs as a share of its round's challenge values, if these
are: the count 1 in the first round; cC + 2 in the repeated round; and, where the stage has mask
variables, cC + 2 cZ + 2 in the repeated round. -/
theorem fold_below_src (s : Sg) (dE dT : PQ.RD) (cC cZ : ℕ) (εs : ℝ≥0∞)
    (hE : RoundBelow 1 dE εs) (hT : RoundBelow (cC + 2) dT εs)
    (hM : s.h ≠ 0 → RoundBelow (cC + (cZ + cZ) + 2) dT εs) :
    Err.Below (foldErr s dE dT (fun _ => 1) (fun _ => cC) (fun _ => cZ) (fun _ => cZ)) εs := by
  by_cases h0 : s.h = 0
  · exact ⟨hE, foldT_below dT εs _ hT (s.h + s.g) _ fun i => by
      show cC + (if i + 1 ≤ s.h then cZ + cZ else 0) + 1 * 2 ≤ _
      rewrite [if_neg (by omega)]
      omega⟩
  · exact ⟨hE, foldT_below dT εs _ (hM h0) (s.h + s.g) _ fun i => by
      show cC + (if i + 1 ≤ s.h then cZ + cZ else 0) + 1 * 2 ≤ _
      split_ifs <;> omega⟩

/-- Both counts of the base case at the radius e, with lists of one member and the count exc for the
tables before the fold, are at most εs as shares of their rounds' challenge values, if these are:
exc + 1 in the first round, and in the second (n - e - 1)^t, with n the number of positions and t
the number of draws. -/
theorem base_below_src (s : Sg) (e exc : ℕ) (dL dB : PQ.RD) (εs : ℝ≥0∞)
    (hL : RoundBelow (exc + 1) dL εs) (hB : RoundBelow ((2 ^ s.C.a - e - 1) ^ s.t) dB εs) :
    Err.Below (baseErr s e exc 1 dL dB) εs :=
  ⟨hL, hB, trivial⟩

namespace Chain

/-! ## The three ways to build a chain -/

/-- A base case with the standard readings and the counts by source. -/
def lastSrc (s : Sg) (e : ℕ) (dL dB : PQ.RD) : Chain s :=
  .last s e dL dB (fun m => lst (sentW dL m) 0) (fun m => shownW s (sentW dB m))
    (baseErr s e (s.cntC e + s.cntZ e) 1 dL dB)

/-- A step to a stage that is not the last, with the standard readings (`stepMid`) and the counts by
source. n0 is s.Z.l. As there, nothing checks what next is. -/
noncomputable def stepMidSrc (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') : Chain s :=
  .step s s' hf s.Z.l e dE dT dS dC (fun m => wordIn s' (colSt s' dS m.1))
    (fun m => wordFr s' (colSt s' dS m.1)) (fun m => wordIn s' (colSt s' dS m.1))
    (foldErr s dE dT (fun _ => 1) (fun _ => s.cntC e) (fun _ => s.cntZ e) (fun _ => s.cntZ e))
    (csErr hf e 1 dS dC) next

/-- A step to the last stage, with the standard readings (`stepEnd`) and the counts by source. n0 is
s.Z.l. As there, nothing checks what next is. -/
noncomputable def stepEndSrc (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') : Chain s :=
  .step s s' hf s.Z.l e dE dT dS dC (fun m => wordIn s' (lastColW dS m.1))
    (fun m => wordFr s' (lastColW dS m.1)) (fun m => wordMk s' (lastMk dS m.1))
    (foldErr s dE dT (fun _ => 1) (fun _ => s.cntC e) (fun _ => s.cntZ e) (fun _ => s.cntZ e))
    (csErr hf e 1 dS dC) next

/-- The base case is taken off at a radius below half the stage's distance. -/
theorem holds_lastSrc {s : Sg} {e : ℕ} {dL dB : PQ.RD} {nL aL nB : ℕ} (hs : s.Sized) (hp : s.Pos)
    (h2 : 2 * e < s.d) (hL : SendsDraws dL nL 1 0 aL) (hB : SendsDraws dB nB 0 s.t s.C.a) :
    (lastSrc s e dL dB).Holds :=
  baseSem_src s hs hp h2 dL dB hL hB

/-- The fold and the code switch of a step, at radii below half the two stages' distances. -/
private theorem step_blocks_src {s s' : Sg} (hf : CsFit s s') {e e' : ℕ} {dE dT dS dC : PQ.RD}
    (hs : s.Sized) (hp : s.Pos) (h2 : 2 * e < s.d) (hF : FoldRounds dE dT)
    (hC : CsRounds s s' dS dC) (hs' : s'.Sized) (h2' : 2 * e' < s'.d) :
    FoldSem s s.Z.l e dE dT (foldErr s dE dT (fun _ => 1) (fun _ => s.cntC e)
        (fun _ => s.cntZ e) (fun _ => s.cntZ e)) ∧
      CsSem hf e e' dS dC (csErr hf e 1 dS dC) :=
  ⟨foldSem_src s s.Z.l hs hp h2 dE dT hF,
    csSem_of hf e e' 1 (Sg.fit_cMid hs).laws (Sg.list_cIn hs' h2') dS dC hC⟩

/-- A step to a stage that is not the last holds if the rest of the chain does. -/
theorem holds_stepMidSrc {s s' : Sg} (hf : CsFit s s') {e : ℕ} {dE dT dS dC : PQ.RD}
    {next : Chain s'} (hs : s.Sized) (hp : s.Pos) (h2 : 2 * e < s.d) (hF : FoldRounds dE dT)
    (hC : CsRounds s s' dS dC) (hs' : s'.Sized) (h2' : 2 * next.rad < s'.d) (hn : next.Holds) :
    (stepMidSrc s s' hf e dE dT dS dC next).Holds :=
  have h := step_blocks_src hf hs hp h2 hF hC hs' h2'
  show _ ∧ _ ∧ _ from ⟨h.1, h.2, hn⟩

/-- A step to the last stage holds if the rest of the chain does. -/
theorem holds_stepEndSrc {s s' : Sg} (hf : CsFit s s') {e : ℕ} {dE dT dS dC : PQ.RD}
    {next : Chain s'} (hs : s.Sized) (hp : s.Pos) (h2 : 2 * e < s.d) (hF : FoldRounds dE dT)
    (hC : CsRounds s s' dS dC) (hs' : s'.Sized) (h2' : 2 * next.rad < s'.d) (hn : next.Holds) :
    (stepEndSrc s s' hf e dE dT dS dC next).Holds :=
  have h := step_blocks_src hf hs hp h2 hF hC hs' h2'
  show _ ∧ _ ∧ _ from ⟨h.1, h.2, hn⟩

/-! ## All counts are small if those written out are -/

/-- The chain's counts are those by source at each stage's radius e, with lists of one member. -/
def PlainSrc : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ εb => εb = baseErr s e (s.cntC e + s.cntZ e) 1 dL dB
  | _, .step s _ hf _ e dE dT dS dC _ _ _ εf εc next =>
    εf = foldErr s dE dT (fun _ => 1) (fun _ => s.cntC e) (fun _ => s.cntZ e)
        (fun _ => s.cntZ e) ∧
      εc = csErr hf e 1 dS dC ∧ next.PlainSrc

/-- The base case by source has the counts by source. -/
theorem plainSrc_lastSrc (s : Sg) (e : ℕ) (dL dB : PQ.RD) : (lastSrc s e dL dB).PlainSrc := rfl

/-- The step by source to a stage that is not the last has the counts by source, if what follows
has. -/
theorem plainSrc_stepMidSrc (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') (h : next.PlainSrc) : (stepMidSrc s s' hf e dE dT dS dC next).PlainSrc :=
  ⟨rfl, rfl, h⟩

/-- The step by source to the last stage has the counts by source, if what follows has. -/
theorem plainSrc_stepEndSrc (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') (h : next.PlainSrc) : (stepEndSrc s s' hf e dE dT dS dC next).PlainSrc :=
  ⟨rfl, rfl, h⟩

/-- P holds of each count that is written out, with its round. At a stage that is folded and
switched, with the radius e: the count 1 in the fold's first round; cntC + 2 in its repeated round;
where the stage has mask variables, cntC + 2 cntZ + 2 in the repeated round; the library's count of
the code switch's second round. At the last stage: cntC + cntZ + 1 in the first round and (n - e -
1)^t in the second, with n the number of positions and t the number of draws. In `SmallSrc`, where
the stage has mask variables, the second follows from the third (`RoundBelow.mono`); a stage with g
= 0 has no round with the second count. -/
def EachSrc (P : ℕ → PQ.RD → Prop) : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ _ =>
    P (s.cntC e + s.cntZ e + 1) dL ∧ P ((2 ^ s.C.a - e - 1) ^ s.t) dB
  | _, .step s _ hf _ e dE dT _ dC _ _ _ _ _ next =>
    P 1 dE ∧ P (s.cntC e + 2) dT ∧ (s.h ≠ 0 → P (s.cntC e + (s.cntZ e + s.cntZ e) + 2) dT) ∧
      P ((csSw hf).W.err2 e 1) dC ∧ next.EachSrc P

/-- Each count that is written out is at most εs as a share of its round's challenge values. -/
def SmallSrc {s : Sg} (c : Chain s) (εs : ℝ≥0∞) : Prop := c.EachSrc fun n d => RoundBelow n d εs

/-- With the counts by source, the inequalities that are written out bound every block's counts. -/
theorem blocks_of_smallSrc {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (hp : c.PlainSrc)
    (h : c.SmallSrc εs) : c.BlocksBelow εs := by
  induction c with
  | last s e dL dB fu fs εb =>
    have hb : εb = baseErr s e (s.cntC e + s.cntZ e) 1 dL dB := hp
    subst hb
    exact base_below_src s e _ dL dB εs h.1 h.2
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    obtain ⟨hf', hc', hn⟩ := hp
    obtain ⟨hE, hT, hM, hC, hN⟩ := h
    subst hf' hc'
    exact ⟨fold_below_src s dE dT _ _ εs hE hT hM, cs_below hf e dS dC εs hC, ih hn hN⟩

/-- Every count of a chain that has the counts by source is at most εs as a share of its round's
challenge values, if each count that is written out in `SmallSrc` is. Nothing is asked of the rounds
in which a tree is sent: their counts are 0. -/
theorem err_below_src {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (hp : c.PlainSrc) (h : c.SmallSrc εs) :
    Err.Below c.err εs :=
  c.below_of_blocks εs (c.blocks_of_smallSrc εs hp h)

/-- For any chain. The batching's count, which is the number of rows less one, and the chain's
counts, over the list of the batching's round and the chain's rounds: each is at most εs as a share
of its round's challenge values, if the batching's is and every block's counts are. -/
theorem errL_below_bat_blocks {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (h : c.BlocksBelow εs) (S : Sz)
    (dA : PQ.RD) (hA : RoundBelow (1 * (S.nRows - 1)) dA εs) :
    Err.Below (s := PQ.uL (ckP .two) (dA :: c.rds)) (batErr S 1 dA, c.errL) εs :=
  ⟨hA, c.errL_below εs (c.below_of_blocks εs h)⟩

/-- The same for a chain with the counts by source, from the counts that are written out. -/
theorem errL_below_bat_src {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (hp : c.PlainSrc)
    (h : c.SmallSrc εs) (S : Sz) (dA : PQ.RD) (hA : RoundBelow (1 * (S.nRows - 1)) dA εs) :
    Err.Below (s := PQ.uL (ckP .two) (dA :: c.rds)) (batErr S 1 dA, c.errL) εs :=
  c.errL_below_bat_blocks εs (c.blocks_of_smallSrc εs hp h) S dA hA

/-! ## The same chain from a stage under two names -/

/-- A step by source to a stage that is not the last, written from two stages that are equal. -/
theorem stepMidSrc_heq {s s1 s' : Sg} (h : s = s1) (hf : CsFit s s') (hf1 : CsFit s1 s') (e : ℕ)
    (dE dT dS dC : PQ.RD) (next : Chain s') :
    HEq (stepMidSrc s s' hf e dE dT dS dC next) (stepMidSrc s1 s' hf1 e dE dT dS dC next) := by
  subst h
  rfl

/-- A step by source to the last stage, written from two stages that are equal. -/
theorem stepEndSrc_heq {s s1 s' : Sg} (h : s = s1) (hf : CsFit s s') (hf1 : CsFit s1 s') (e : ℕ)
    (dE dT dS dC : PQ.RD) (next : Chain s') :
    HEq (stepEndSrc s s' hf e dE dT dS dC next) (stepEndSrc s1 s' hf1 e dE dT dS dC next) := by
  subst h
  rfl

end Chain

end OnBytes.Slice
