-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyAtLetters.lean: the rounds of a proximity test after the batching, for any number
of stages, with the list sizes and the counts of exceptional points as letters. NOTHING IS SAID OF
THE LETTERS: that they bound lists and counts is asked, block by block.

OnBytes/Slice/ManyBySource.lean builds chains of stages with lists of one member and the counts by
source, OnBytes/Slice/ManyJohnson.lean with the Johnson bound's lists and two counts as letters. The
blocks beneath both take all their numbers as letters (`foldSem_of`, `csSem_of`, `baseSem_of`,
OnBytes/Slice/ChainSem.lean). This file keeps them so. Four functions of a stage and a radius give
the numbers: L the list, mC the count for the main rows, mS the count for the carried mask rows,
which stand beside the main rows in the tables before the fold (the library's S), mW the count for
the fresh mask rows, which the fold's first round sends (the library's W). At a stage both are under
the one code `Sg.cZ`, so the same statement is asked of mS and of mW. A fold at the stage s and the
radius e has L s e, mC s e, mS s e, mW s e, the same in every round of the fold. The base case has
the count mC s e + mS s e for the tables before the fold, and the list L s e. A code switch into the
stage s' has the list L s' e', at the next radius e'. What is asked of the numbers is what the
blocks ask: `SumPar.ErrOK` of the fold's, `BaseCodes` of the base case's, `LdCode.ListAt` of the
code switch's. One letter L is so asked of three kinds of codes: the fold's complexes, the tables
before the fold in the switch into the stage, and pairs of such tables in the base case. The Johnson
bound serves all three, since it reads positions and distance alone; a sharper number for one need
not serve the others.

Main definitions: `Chain.lastAt`, `Chain.stepMidAt`, `Chain.stepEndAt`, `Chain.PlainAt`,
`Chain.EachAt`, `Chain.SmallAt`.
Main theorems.
 `Chain.holds_lastAt`, `Chain.holds_stepMidAt`, `Chain.holds_stepEndAt`   each way of building a
                chain gives one whose blocks are taken off, if the numbers are as the blocks ask.
                Asked besides: of a step that the stage's sizes are in order, e < d, the rounds are
                a fold's and a code switch's, and the rest of the chain holds; of a base case that
                its two rounds send and draw what a base case's do.
 `fold_below_at`   every count of a fold is small if those written out are.
 `Chain.plainAt_lastAt`, `Chain.plainAt_stepMidAt`, `Chain.plainAt_stepEndAt`,
 `Chain.blocks_of_smallAt`, `Chain.err_below_at`   every count of such a chain is small if those
                written out are.
 `Chain.plainAt_of_plainJ`, `Chain.plainAt_of_plainSrc`   the chains of the two other files have
                such numbers.
 `Sg.countsAt_full`   the named hypothesis of OnBytes/Slice/BlocksJohnson.lean holds of every stage
                at every radius at the number of all field elements.

Not claimed. THIS IS NO PROOF OF SOUNDNESS AT ANY RADIUS. That any numbers are as the blocks ask is
shown here of none. At the full count of `Sg.countsAt_full` the count of each repeated round of a
fold and of the base case's first round is no smaller than the number of field elements, which is
the number of values that such a round draws: every challenge value that passes the round's test of
work counts as bad. In a round without work the count is then no smaller a share than 1. In a round
with b test bits the share is about 2^-b (`card_wRound`, `below_round_div`,
OnBytes/Slice/Rates.lean), so these clauses of `SmallAt` can hold there: that share is the work's
alone, and no fact on a code stands behind it. The theorem shows that the hypothesis can be met, no
more. No chain is built, and no number is stated at any file. That the planner's numbers are these
letters is not shown. Every theorem that goes further than `closes_many` (to the standard readings,
a group, a key or a file) asks besides that twice the first radius be below the stage's distance.
Nothing on the batching, a stored table, its link or a record.

-/
import Cb.Gen.FullErrTow
import OnBytes.Slice.ManyJohnsonErr

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run
open scoped ENNReal

/-- The named hypothesis of OnBytes/Slice/BlocksJohnson.lean holds of every stage at every radius at
the number of all field elements (the library's `ldCode_mcaAtFull`). At that number it says nothing
of a code: a count of field elements is at most their number. What the hypothesis assumes is the
size of the two numbers (the head of that file). -/
theorem Sg.countsAt_full (s : Sg) (e : ℕ) :
    s.CountsAt e (Fintype.card GE) (Fintype.card GE) :=
  ⟨ldCode_mcaAtFull _ e, ldCode_mcaAtFull _ e⟩

/-- Every count of a fold with lists of L members and the counts cC, cS, cW for the main rows and
the two tables of mask rows is at most εs as a share of its round's challenge values, if these are:
the count L in the first round; cC + 2 L in the repeated round; and, where the stage has mask
variables, cC + cS + cW + 2 L in the repeated round. -/
theorem fold_below_at (s : Sg) (dE dT : PQ.RD) (cC cS cW L : ℕ) (εs : ℝ≥0∞)
    (hE : RoundBelow L dE εs) (hT : RoundBelow (cC + L * 2) dT εs)
    (hM : s.h ≠ 0 → RoundBelow (cC + (cS + cW) + L * 2) dT εs) :
    Err.Below (foldErr s dE dT (fun _ => L) (fun _ => cC) (fun _ => cS) (fun _ => cW)) εs := by
  by_cases h0 : s.h = 0
  · exact ⟨hE, foldT_below dT εs _ hT (s.h + s.g) _ fun i => by
      show cC + (if i + 1 ≤ s.h then cS + cW else 0) + L * 2 ≤ _
      rewrite [if_neg (by omega)]
      omega⟩
  · exact ⟨hE, foldT_below dT εs _ (hM h0) (s.h + s.g) _ fun i => by
      show cC + (if i + 1 ≤ s.h then cS + cW else 0) + L * 2 ≤ _
      split_ifs <;> omega⟩

namespace Chain
variable (L mC mS mW : Sg → ℕ → ℕ)

/-! ## The three ways to build a chain -/

/-- A base case with the standard readings and the numbers of three of the letters: the count
mC s e + mS s e, the list L s e. mW does not occur and is no argument. -/
def lastAt (s : Sg) (e : ℕ) (dL dB : PQ.RD) : Chain s :=
  .last s e dL dB (fun m => lst (sentW dL m) 0) (fun m => shownW s (sentW dB m))
    (baseErr s e (mC s e + mS s e) (L s e) dL dB)

/-- A step to a stage that is not the last, with the standard readings (`stepMid`) and the numbers
of the four letters: this stage's in the fold, the next stage's list, at the next radius, in the
code switch. n0 is s.Z.l. As there, nothing checks what next is. -/
noncomputable def stepMidAt (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') : Chain s :=
  .step s s' hf s.Z.l e dE dT dS dC (fun m => wordIn s' (colSt s' dS m.1))
    (fun m => wordFr s' (colSt s' dS m.1)) (fun m => wordIn s' (colSt s' dS m.1))
    (foldErr s dE dT (fun _ => L s e) (fun _ => mC s e) (fun _ => mS s e) (fun _ => mW s e))
    (csErr hf e (L s' next.rad) dS dC) next

/-- A step to the last stage, with the standard readings (`stepEnd`) and the numbers of the four
letters as in `stepMidAt`. n0 is s.Z.l. As there, nothing checks what next is. -/
noncomputable def stepEndAt (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') : Chain s :=
  .step s s' hf s.Z.l e dE dT dS dC (fun m => wordIn s' (lastColW dS m.1))
    (fun m => wordFr s' (lastColW dS m.1)) (fun m => wordMk s' (lastMk dS m.1))
    (foldErr s dE dT (fun _ => L s e) (fun _ => mC s e) (fun _ => mS s e) (fun _ => mW s e))
    (csErr hf e (L s' next.rad) dS dC) next

variable {L mC mS mW}

/-- The base case is taken off, if its numbers are as the block asks. -/
theorem holds_lastAt {s : Sg} {e : ℕ} {dL dB : PQ.RD} {nL aL nB : ℕ}
    (hc : BaseCodes s e (mC s e + mS s e) (L s e)) (hL : SendsDraws dL nL 1 0 aL)
    (hB : SendsDraws dB nB 0 s.t s.C.a) : (lastAt L mC mS s e dL dB).Holds :=
  baseSem_of s e _ _ dL dB hc hL hB

/-- The fold and the code switch of a step, if their numbers are as the blocks ask. -/
private theorem step_blocks_at {s s' : Sg} (hf : CsFit s s') {e e' : ℕ} {dE dT dS dC : PQ.RD}
    (hs : s.Sized) (he : e < s.d)
    (hE : (s.par 0).ErrOK e (fun _ => L s e) (fun _ => mC s e) (fun _ => mS s e)
      (fun _ => mW s e))
    (hF : FoldRounds dE dT) (hC : CsRounds s s' dS dC) (hl : s'.cIn.ListAt e' (L s' e')) :
    FoldSem s s.Z.l e dE dT (foldErr s dE dT (fun _ => L s e) (fun _ => mC s e)
        (fun _ => mS s e) (fun _ => mW s e)) ∧
      CsSem hf e e' dS dC (csErr hf e (L s' e') dS dC) :=
  ⟨foldSem_of s s.Z.l s.d e _ _ _ _ (Sg.codesOK hs he) hE dE dT hF,
    csSem_of hf e e' (L s' e') (Sg.fit_cMid hs).laws hl dS dC hC⟩

/-- A step to a stage that is not the last holds if the rest of the chain does. -/
theorem holds_stepMidAt {s s' : Sg} (hf : CsFit s s') {e : ℕ} {dE dT dS dC : PQ.RD}
    {next : Chain s'} (hs : s.Sized) (he : e < s.d)
    (hE : (s.par 0).ErrOK e (fun _ => L s e) (fun _ => mC s e) (fun _ => mS s e)
      (fun _ => mW s e))
    (hF : FoldRounds dE dT) (hC : CsRounds s s' dS dC)
    (hl : s'.cIn.ListAt next.rad (L s' next.rad)) (hn : next.Holds) :
    (stepMidAt L mC mS mW s s' hf e dE dT dS dC next).Holds :=
  have h := step_blocks_at hf hs he hE hF hC hl
  show _ ∧ _ ∧ _ from ⟨h.1, h.2, hn⟩

/-- A step to the last stage holds if the rest of the chain does. -/
theorem holds_stepEndAt {s s' : Sg} (hf : CsFit s s') {e : ℕ} {dE dT dS dC : PQ.RD}
    {next : Chain s'} (hs : s.Sized) (he : e < s.d)
    (hE : (s.par 0).ErrOK e (fun _ => L s e) (fun _ => mC s e) (fun _ => mS s e)
      (fun _ => mW s e))
    (hF : FoldRounds dE dT) (hC : CsRounds s s' dS dC)
    (hl : s'.cIn.ListAt next.rad (L s' next.rad)) (hn : next.Holds) :
    (stepEndAt L mC mS mW s s' hf e dE dT dS dC next).Holds :=
  have h := step_blocks_at hf hs he hE hF hC hl
  show _ ∧ _ ∧ _ from ⟨h.1, h.2, hn⟩

/-! ## All counts are small if those written out are -/

variable (L mC mS mW)

/-- The chain's numbers are those of the four letters at each stage and its radius e; in a code
switch the list is the next stage's at the next radius. Not `OnBytes.Slice.PlainAt`
(a file of this project that is not in this library): write c.PlainAt or Chain.PlainAt. -/
def PlainAt : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ εb => εb = baseErr s e (mC s e + mS s e) (L s e) dL dB
  | _, .step s s' hf _ e dE dT dS dC _ _ _ εf εc next =>
    εf = foldErr s dE dT (fun _ => L s e) (fun _ => mC s e) (fun _ => mS s e)
        (fun _ => mW s e) ∧
      εc = csErr hf e (L s' next.rad) dS dC ∧ next.PlainAt

/-- The base case at the four letters has their numbers. -/
theorem plainAt_lastAt (s : Sg) (e : ℕ) (dL dB : PQ.RD) :
    (lastAt L mC mS s e dL dB).PlainAt L mC mS mW := rfl

/-- The step to a stage that is not the last has their numbers, if what follows has. -/
theorem plainAt_stepMidAt (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') (h : next.PlainAt L mC mS mW) :
    (stepMidAt L mC mS mW s s' hf e dE dT dS dC next).PlainAt L mC mS mW :=
  ⟨rfl, rfl, h⟩

/-- The step to the last stage has their numbers, if what follows has. -/
theorem plainAt_stepEndAt (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') (h : next.PlainAt L mC mS mW) :
    (stepEndAt L mC mS mW s s' hf e dE dT dS dC next).PlainAt L mC mS mW :=
  ⟨rfl, rfl, h⟩

/-- P holds of each count that is written out, with its round. At a stage that is folded and
switched, with the radius e and the next stage's list L' at the next radius: L in the fold's first
round; mC + 2 L in its repeated round; where the stage has mask variables, mC + mS + mW + 2 L in the
repeated round; the library's two counts of the code switch at L'. At the last stage: mC + mS + L in
the first round and (n - e - 1)^t in the second, with n the number of positions and t the number of
draws. In `SmallAt`, where the stage has mask variables, the second follows from the third
(`RoundBelow.mono`); a stage with g = 0 has no round with the second count. -/
def EachAt (P : ℕ → PQ.RD → Prop) : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ _ =>
    P (mC s e + mS s e + L s e) dL ∧ P ((2 ^ s.C.a - e - 1) ^ s.t) dB
  | _, .step s s' hf _ e dE dT dS dC _ _ _ _ _ next =>
    P (L s e) dE ∧ P (mC s e + L s e * 2) dT ∧
      (s.h ≠ 0 → P (mC s e + (mS s e + mW s e) + L s e * 2) dT) ∧
      P ((csSw hf).W.err1 (L s' next.rad)) dS ∧ P ((csSw hf).W.err2 e (L s' next.rad)) dC ∧
      next.EachAt P

/-- Each count that is written out is at most εs as a share of its round's challenge values. -/
def SmallAt {s : Sg} (c : Chain s) (εs : ℝ≥0∞) : Prop :=
  c.EachAt L mC mS mW fun n d => RoundBelow n d εs

variable {L mC mS mW}

/-- With such numbers, the inequalities that are written out bound every block's counts. -/
theorem blocks_of_smallAt {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (hp : c.PlainAt L mC mS mW)
    (h : c.SmallAt L mC mS mW εs) : c.BlocksBelow εs := by
  induction c with
  | last s e dL dB fu fs εb =>
    have hb : εb = baseErr s e (mC s e + mS s e) (L s e) dL dB := hp
    subst hb
    exact base_below_joh s e _ _ dL dB εs h.1 h.2
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    obtain ⟨hf', hc', hn⟩ := hp
    obtain ⟨hE, hT, hM, hS, hC, hN⟩ := h
    subst hf' hc'
    exact ⟨fold_below_at s dE dT _ _ _ _ εs hE hT hM, cs_below_joh hf e _ dS dC εs hS hC,
      ih hn hN⟩

/-- Every count of a chain that has such numbers is at most εs as a share of its round's challenge
values, if each count that is written out in `SmallAt` is. -/
theorem err_below_at {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (hp : c.PlainAt L mC mS mW)
    (h : c.SmallAt L mC mS mW εs) : Err.Below c.err εs :=
  c.below_of_blocks εs (c.blocks_of_smallAt εs hp h)

/-! ## The chains of the two other files -/

/-- A chain with the Johnson bound's lists and the counts cC, cZ has the numbers of the letters
`Sg.lstJ`, cC, cZ, cZ. -/
theorem plainAt_of_plainJ {cC cZ : Sg → ℕ → ℕ} {s : Sg} (c : Chain s) (h : c.PlainJ cC cZ) :
    c.PlainAt Sg.lstJ cC cZ cZ := by
  induction c with
  | last s e dL dB fu fs εb => exact h
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih => exact ⟨h.1, h.2.1, ih h.2.2⟩

/-- A chain with lists of one member and the counts by source has the numbers of the letters 1,
`Sg.cntC`, `Sg.cntZ`, `Sg.cntZ`. -/
theorem plainAt_of_plainSrc {s : Sg} (c : Chain s) (h : c.PlainSrc) :
    c.PlainAt (fun _ _ => 1) Sg.cntC Sg.cntZ Sg.cntZ := by
  induction c with
  | last s e dL dB fu fs εb => exact h
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih => exact ⟨h.1, h.2.1, ih h.2.2⟩

end Chain

end OnBytes.Slice
