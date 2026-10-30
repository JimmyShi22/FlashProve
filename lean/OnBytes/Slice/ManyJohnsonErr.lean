-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyJohnsonErr.lean: which counts it is enough to have small for the rounds of a
proximity test after the batching, for any number of stages, at radii below the Johnson radius.
ARITHMETIC ON ERROR COUNTS ALONE: that these counts bound anything rests on a named, unproved
statement on two codes at each stage (OnBytes/Slice/ManyJohnson.lean).

OnBytes/Slice/ManyJohnson.lean builds chains whose lists are the Johnson bound's (`Sg.lstJ`) and
whose counts for a main row and a mask row are letters. This file takes these letters from two
functions cC and cZ of a stage and a radius, says what it is for a chain to have such counts
(`Chain.PlainJ`), writes out one count for each kind of round (`Chain.EachJ`), and shows that every
count of the chain is at most εs as a share of its round's challenge values if those written out are
(`Chain.err_below_joh`). With lists of L members a fold's first round has the count L; its repeated
round 2 L beside the codes' counts; the base case's first round L beside them; the second round of
a code switch the library's count at the next stage's list; its first round the library's count for
two members of that list that collide under the sample (`LdSwW.err1`,
Cb/Ld/LdSwitchWords.lean: L choose 2, times the sample's error).



Main definitions: `Chain.PlainJ`, `Chain.EachJ`, `Chain.SmallJ`.
Main theorems: `cs_below_joh`, `Chain.plainJ_lastJ`, `Chain.plainJ_stepMidJ`,
`Chain.plainJ_stepEndJ`, `Chain.blocks_of_smallJ`, `Chain.err_below_joh`.

Not claimed. No count is shown to be small, at no stage and no file. That the planner's numbers
under the rule of the Johnson radius are these counts is not shown. Nothing on the batching's count,
which at lists of L members is L times the number of rows less one: `Chain.errL_below_bat_blocks`
(OnBytes/Slice/ManyBySource.lean) is at lists of one member. Nothing here says that a prover has
lost: see OnBytes/Slice/ManyJohnson.lean, and its head for the hypothesis. Nothing on a stored
table, its link or a record.

-/
import OnBytes.Slice.ManyJohnson

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run
open scoped ENNReal

/-- Both counts of a code switch at the radius e, with lists of L members, are at most εs as shares
of their rounds' challenge values, if the library's two counts are. -/
theorem cs_below_joh {s s' : Sg} (hf : CsFit s s') (e L : ℕ) (dS dC : PQ.RD) (εs : ℝ≥0∞)
    (hS : RoundBelow ((csSw hf).W.err1 L) dS εs) (hC : RoundBelow ((csSw hf).W.err2 e L) dC εs) :
    Err.Below (csErr hf e L dS dC) εs :=
  ⟨hS, hC, trivial⟩

namespace Chain
variable (cC cZ : Sg → ℕ → ℕ)

/-- The chain's counts are cC and cZ at each stage and its radius e, with the Johnson bound's lists:
the stage's own in a fold and in the base case, the next stage's at the next radius in a code
switch. -/
def PlainJ : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ εb => εb = baseErr s e (cC s e + cZ s e) (s.lstJ e) dL dB
  | _, .step s s' hf _ e dE dT dS dC _ _ _ εf εc next =>
    εf = foldErr s dE dT (fun _ => s.lstJ e) (fun _ => cC s e) (fun _ => cZ s e)
        (fun _ => cZ s e) ∧
      εc = csErr hf e (s'.lstJ next.rad) dS dC ∧ next.PlainJ

/-- The base case of OnBytes/Slice/ManyJohnson.lean at these counts has them. -/
theorem plainJ_lastJ (s : Sg) (e : ℕ) (dL dB : PQ.RD) :
    (lastJ s e (cC s e) (cZ s e) dL dB).PlainJ cC cZ := rfl

/-- The step to a stage that is not the last at these counts has them, if what follows has. -/
theorem plainJ_stepMidJ (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') (h : next.PlainJ cC cZ) :
    (stepMidJ s s' hf e (cC s e) (cZ s e) dE dT dS dC next).PlainJ cC cZ :=
  ⟨rfl, rfl, h⟩

/-- The step to the last stage at these counts has them, if what follows has. -/
theorem plainJ_stepEndJ (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') (h : next.PlainJ cC cZ) :
    (stepEndJ s s' hf e (cC s e) (cZ s e) dE dT dS dC next).PlainJ cC cZ :=
  ⟨rfl, rfl, h⟩

/-- P holds of each count that is written out, with its round. Write L for the Johnson bound's list
at the stage and its radius e, and L' for the next stage's at the next radius. At a stage that is
folded and switched: L in the fold's first round; cC + 2 L in its repeated round; where the stage
has mask variables, cC + 2 cZ + 2 L in the repeated round; the library's two counts of the code
switch at L'. At the last stage: cC + cZ + L in the first round and (n - e - 1)^t in the second,
with n the number of positions and t the number of draws. -/
def EachJ (P : ℕ → PQ.RD → Prop) : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ _ =>
    P (cC s e + cZ s e + s.lstJ e) dL ∧ P ((2 ^ s.C.a - e - 1) ^ s.t) dB
  | _, .step s s' hf _ e dE dT dS dC _ _ _ _ _ next =>
    P (s.lstJ e) dE ∧ P (cC s e + s.lstJ e * 2) dT ∧
      (s.h ≠ 0 → P (cC s e + (cZ s e + cZ s e) + s.lstJ e * 2) dT) ∧
      P ((csSw hf).W.err1 (s'.lstJ next.rad)) dS ∧ P ((csSw hf).W.err2 e (s'.lstJ next.rad)) dC ∧
      next.EachJ P

/-- Each count that is written out is at most εs as a share of its round's challenge values. -/
def SmallJ {s : Sg} (c : Chain s) (εs : ℝ≥0∞) : Prop :=
  c.EachJ cC cZ fun n d => RoundBelow n d εs

variable {cC cZ}

/-- With such counts, the inequalities that are written out bound every block's counts. -/
theorem blocks_of_smallJ {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (hp : c.PlainJ cC cZ)
    (h : c.SmallJ cC cZ εs) : c.BlocksBelow εs := by
  induction c with
  | last s e dL dB fu fs εb =>
    have hb : εb = baseErr s e (cC s e + cZ s e) (s.lstJ e) dL dB := hp
    subst hb
    exact base_below_joh s e _ _ dL dB εs h.1 h.2
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    obtain ⟨hf', hc', hn⟩ := hp
    obtain ⟨hE, hT, hM, hS, hC, hN⟩ := h
    subst hf' hc'
    exact ⟨fold_below_joh s dE dT _ _ _ εs hE hT hM, cs_below_joh hf e _ dS dC εs hS hC, ih hn hN⟩

/-- Every count of a chain that has such counts is at most εs as a share of its round's challenge
values, if each count that is written out in `SmallJ` is. -/
theorem err_below_joh {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (hp : c.PlainJ cC cZ)
    (h : c.SmallJ cC cZ εs) : Err.Below c.err εs :=
  c.below_of_blocks εs (c.blocks_of_smallJ εs hp h)

end Chain

end OnBytes.Slice
