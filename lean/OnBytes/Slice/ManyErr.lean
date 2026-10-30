-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyErr.lean: the error counts of a chain of any number of stages, and when each of
them is at most a given share.

OnBytes/Slice/ChainErrAny.lean has this for three stages. Here the chain is a `Chain` of
OnBytes/Slice/ManyDefs.lean, which carries its blocks' counts as fields. The theorem that the prover
has lost (OnBytes/Slice/ManyCloses.lean) has the counts carried to the shape of the list of rounds,
`Chain.errL`, with the batching's count in front: the last theorem here is in that form.

Main definitions.
 `RoundBelow`     a count n in a round d is at most εs as a share of its round's challenge values.
 `Chain.Plain`    the counts are the library's at each stage's radius, with lists of one member.
 `Chain.Each`     a property holds of each count that is written out, with its round: four counts
                  at a stage that is folded and switched, two at the last stage.
 `Chain.Small`    each of these counts is at most εs as such a share.
Main theorems.
 `Chain.err_below`  every count of a chain with `Plain` is at most εs, if `Small` holds.
 `Chain.errL_below`, `Chain.errL_below_bat`  the same for `Chain.errL`, and with the batching's
                  count in front.
 `Chain.plain_lastStd`, `Chain.plain_stepMid`, `Chain.plain_stepEnd`   the standard base case and
                  steps have `Plain`.
 `below_cast`     the bound is kept where a list of counts is carried to an equal shape.

Rounds that ask for work need no word of their own here: a written round's challenge values hold its
test bits. The gain from work shows where `RoundBelow` is proved for a round (`below_round_div`,
OnBytes/Slice/Rates.lean). Proved by induction on the chain.

What this file does not claim. Nothing on the sizes of the counts: `Small` is a hypothesis.
Nothing on whether the prover has lost with these counts.

-/
import OnBytes.Slice.ChainErrAny
import OnBytes.Slice.ManyCloses

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run
open scoped ENNReal

/-- The count n of bad typed values in the written round d is at most εs as a share of its round's
challenge values: n times w is at most εs times their number. A round's challenge values are its
written verifier messages (`(wRound d).Chal`): a string of its hash blocks with a setting of its
test bits. w is the number in the law of the format's sampler: at most w challenge values that pass
the round's test of work go to one typed value. -/
def RoundBelow (n : ℕ) (d : PQ.RD) (εs : ℝ≥0∞) : Prop :=
  ((n * wOf d : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (wRound d).Chal : ℝ≥0∞)

/-- A smaller count is at most εs if a larger count of the same round is. -/
theorem RoundBelow.mono {n n' : ℕ} {d : PQ.RD} {εs : ℝ≥0∞} (h : n ≤ n')
    (H : RoundBelow n' d εs) : RoundBelow n d εs :=
  round_mono d _ n n' h H

/-- A list of counts that is carried to an equal shape meets the bounds that it met. -/
theorem below_cast {s t : Shape} (h : s = t) (ε : Err t) (εs : ℝ≥0∞) (H : Err.Below ε εs) :
    Err.Below (h ▸ ε : Err s) εs := by
  subst h
  exact H

namespace Chain

/-- The chain's counts are the library's at each stage's radius e, with lists of one member: those
of `chainErr` (OnBytes/Slice/ChainErrAny.lean), for each stage of the chain. -/
def Plain : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ εb => εb = baseErr s e (e + 1) 1 dL dB
  | _, .step s _ hf _ e dE dT dS dC _ _ _ εf εc next =>
    εf = foldErr s dE dT (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1) ∧
      εc = csErr hf e 1 dS dC ∧ next.Plain

/-- The standard base case has the library's counts. -/
theorem plain_lastStd (s : Sg) (e : ℕ) (dL dB : PQ.RD) : (lastStd s e dL dB).Plain := rfl

/-- The standard step to a stage that is not the last has the library's counts, if what follows
has. -/
theorem plain_stepMid (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') (h : next.Plain) : (stepMid s s' hf e dE dT dS dC next).Plain :=
  ⟨rfl, rfl, h⟩

/-- The standard step to the last stage has the library's counts, if what follows has. -/
theorem plain_stepEnd (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') (h : next.Plain) : (stepEnd s s' hf e dE dT dS dC next).Plain :=
  ⟨rfl, rfl, h⟩

/-- P holds of each count that is written out, with its round. At a stage that is folded and
switched, with the radius e: the count 1 in the fold's first round; e + 3 in its repeated round;
where the stage has mask variables, 3 (e + 1) + 2 in the repeated round; the library's count of the
code switch's second round. At the last stage: e + 2 in the first round and (n - e - 1)^t in the
second, with n the number of positions and t the number of draws. -/
def Each (P : ℕ → PQ.RD → Prop) : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ _ => P (e + 1 + 1) dL ∧ P ((2 ^ s.C.a - e - 1) ^ s.t) dB
  | _, .step s _ hf _ e dE dT _ dC _ _ _ _ _ next =>
    P 1 dE ∧ P (e + 3) dT ∧ (s.h ≠ 0 → P (e + 1 + (e + 1 + (e + 1)) + 2) dT) ∧
      P ((csSw hf).W.err2 e 1) dC ∧ next.Each P

/-- Each count that is written out is at most εs as a share of its round's challenge values. -/
def Small {s : Sg} (c : Chain s) (εs : ℝ≥0∞) : Prop := c.Each fun n d => RoundBelow n d εs

/-- Every block's counts are at most εs as shares of their rounds' challenge values. -/
def BlocksBelow : {s : Sg} → Chain s → ℝ≥0∞ → Prop
  | _, .last _ _ _ _ _ _ εb => fun εs => Err.Below εb εs
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ εf εc next => fun εs =>
    Err.Below εf εs ∧ Err.Below εc εs ∧ next.BlocksBelow εs

/-- Every count of the chain is at most εs as a share of its round's challenge values, if every
block's counts are. -/
theorem below_of_blocks {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (h : c.BlocksBelow εs) :
    Err.Below c.err εs := by
  induction c with
  | last s e dL dB fu fs εb => exact h
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    exact Err.Below.app h.1 (Err.Below.app h.2.1 (ih h.2.2))

/-- With the library's counts, the inequalities that are written out bound every block's
counts. -/
theorem blocks_of_small {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (hp : c.Plain) (h : c.Small εs) :
    c.BlocksBelow εs := by
  induction c with
  | last s e dL dB fu fs εb =>
    have hb : εb = baseErr s e (e + 1) 1 dL dB := hp
    subst hb
    exact base_below s e dL dB εs h.1 h.2
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    obtain ⟨hf', hc', hn⟩ := hp
    obtain ⟨hE, hT, hM, hC, hN⟩ := h
    subst hf' hc'
    exact ⟨fold_below s dE dT e εs hE hT hM, cs_below hf e dS dC εs hC, ih hn hN⟩

/-- Every count of a chain that has the library's counts is at most εs as a share of its round's
challenge values, if each count that is written out in `Small` is. Nothing is asked of the rounds in
which a tree is sent: their counts are 0. -/
theorem err_below {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (hp : c.Plain) (h : c.Small εs) :
    Err.Below c.err εs :=
  c.below_of_blocks εs (c.blocks_of_small εs hp h)

/-- The counts carried to the shape of the list of rounds meet the bounds that the counts meet. -/
theorem errL_below {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (h : Err.Below c.err εs) :
    Err.Below c.errL εs :=
  below_cast c.uL_rds c.err εs h

/-- The batching's count, which is the number of rows less one, and the chain's counts, over the
list of the batching's round and the chain's rounds: each is at most εs as a share of its round's
challenge values, if the batching's is and `Small` holds. -/
theorem errL_below_bat {s : Sg} (c : Chain s) (εs : ℝ≥0∞) (hp : c.Plain) (h : c.Small εs) (S : Sz)
    (dA : PQ.RD) (hA : RoundBelow (1 * (S.nRows - 1)) dA εs) :
    Err.Below (s := PQ.uL (ckP .two) (dA :: c.rds)) (batErr S 1 dA, c.errL) εs :=
  ⟨hA, c.errL_below εs (c.err_below εs hp h)⟩

end Chain

end OnBytes.Slice
