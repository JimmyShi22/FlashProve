-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyHoldsJoh.lean: the blocks' statements of ANY chain of stages (`Chain.Holds`) from
conditions stage by stage: at four letters, with no hypothesis but these conditions, the facts on
codes among them; and below the Johnson radius UNDER THE THEOREM ON CODES, TAKEN AS GIVEN
(`Cb.BCHKS46At`: a hypothesis, which this file does not prove).

OnBytes/Slice/ManyAtLetters.lean and OnBytes/Slice/ManyJohnson.lean show `Chain.Holds` of chains
that are built by their three makers, which fix the readings. `Chain.Holds` does not look at a
chain's readings: it speaks of stages, radii, rounds, error counts and each fold's number n0, which
is any number here. So this file takes any chain whose error counts are those of the four letters
(`Chain.PlainAt`) and asks, stage by stage, what the blocks ask (`Chain.OkAt`). Below the Johnson
radius these follow from conditions on sizes, radius and the rounds' forms alone (`Chain.JohAt`) and
the hypothesis on codes, at the letters: the Johnson bound's list (`Sg.lstJ`); for the main rows the
integer part of `bchksBound` at the main code (`Sg.flC`); for both tables of mask rows the integer
part of `bchksBound` at the Reed-Solomon code in which the repeated mask code lies, and the Johnson
bound's list at that code's distance (`Sg.flZ`).

Main definitions: `Chain.OkAt`, `Sg.StageJ`, `Chain.JohAt`, `Sg.flC`, `Sg.flZ`.
Main theorems: `Chain.holds_of_okAt` (no further hypothesis), `Chain.JohAt.first`, `Chain.okAt_joh`,
`Chain.holds_joh` (under the hypothesis).

Not claimed. THIS IS NO PROOF OF SOUNDNESS AT THE JOHNSON RADIUS. That any chain meets `Chain.JohAt`
is not shown here (OnBytes/Slice/SmallRecChain.lean and OnBytes/Slice/FullRecChain.lean show it of
two chains); `Chain.PlainAt` holds of the chains of OnBytes/Slice/ManyAtLetters.lean's makers by
definition. `bchksBound` is evaluated nowhere here: no number is stated, and nothing says that the
counts are small. `Sg.StageJ` asks of each stage a main and a mask code with at least two
coefficients each. A code switch is written at one answer to a sample (`CsRounds`). Nothing on the
batching, a stored table, its link, a record, a program or a file.

-/
import OnBytes.Slice.ManyAtLetters
import OnBytes.Slice.CountsFloor

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run
open Cb.CodeListRS

namespace Sg

/-- The count for the main rows: the integer part of `bchksBound` at the main code. -/
noncomputable def flC (s : Sg) (e : ℕ) : ℕ := ⌊bchksBound (2 ^ s.C.a) (s.C.r + s.C.l - 1) e⌋₊

/-- The count for a table of mask rows: the integer part of `bchksBound` at the Reed-Solomon code of
the main rows' length in which the repeated mask code lies, and the Johnson bound's list at that
code's distance. -/
noncomputable def flZ (s : Sg) (e : ℕ) : ℕ :=
  ⌊bchksBound (2 ^ s.C.a) (2 ^ (s.C.a - s.Z.a) * (s.Z.r + s.Z.l - 1)) e⌋₊ +
    listMax (2 ^ s.C.a) s.dZ e

/-- What is asked of a stage and its radius: sizes in order; a main and a mask code with at least
two coefficients each (so `Sg.Pos`, which is asked besides, follows); the radius is not 0 and is
below the stage's Johnson radius. -/
structure StageJ (s : Sg) (e : ℕ) : Prop where
  sized : s.Sized
  pos : s.Pos
  twoC : 0 < s.C.r + s.C.l - 1
  twoZ : 0 < s.Z.r + s.Z.l - 1
  rad : 0 < e
  joh : s.InJ e

/-- Under the hypothesis on codes: the named hypothesis of OnBytes/Slice/BlocksJohnson.lean, at
these counts. -/
theorem StageJ.counts (hA : BCHKS46At GF GE) {s : Sg} {e : ℕ} (h : s.StageJ e) :
    s.CountsAt e (s.flC e) (s.flZ e) :=
  countsAt_floor hA h.sized h.pos h.twoC h.twoZ h.rad h.joh

end Sg

namespace Chain
variable (L mC mS mW : Sg → ℕ → ℕ)

/-- **What the blocks ask, stage by stage, at the four letters.** At the last stage: `BaseCodes`,
and the two rounds send and draw what a base case's do. At a stage that is folded and switched:
sizes in order, e < d, `SumPar.ErrOK`, the rounds are a fold's and a code switch's, and the next
stage's tables have lists of at most L at the next radius. -/
def OkAt : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ _ =>
    BaseCodes s e (mC s e + mS s e) (L s e) ∧ (∃ nL aL, SendsDraws dL nL 1 0 aL) ∧
      ∃ nB, SendsDraws dB nB 0 s.t s.C.a
  | _, .step s s' _ _ e dE dT dS dC _ _ _ _ _ next =>
    s.Sized ∧ e < s.d ∧
      (s.par 0).ErrOK e (fun _ => L s e) (fun _ => mC s e) (fun _ => mS s e) (fun _ => mW s e) ∧
      FoldRounds dE dT ∧ CsRounds s s' dS dC ∧ s'.cIn.ListAt next.rad (L s' next.rad) ∧ next.OkAt

variable {L mC mS mW}

/-- **Any chain with the letters' numbers whose stages are as the blocks ask has its blocks taken
off.** Nothing is asked of the chain's readings. -/
theorem holds_of_okAt {s : Sg} (c : Chain s) (hp : c.PlainAt L mC mS mW)
    (h : c.OkAt L mC mS mW) : c.Holds := by
  induction c with
  | last s e dL dB fu fs εb =>
    have hb : εb = baseErr s e (mC s e + mS s e) (L s e) dL dB := hp
    subst hb
    obtain ⟨hc, ⟨nL, aL, hL⟩, nB, hB⟩ := h
    exact baseSem_of s e _ _ dL dB hc hL hB
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    obtain ⟨hf', hc', hn⟩ := hp
    obtain ⟨hs, he, hE, hF, hC, hl, hN⟩ := h
    subst hf' hc'
    exact ⟨foldSem_of s n0 s.d e _ _ _ _ (Sg.codesOK hs he) hE dE dT hF,
      csSem_of hf e next.rad (L s' next.rad) (Sg.fit_cMid hs).laws hl dS dC hC, ih hn hN⟩

/-- **Conditions on sizes, radii and the rounds' forms alone**, stage by stage. -/
def JohAt : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ _ =>
    s.StageJ e ∧ (∃ nL aL, SendsDraws dL nL 1 0 aL) ∧ ∃ nB, SendsDraws dB nB 0 s.t s.C.a
  | _, .step s s' _ _ e dE dT dS dC _ _ _ _ _ next =>
    s.StageJ e ∧ FoldRounds dE dT ∧ CsRounds s s' dS dC ∧ next.JohAt

/-- The chain's first stage, at the chain's first radius. -/
theorem JohAt.first {s : Sg} {c : Chain s} (h : c.JohAt) : s.StageJ c.rad := by
  cases c with
  | last s e dL dB fu fs εb => exact h.1
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next => exact h.1

/-- **Under the hypothesis on codes** the stages are as the blocks ask, at the Johnson bound's lists
and the counts `Sg.flC`, `Sg.flZ`. -/
theorem okAt_joh (hA : BCHKS46At GF GE) {s : Sg} (c : Chain s) (h : c.JohAt) :
    c.OkAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ := by
  induction c with
  | last s e dL dB fu fs εb =>
    exact ⟨baseCodes_joh h.1.sized h.1.joh (h.1.counts hA), h.2.1, h.2.2⟩
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    obtain ⟨hS, hF, hC, hN⟩ := h
    exact ⟨hS.sized, hS.joh.1, foldNums_joh hS.sized hS.joh (hS.counts hA), hF, hC,
      Sg.listJ_of (Sg.fit_cIn hN.first.sized) hN.first.joh, ih hN⟩

/-- **UNDER THE HYPOTHESIS ON CODES: any chain with these numbers whose stages meet the conditions
on sizes, radii and rounds has its blocks taken off**, at radii below the Johnson radius. -/
theorem holds_joh (hA : BCHKS46At GF GE) {s : Sg} (c : Chain s)
    (hp : c.PlainAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ) (h : c.JohAt) : c.Holds :=
  c.holds_of_okAt hp (c.okAt_joh hA h)

end Chain

end OnBytes.Slice
