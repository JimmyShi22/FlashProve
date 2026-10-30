-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyProx.lean: a proximity test as a step.

OnBytes/Slice/KeyStep.lean has a calculus of steps. OnBytes/Slice/ManySem.lean takes the rounds of a
chain of any number of stages off (`chain_many`). This file makes a chain's rounds a step, puts the
batching's round in front, and proves the step's statement from the blocks' statements. Such a step
ends a claim: if the group's relation before the batching has no witness, the prover has lost in
these rounds. With `Step.Sem.test` it can stand in the middle of a protocol, other claims riding
along.

The first fold's mask. A chain's yes in the field reads the first tree as three words; the second is
the word of fresh mask rows, which the first fold uses. In some tests that word was sent before the
test. In others it comes in the first message of the fold itself. Here it is read off the state and
the chain's first prover message, which covers both. `chain_many` takes the word as fixed before the
chain; it is used once for each first message (`doomed_each_first`).

Main definitions.
 `Chain.Msg0`, `Chain.msg0`   the type of a chain's first prover message; that message.
 `chainStep`    a chain's rounds as a step. Its test is the chain's yes in the field.
 `Prox`         what a proximity test is made of, seen from states X: the first stage, the chain,
                the batching's round and error count, the claim that the batching makes, and the
                first tree's three words.
 `Prox.bat`, `Prox.step`   the batching's round as a step; the whole test as a step.
 `Prox.Holds`   the batching's statement, from a claim W on states, and the blocks' statements.
Main theorems.
 `doomed_each_first`   a goal may be proved for each first prover message apart.
 `chain_many_own`  `chain_many` with the word of fresh mask rows read off the first message.
 `Chain.exists_blL`   a transcript of a chain's list of rounds is made of blocks' transcripts.
 `chainStep_sem`   if the blocks are taken off, the chain's step takes "the first claim has a
                   witness" to `True`.
 `Prox.sem`        the whole test takes W to `True`.
Not claimed. That `Prox.Holds` holds of any test. Nothing on the sizes of the error counts. The
casts in this file are between a chain's joined shapes and the shape of its list of rounds; they are
those of OnBytes/Slice/ManyCloses.lean, and the step's error counts are that file's `Chain.errL`.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyStep

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run

variable {X X' : Type}

/-- A goal may be proved for each first prover message apart: towards "if the first message is m₀,
the goal". -/
theorem doomed_each_first (r : Round) (s : Shape) (e : ℕ) (ε : Err s) (bad : Tr (r :: s) → Prop)
    (h : ∀ m₀ : r.Msg, Doomed (r :: s) (e, ε) fun τ => τ.1 = m₀ → bad τ) :
    Doomed (r :: s) (e, ε) bad := fun m =>
  le_trans (cnt_mono fun c hc hd => hc (Doomed.mono s ε
    (bad := fun τ => m = m → bad (m, c, τ)) (bad' := fun τ => bad (m, c, τ))
    (fun _ hτ => hτ rfl) hd)) (h m m)

namespace Chain

/-- The type of the chain's first prover message. -/
def Msg0 : {s : Sg} → Chain s → Type
  | _, .last _ _ dL _ _ _ _ => (wRound dL).Msg
  | _, .step _ _ _ _ _ dE _ _ _ _ _ _ _ _ _ => (wRound dE).Msg

/-- The chain's first prover message. -/
def msg0 : {s : Sg} → (c : Chain s) → c.Bl → c.Msg0
  | _, .last _ _ _ _ _ _ _ => fun τ => τ.1
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fun b => b.1.1

/-- A transcript of a chain's list of rounds is made of blocks' transcripts. -/
theorem exists_blL {s : Sg} (c : Chain s) (τ : Tr (uW c.rds)) : ∃ b, τ = c.trL b := by
  obtain ⟨b, hb⟩ := c.exists_bl (cast (congrArg Iop.Tr c.uL_rds) τ)
  refine ⟨b, ?_⟩
  rw [← c.tr_cast, ← hb, cast_cast, cast_eq]

end Chain

/-- The chain, with the word of fresh mask rows read off the chain's first prover message. What is
asked and what is given are those of `chain_many`. -/
theorem chain_many_own {s : Sg} (c : Chain s) (h : c.Holds) (q : GE × (s.cIn.J → GE))
    (y : s.cIn.Word) (z : c.Msg0 → s.cFr.Word) (g : s.cIn.Word)
    (hno : ∀ w, ¬ s.RIn c.rad (q, y) w) (bad : Tr c.sh → Prop)
    (hp : ∀ b, c.pass b = false → bad (c.tr b))
    (H : ∀ b, ¬ c.Acc q y (z (c.msg0 b)) g b → bad (c.tr b)) : Doomed c.sh c.err bad := by
  cases c with
  | last s e dL dB fu fs εb =>
    exact chain_many (.last s e dL dB fu fs εb) h q y (z ((wRound dL).dOrc, (wRound dL).dPlain)) g
      hno bad hp H
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    obtain ⟨e0, εf'⟩ := εf
    refine doomed_each_first (wRound dE) _ e0 _ bad fun m₀ => ?_
    refine chain_many (.step s s' hf n0 e dE dT dS dC fW fZ fG (e0, εf') εc next) h q y (z m₀) g hno
      _ (fun b hb _ => hp b hb) fun b hb hm => H b ?_
    have hm' : b.1.1 = m₀ := hm
    show ¬ Chain.Acc _ q y (z b.1.1) g b
    rw [hm']
    exact hb

/-- A chain's rounds as a step. q, y, g read the first claim and two of the first tree's words off
the state; z reads the word of fresh mask rows off the state and the chain's first prover message.
The test: the chain's yes in the field, of whatever blocks' transcripts make up the transcript. The
next state does not depend on the transcript. -/
def chainStep {s : Sg} (c : Chain s) (q : X → GE × (s.cIn.J → GE)) (y : X → s.cIn.Word)
    (z : X → c.Msg0 → s.cFr.Word) (g : X → s.cIn.Word) (out : X → X') : Step X X' where
  rds := c.rds
  err := c.errL
  ok x τ := ∀ b, τ = c.trL b → c.Acc (q x) (y x) (z x (c.msg0 b)) (g x) b
  nx x _ := out x

/-- If each block of the chain is taken off, the chain's step ends the claim "the first claim has a
witness at the first stage's radius". -/
theorem chainStep_sem {s : Sg} (c : Chain s) (h : c.Holds) (q : X → GE × (s.cIn.J → GE))
    (y : X → s.cIn.Word) (z : X → c.Msg0 → s.cFr.Word) (g : X → s.cIn.Word) (out : X → X') :
    (chainStep c q y z g out).Sem (fun x => ∃ w, s.RIn c.rad (q x, y x) w) fun _ => True :=
  fun x hx => by
  refine doomed_cast c.uL_rds c.err _ ?_
  refine chain_many_own c h (q x) (y x) (z x) (g x) (fun w hw => hx ⟨w, hw⟩) _ ?_ ?_
  · intro b hb
    beta_reduce
    rw [c.tr_cast]
    intro hp
    have hp' : PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds (c.trL b)) = true := hp
    rw [c.pass_trL, hb] at hp'
    cases hp'
  · intro b hb
    beta_reduce
    rw [c.tr_cast]
    intro _ ho
    exact absurd (ho b rfl) hb

/-- What a proximity test is made of, seen from states X. -/
structure Prox (X : Type) where
  /-- the first stage -/
  s : Sg
  /-- the rounds after the batching -/
  c : Chain s
  /-- the batching's round and its error count -/
  dA : PQ.RD
  εa : ℕ
  /-- the claim that the batching makes of what the state holds, at a verifier's message -/
  q : X → (wRound dA).Chal → GE × (s.cIn.J → GE)
  /-- the first tree's words: main rows and carried mask rows; fresh mask rows, which may come in
  the chain's first prover message; the masking word -/
  y : X → s.cIn.Word
  z : X → c.Msg0 → s.cFr.Word
  g : X → s.cIn.Word

namespace Prox

/-- The batching's round: the state is kept, the verifier's message is laid beside it. -/
def bat (P : Prox X) : Step X (X × (wRound P.dA).Chal) :=
  Step.one P.dA P.εa (fun _ _ _ => True) fun x _ c => (x, c)

/-- The whole test: the batching's round, then the chain. -/
def step (P : Prox X) (out : X → X') : Step X X' :=
  P.bat.seq (chainStep P.c (fun p => P.q p.1 p.2) (fun p => P.y p.1) (fun p => P.z p.1)
    (fun p => P.g p.1) fun p => out p.1)

/-- The batching's statement and the blocks' statements. W: the claim before the batching, in the
use that is meant "the group's relation has a witness". -/
def Holds (P : Prox X) (W : X → Prop) : Prop :=
  P.bat.Sem W (fun p => ∃ w, P.s.RIn P.c.rad (P.q p.1 p.2, P.y p.1) w) ∧ P.c.Holds

/-- The whole test ends the claim W. -/
theorem sem (P : Prox X) {W : X → Prop} (h : P.Holds W) (out : X → X') :
    (P.step out).Sem W fun _ => True :=
  h.1.seq (chainStep_sem P.c h.2 _ _ _ _ _)

/-- The next state of the whole test does not depend on the transcript. -/
theorem step_nx (P : Prox X) (out : X → X') (x : X) (τ : Tr (uW (P.step out).rds)) :
    (P.step out).nx x τ = out x := rfl

end Prox

end OnBytes.Slice
