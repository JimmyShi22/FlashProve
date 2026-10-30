-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyDefs.lean: the rounds after the batching for any number of stages: definitions.

OnBytes/Slice/ChainSem.lean writes the rounds after the link's fifth out for three stages: the
batching, a fold, a code switch, a second fold, a second code switch, the base case. This file has
the same rounds, without the batching, for any number of stages. A chain from a stage s on is either
the base case at s, or a fold at s, a code switch to a stage s', and a chain from s' on. The type of
a claim and of a word hangs on the stage, so the chains are a family of types over the stages.

A chain holds, beside its stages and written rounds, a radius for each stage, how the next tree and
the base case's two messages are read in the field, the number n0 of each fold, and the error counts
of each block. All else is defined by recursion on it.

Main definitions.
 `Chain`        a chain from a stage on.
 `Chain.rad`    the radius at its first stage. `Chain.len`: its number of code switches.
 `Chain.rds`    its written rounds, as a list. `Chain.sh`: the blocks' shapes joined.
 `Chain.err`    the blocks' error counts in a row.
 `Chain.Holds`  each block is taken off (`FoldSem`, `CsSem`, `BaseSem` of ChainSem.lean).
 `Chain.Bl`     the blocks' transcripts, one after the other. `Chain.tr`, `Chain.trL`: the
                transcript of the joined shapes, and of the list of rounds, that they make.
 `Chain.rvs`    the written rounds as a view shows them, block by block.
 `Chain.pass`   all tests of work pass.
 `Chain.Acc`    the yes in the field: the claim is carried from block to block, and the base case's
                test holds of the last claim.
 `Chain.lastStd`, `Chain.stepMid`, `Chain.stepEnd`   a base case, a step to a stage that is not the
                last, and a step to the last stage, with the readings of OnBytes/Slice/SemLib.lean
                (`stdReads`) and the error counts for lists of one member.
Not claimed. No theorem is in this file.

-/
import OnBytes.Slice.SemLib

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

/-- A chain from the stage s on. e: the stage's radius. In `last`: dL, dB are the base case's two
rounds; fu, fs read what they send; εb are their error counts. In `step`: n0 is the number of
entries of a mask row on which the fold's hiding polynomial has weights; dE, dT are the fold's first
round and its repeated round; dS, dC the code switch's two rounds; fW, fZ, fG read the next stage's
tree off the message of dS: the word of main rows and carried mask rows, the word of fresh mask
rows, and the base case's masking word; εf, εc are the error counts of the fold and the switch. A
step uses fZ of the step before it, a base case uses fG. -/
inductive Chain : Sg → Type
  | last (s : Sg) (e : ℕ) (dL dB : PQ.RD) (fu : (wRound dL).Msg → GE)
      (fs : (wRound dB).Msg → s.cIn.MR) (εb : Err (PQ.uL (ckP .two) [dL, dB])) : Chain s
  | step (s s' : Sg) (hf : CsFit s s') (n0 e : ℕ) (dE dT dS dC : PQ.RD)
      (fW : (wRound dS).Msg → s'.cIn.Word) (fZ : (wRound dS).Msg → s'.cFr.Word)
      (fG : (wRound dS).Msg → s'.cIn.Word)
      (εf : Err (PQ.uL (ckP .two) (foldRds s dE dT))) (εc : Err (PQ.uL (ckP .two) [dS, dC]))
      (next : Chain s') : Chain s

namespace Chain

/-- The radius at the chain's first stage. -/
def rad : {s : Sg} → Chain s → ℕ
  | _, .last _ e _ _ _ _ _ => e
  | _, .step _ _ _ _ e _ _ _ _ _ _ _ _ _ _ => e

/-- The number of code switches. -/
def len : {s : Sg} → Chain s → ℕ
  | _, .last _ _ _ _ _ _ _ => 0
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ next => next.len + 1

/-- The written rounds, as a list. -/
def rds : {s : Sg} → Chain s → List PQ.RD
  | _, .last _ _ dL dB _ _ _ => [dL, dB]
  | _, .step s _ _ _ _ dE dT dS dC _ _ _ _ _ next => foldRds s dE dT ++ ([dS, dC] ++ next.rds)

/-- The blocks' shapes joined. -/
def sh : {s : Sg} → Chain s → Shape
  | _, .last _ _ dL dB _ _ _ => PQ.uL (ckP .two) [dL, dB]
  | _, .step s _ _ _ _ dE dT dS dC _ _ _ _ _ next =>
    PQ.uL (ckP .two) (foldRds s dE dT) ++ (PQ.uL (ckP .two) [dS, dC] ++ next.sh)

/-- The blocks' error counts in a row. -/
def err : {s : Sg} → (c : Chain s) → Err c.sh
  | _, .last _ _ _ _ _ _ εb => εb
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ εf εc next => Err.app εf (Err.app εc next.err)

/-- Each block is taken off, with the chain's radii and error counts. -/
def Holds : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ εb => BaseSem s e dL dB εb
  | _, .step s _ hf n0 e dE dT dS dC _ _ _ εf εc next =>
    FoldSem s n0 e dE dT εf ∧ CsSem hf e next.rad dS dC εc ∧ next.Holds

/-- The blocks' transcripts, one after the other. -/
def Bl : {s : Sg} → Chain s → Type
  | _, .last _ _ dL dB _ _ _ => Tr (PQ.uL (ckP .two) [dL, dB])
  | _, .step s _ _ _ _ dE dT dS dC _ _ _ _ _ next =>
    Tr (PQ.uL (ckP .two) (foldRds s dE dT)) × Tr (PQ.uL (ckP .two) [dS, dC]) × next.Bl

/-- The transcript of the joined shapes that the blocks' transcripts make. -/
def tr : {s : Sg} → (c : Chain s) → c.Bl → Tr c.sh
  | _, .last _ _ _ _ _ _ _ => fun τ => τ
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ next => fun b =>
    Tr.app b.1 (Tr.app b.2.1 (next.tr b.2.2))

/-- The transcript of the list of rounds that the blocks' transcripts make. -/
def trL : {s : Sg} → (c : Chain s) → c.Bl → Tr (PQ.uL (ckP .two) c.rds)
  | _, .last _ _ _ _ _ _ _ => fun τ => τ
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ next => fun b =>
    joinT _ _ b.1 (joinT _ _ b.2.1 (next.trL b.2.2))

/-- All tests of work pass. -/
def pass : {s : Sg} → (c : Chain s) → c.Bl → Bool
  | _, .last _ _ _ _ _ _ _ => fun τ => PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ)
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ next => fun b =>
    PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ b.1) &&
      (PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ b.2.1) && next.pass b.2.2)

/-- The yes in the field. q: the claim on the first stage's tables. y, z, g: the first stage's tree,
read as the word of main rows and carried mask rows, the word of fresh mask rows and the masking
word. A step carries the claim through its fold and its code switch and reads the next tree by the
chain's own readings, which are free fields. The base case asks its test of the claim that has come
to it. -/
def Acc : {s : Sg} → (c : Chain s) → GE × (s.cIn.J → GE) → s.cIn.Word → s.cFr.Word → s.cIn.Word →
    c.Bl → Prop
  | _, .last s _ dL dB fu fs _ => fun q y _ g τ =>
    LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) q) q.1 (s.cIn.T y)
      (s.cIn.T g) (fu τ.1) (gOne _ (valsOf dL τ.2.1)) (fs τ.2.2.1)
      (gPos s.C.a s.t _ (valsOf dB τ.2.2.2.1))
  | _, .step s _ hf n0 _ dE dT dS dC fW fZ fG _ _ next => fun q y z _ b =>
    next.Acc
      (csNextW hf dS dC (foldNext s n0 dE dT q b.1) (foldWords s y z (foldPt s dE dT b.1)) b.2.1)
      (fW b.2.1.1) (fZ b.2.1.1) (fG b.2.1.1) b.2.2

/-- The written rounds as a view shows them, block by block. -/
def rvs : {s : Sg} → (c : Chain s) → c.Bl → List Fmt.RoundView
  | _, .last _ _ dL dB _ _ _ => fun τ => PQ.rvSL (ckP .two) [dL, dB] τ
  | _, .step s _ _ _ _ dE dT dS dC _ _ _ _ _ next => fun b =>
    PQ.rvSL (ckP .two) (foldRds s dE dT) b.1 ++
      (PQ.rvSL (ckP .two) [dS, dC] b.2.1 ++ next.rvs b.2.2)

/-! ## The standard readings and counts -/

/-- A base case with the standard readings, and the error counts for lists of one member. -/
def lastStd (s : Sg) (e : ℕ) (dL dB : PQ.RD) : Chain s :=
  .last s e dL dB (fun m => lst (sentW dL m) 0) (fun m => shownW s (sentW dB m))
    (baseErr s e (e + 1) 1 dL dB)

/-- A step to a stage that is not the last, with the standard readings, and the error counts for
lists of one member; n0 is `s.Z.l`, as in the standard readings of SemLib.lean. It is meant for a
`next` that is a step: such a chain does not use the masking word, which is set to the first word
here. Nothing in this definition checks what `next` is. -/
noncomputable def stepMid (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') : Chain s :=
  .step s s' hf s.Z.l e dE dT dS dC (fun m => wordIn s' (colSt s' dS m.1))
    (fun m => wordFr s' (colSt s' dS m.1)) (fun m => wordIn s' (colSt s' dS m.1))
    (foldErr s dE dT (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1))
    (csErr hf e 1 dS dC) next

/-- A step to the last stage, with the standard readings, and the error counts for lists of one
member; n0 is `s.Z.l`, as in `stepMid`. It is meant for a `next` that is a base case, which does not
use the word of fresh mask rows. Nothing in this definition checks what `next` is. -/
noncomputable def stepEnd (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') : Chain s :=
  .step s s' hf s.Z.l e dE dT dS dC (fun m => wordIn s' (lastColW dS m.1))
    (fun m => wordFr s' (lastColW dS m.1)) (fun m => wordMk s' (lastMk dS m.1))
    (foldErr s dE dT (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1))
    (csErr hf e 1 dS dC) next

end Chain

end OnBytes.Slice
