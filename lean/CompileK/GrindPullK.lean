-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/GrindPullK.lean: knowledge soundness for explicit lists of errors, carried through the
step that makes verifier messages from blocks, as far as the step that adds tests (proof of work,
"grinding").

Statements and proofs.
A list of errors (`Err`, Iop/Rbr.lean) has one number e_i for each round: how many values of the
verifier message may let a prover that has lost escape; as a probability the round's error is
ε_i = e_i / |C_i|, C_i the set of all values of that message.

The knowledge form of Iop/GrindPull.lean. The tests stand last among the steps on interfaces: first
every verifier message is made from hash-length blocks by a sampler (`BatchProtocol.draws`), then tests are
added (`BatchProtocol.grind`); the interface that the compiler with tests takes is
`BatchProtocol.drawsGrind W L dr gT gL gB`, with the lists of test bits given on the shapes of L.
The witness map of that interface is wit on the same symbols, re-typed twice (`Orcs.strip`, then
`Orcs.push`). By its type it sees the instance and the prover's oracles only.

Main names, each under the hypotheses of its statement:
  `Spec.soundAtK_pull`, `Spec.soundAtK_draws`: `BatchProtocol.SoundAtK` (Hiop/GrindK.lean) is kept: each
    count is multiplied by the bound on the fibres of its round's sampler (`Err.pull`).
  `Spec.grindDrawsSoundK`: knowledge soundness of the interface on blocks with tests at one number:
    from e_i ≤ c (2^b_i |C_i|) in every round of L, that is ε_i 2^-b_i ≤ c: at κ₀^K c, κ₀ the bias
    of a block, K the largest number of blocks of a round.
  `Spec.grindDrawsPropsK`: all clauses but acceptance, with a witness (`BatchProtocol.PropsNoAccK`): the
    numbers that `BatchProtocol.draws` gives, which are those of CompileK/Main.lean (`Top.Batch.numsDraw`),
    and κ₀^K c in the place of εs.
  `Spec.soundKG_draws`: with the blocks put in, `BatchProtocol.SoundKG` (a bound c on each round's error,
    that round's bits of work reckoned in) still holds, now at κ₀^K c.
  `Spec.propsNoAccK_drawsGrind`: `grindDrawsPropsK` from `PropsK` and `SoundKG` of L.
  `Spec.grindDrawsPropsK_same`: without explicit lists: the numbers of CompileK/Main.lean
    unchanged, for all lists of test bits.

Limits: the largest error of the bare protocol does not occur in κ₀^K c. A round with b_i = 0 must
be at most c by itself. The factor κ₀^K is the one that CompileK/Main.lean pays on εs
(`DataK.nums`). This file says nothing on the size of any error: c is free, and at κ₀^K c ≥ 1 the
bound says nothing. It says nothing on the honest side beyond `PropsNoAcc`; nothing on a wire, on
tries or on a compiled scheme. `PropsK` in the hypothesis brings L's own soundness at M.εs, which
the conclusion of `grindDrawsPropsK` does not read.

Terms: lean/GLOSSARY.md.
-/
import Hiop.GrindK
import CompileK.KnowPull
import Iop.GrindPull

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace Spec

/-- Under the hypotheses below, knowledge soundness for explicit lists is kept along samplers with
bounded fibres, with each count multiplied by the bound on the fibres of its round's sampler
(`Err.pull`). -/
def soundAtK_pull : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape)
      (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape),
    σT.Fib → σL.Fib → σB.Fib → L.SoundAtK Rno wit εT εL εB →
    (L.pull σT σL σB).SoundAtK
      Rno (fun x o => wit x (Orcs.push σB o)) (Err.pull σT εT) (Err.pull σL εL) (Err.pull σB εB)

/-- Under the hypotheses below, knowledge soundness for explicit lists is kept when verifier
messages are made from blocks, with each count multiplied by the bound on the fibres of its round's
sampler (`Err.pull`). -/
def soundAtK_draws : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (lam : ℕ)
      (dr : L.Draws lam) (κ₀ : ℝ≥0∞),
    dr.Good κ₀ → L.SoundAtK Rno wit εT εL εB →
    (L.draws dr).SoundAtK Rno (fun x o => wit x (Orcs.push (Samplers.ofDraws _ dr.B) o))
      (Err.pull (Samplers.ofDraws _ dr.T) εT) (Err.pull (Samplers.ofDraws _ dr.Lk) εL)
      (Err.pull (Samplers.ofDraws _ dr.B) εB)

/-- Under the hypotheses below, the interface on blocks with tests has knowledge soundness at one
number. -/
def grindDrawsSoundK : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (εT : Err L.offline.shape) (εL : Err L.link.shape)
      (εB : Err L.onlineBatch.loc.shape) (lam : ℕ) (dr : L.Draws lam) (κ₀ : ℝ≥0∞) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    1 ≤ κ₀ → dr.Good κ₀ → L.SoundAtK Rno wit εT εL εB → Err.BelowG gT εT c →
    Err.BelowG gL εL c → Err.BelowG gB εB c →
    (L.drawsGrind W dr gT gL gB).SoundK Rno
      (fun x o =>
        wit x
          (Orcs.push (Samplers.ofDraws _ dr.B) (Orcs.strip (gB.pull (Samplers.ofDraws _ dr.B)) o)))
      (κ₀ ^ dr.K * c)

/-- Under the hypotheses below, all clauses but acceptance hold, with a witness, on blocks with
tests. -/
def grindDrawsPropsK : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (M : LH.Nums) (εT : Err L.offline.shape)
      (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (lam n : ℕ) (dr : L.Draws lam) (κ₀ : ℝ≥0∞)
      (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    1 ≤ κ₀ → dr.Good κ₀ → dr.TotLe n → L.PropsK Ryes Rno wit M → L.SoundAtK Rno wit εT εL εB →
    Err.BelowG gT εT c → Err.BelowG gL εL c → Err.BelowG gB εB c →
    (L.drawsGrind W dr gT gL gB).PropsNoAccK Ryes Rno
      (fun x o =>
        wit x
          (Orcs.push (Samplers.ofDraws _ dr.B) (Orcs.strip (gB.pull (Samplers.ofDraws _ dr.B)) o)))
      { M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize with εs := κ₀ ^ dr.K * c }

/-- If the hypotheses below hold and verifier messages are built out of blocks, `BatchProtocol.SoundKG` (a
round's error within c once its bits of work count) survives, with c raised to κ₀^K c. -/
def soundKG_draws : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (lam : ℕ) (dr : L.Draws lam) (κ₀ : ℝ≥0∞) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
      (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    1 ≤ κ₀ → dr.Good κ₀ → L.SoundKG Rno wit gT gL gB c →
    (L.draws dr).SoundKG Rno (fun x o => wit x (Orcs.push (Samplers.ofDraws _ dr.B) o))
      (gT.pull (Samplers.ofDraws _ dr.T)) (gL.pull (Samplers.ofDraws _ dr.Lk))
      (gB.pull (Samplers.ofDraws _ dr.B)) (κ₀ ^ dr.K * c)

/-- Under the hypotheses below, all clauses but acceptance hold, with a witness, on blocks with
tests, from all properties of L with a witness and "every round of L has error at most c, counting
its bits of work".
-/
def propsNoAccK_drawsGrind : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (M : LH.Nums) (lam n : ℕ) (dr : L.Draws lam) (κ₀ : ℝ≥0∞)
      (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    1 ≤ κ₀ → dr.Good κ₀ → dr.TotLe n → L.PropsK Ryes Rno wit M → L.SoundKG Rno wit gT gL gB c →
    (L.drawsGrind W dr gT gL gB).PropsNoAccK Ryes Rno
      (fun x o =>
        wit x
          (Orcs.push (Samplers.ofDraws _ dr.B) (Orcs.strip (gB.pull (Samplers.ofDraws _ dr.B)) o)))
      { M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize with εs := κ₀ ^ dr.K * c }

/-- Without explicit lists: the numbers after the blocks, unchanged, for all lists of test bits. -/
def grindDrawsPropsK_same : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (M : LH.Nums) (lam n : ℕ) (dr : L.Draws lam) (κ₀ : ℝ≥0∞)
      (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape),
    1 ≤ κ₀ → dr.Good κ₀ → dr.TotLe n → L.PropsK Ryes Rno wit M →
    (L.drawsGrind W dr gT gL gB).PropsNoAccK Ryes Rno
      (fun x o =>
        wit x
          (Orcs.push (Samplers.ofDraws _ dr.B) (Orcs.strip (gB.pull (Samplers.ofDraws _ dr.B)) o)))
      (M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize)

end Spec

theorem soundAtK_pull : Spec.soundAtK_pull := fun _ X Wn L _ wit _ _ εB _ _ σB hT hL hB h =>
  ⟨h.sndT.pull hT, h.sndL.pull hL, sndBK_pull X Wn _ L.onlineBatch σB hB L.maxBatchSize L.early L.late _ wit εB h.sndB⟩

theorem soundAtK_draws : Spec.soundAtK_draws := fun I X Wn L Rno wit εT εL εB _ _ _ hg h =>
  soundAtK_pull I X Wn L Rno wit εT εL εB _ _ _ hg.1.fibS hg.2.1.fibS hg.2.2.fibS h

theorem grindDrawsSoundK : Spec.grindDrawsSoundK := by
  intro W _ I X Wn L Rno wit εT εL εB lam dr κ₀ gT gL gB c h1 hg h eT eL eB
  exact grindSoundK W I X Wn (L.draws dr) Rno _ _ _ _ _ _ _ _
    (soundAtK_draws I X Wn L Rno wit εT εL εB lam dr κ₀ hg h)
    (eT.pull (drawsGood lam κ₀ h1 _ dr.T hg.1 dr.K _ (le_max_left _ _) le_rfl))
    (eL.pull (drawsGood lam κ₀ h1 _ dr.Lk hg.2.1 dr.K _
        (le_trans (le_max_left _ _) (le_max_right _ _)) le_rfl))
    (eB.pull (drawsGood lam κ₀ h1 _ dr.B hg.2.2 dr.K _
        (le_trans (le_max_right _ _) (le_max_right _ _)) le_rfl))

theorem grindDrawsPropsK : Spec.grindDrawsPropsK := by
  intro W _ I X Wn L Ryes Rno wit M εT εL εB lam n dr κ₀ gT gL gB c h1 hg hn h hA eT eL eB
  have hK := grindDrawsSoundK W I X Wn L Rno wit εT εL εB lam dr κ₀ gT gL gB c h1 hg hA eT eL eB
  exact ⟨grindDrawsProps W h1 hg hn h.props (sound_of_soundK I X Wn _ Rno _ _ hK), hK⟩

theorem soundKG_draws : Spec.soundKG_draws := by
  rintro I X Wn L Rno wit lam dr κ₀ gT gL gB c h1 hg ⟨εT, εL, εB, hA, eT, eL, eB⟩
  exact ⟨_, _, _,
    soundAtK_draws I X Wn L Rno wit εT εL εB lam dr κ₀ hg hA,
    eT.pull (drawsGood lam κ₀ h1 _ dr.T hg.1 dr.K _ (le_max_left _ _) le_rfl),
    eL.pull (drawsGood lam κ₀ h1 _ dr.Lk hg.2.1 dr.K _
        (le_trans (le_max_left _ _) (le_max_right _ _)) le_rfl),
    eB.pull (drawsGood lam κ₀ h1 _ dr.B hg.2.2 dr.K _
        (le_trans (le_max_right _ _) (le_max_right _ _)) le_rfl)⟩

theorem propsNoAccK_drawsGrind : Spec.propsNoAccK_drawsGrind := by
  rintro W _ I X Wn L Ryes Rno wit M lam n dr κ₀ gT gL gB c h1 hg hn h ⟨εT, εL, εB, hA, eT, eL, eB⟩
  exact grindDrawsPropsK W I X Wn L Ryes Rno wit M εT εL εB lam n dr κ₀ gT gL gB
    c h1 hg hn h hA eT eL eB

theorem grindDrawsPropsK_same : Spec.grindDrawsPropsK_same := by
  intro W _ I X Wn L Ryes Rno wit M lam n dr κ₀ gT gL gB h1 hg hn h
  exact grindPropsK_same W I X Wn (L.draws dr) Ryes Rno _ _ _ _ _
    (propsK_draws I X Wn L Ryes Rno wit M lam n dr κ₀ h1 hg hn h)

end Iop
