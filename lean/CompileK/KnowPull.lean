-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowPull.lean: knowledge soundness is kept when verifier messages are made from blocks,
with the samplers' bias in the bound.

This file is about the interactive oracle proofs that the compiler takes: round-by-round knowledge
soundness is kept, with the samplers' bias in the bound, under the hypotheses of the statements,
when each verifier message is drawn as a function of uniform hash-length blocks.
Statements and proofs.
The compiler takes an interface whose verifier messages are tuples of hash-length blocks; an
interface with challenges in fields, positions and so on is brought to that form by a sampler for
each round (Iop/Pull.lean, Iop/BatchPull.lean, Iop/Draw.lean, Iop/BatchWireDraw.lean). That the
properties of `Iop.BatchProtocol.Props` are kept, with the bias in the numbers, is `Iop.pullPropsB` and
`Iop.drawsPropsB`. Here the same is stated and proved for the soundness with a witness of
Hiop/Interface.lean.

Main names, each under the hypotheses of its statement:
  `Spec.sndBK_pull`: (Snd-B) with a witness is kept: same relation, extractor wit ∘ Orcs.push, every
    count times the bound on the fibres of its round's sampler.
  `Spec.soundK_pull`: `BatchProtocol.SoundK` is kept along any good samplers: εs becomes κ εs.
  `Spec.soundK_draws`: `BatchProtocol.SoundK` is kept along block samplers with bias κ₀ ≥ 1 a block: εs
    becomes κ₀^K εs, K the largest number of blocks of a round.
  `Spec.propsK_draws`: `BatchProtocol.PropsK` is kept, with the numbers M.pullB (κ₀^K) (κ₀^n) maxBatchSize, which are
    those of `Top.Batch.numsDraw`, n a bound on the blocks of all rounds of a protocol
    (`dr.TotLe n`).

Why: `SndBK` (Ior/Batch.lean) is the late form of (Snd-B) (`BatchInteractiveOracleProof.SndBL`, Iop/Batch.lean) of
the guarded protocol (`BatchInteractiveOracleProof.guard`, Ior/Batch.lean) for the empty language, so
`Iop.BatchPull.sndBL_pull` applies to the guarded protocol; `guard_pull` says what its pull is.
The extractor after the pull is the old one on the same symbols: `Orcs.push` only re-types the
family of symbols (positions and alphabets of a pulled round are those of the round). It sees no
source string and no verifier message.

Limits: this file says nothing on whether any interface has `SoundK`. It says nothing on a converse
(from the pulled interface back). At κ₀^K εs ≥ 1 the bound on the errors says nothing, as
everywhere; the state function and the extractor are still there.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowExt
import Hiop.Interface
import Iop.BatchWireDrawOK

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace Spec

/-- States: the oracles of a transcript with the images of its verifier messages are the oracles of
the transcript. -/
def read_push : Prop :=
  ∀ (s : Shape) (σ : Samplers s) (τ : Tr (s.pull σ)), (Tr.push σ τ).read = Orcs.push σ τ.read

/-- States: guard and pull commute, with the extractor wit ∘ Orcs.push on the pulled side. -/
def guard_pull : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (R : X → E.Str → W → Prop)
      (wit : X → Orcs Q.loc.shape → W) (σ : Samplers Q.loc.shape),
    (Q.guard R wit).pull σ = (Q.pull σ).guard R (fun x o => wit x (Orcs.push σ o))

/-- States: (Snd-B) with a witness is kept by the pull, for samplers with `σ.Fib`, at the errors
`Err.pull σ ε`. -/
def sndBK_pull : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (σ : Samplers Q.loc.shape), σ.Fib →
    ∀ (N : ℕ) (early : X → X) (late : Option ℕ) (R : X → E.Str → W → Prop)
        (wit : X → Orcs Q.loc.shape → W) (ε : Err Q.loc.shape),
      Q.SndBK N early late R wit ε →
      (Q.pull σ).SndBK N early late R (fun x o => wit x (Orcs.push σ o)) (Err.pull σ ε)

/-- States: index-binding round-by-round knowledge soundness is kept along good samplers, at κ εs.
-/
def soundK_pull : Prop :=
  ∀ (I X W : Type) (L : BatchProtocol I X) (Rno : I → X → W → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → W)
      (εs : ℝ≥0∞) (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape)
      (σB : Samplers L.onlineBatch.loc.shape) (κ K : ℝ≥0∞),
    σT.Good κ K → σL.Good κ K → σB.Good κ K → L.SoundK Rno wit εs →
    (L.pull σT σL σB).SoundK Rno (fun x o => wit x (Orcs.push σB o)) (κ * εs)

/-- States, under the hypotheses below: index-binding round-by-round knowledge soundness is kept
when verifier messages are made from blocks, at κ₀^K εs. -/
def soundK_draws : Prop :=
  ∀ (I X W : Type) (L : BatchProtocol I X) (Rno : I → X → W → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → W)
      (εs : ℝ≥0∞) (lam n : ℕ) (dr : L.Draws lam) (κ₀ : ℝ≥0∞),
    1 ≤ κ₀ → dr.Good κ₀ → dr.TotLe n → L.SoundK Rno wit εs →
    (L.draws dr).SoundK Rno
      (fun x o => wit x (Orcs.push (Samplers.ofDraws _ dr.B) o)) (κ₀ ^ dr.K * εs)

/-- The same without a bound on the blocks of all rounds, which the conclusion does not name. -/
def soundK_draws_any : Prop :=
  ∀ (I X W : Type) (L : BatchProtocol I X) (Rno : I → X → W → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → W)
      (εs : ℝ≥0∞) (lam : ℕ) (dr : L.Draws lam) (κ₀ : ℝ≥0∞),
    1 ≤ κ₀ → dr.Good κ₀ → L.SoundK Rno wit εs →
    (L.draws dr).SoundK Rno
      (fun x o => wit x (Orcs.push (Samplers.ofDraws _ dr.B) o)) (κ₀ ^ dr.K * εs)

/-- States, under the hypotheses below: all properties with a witness are kept when verifier
messages are made from blocks, with the numbers below. -/
def propsK_draws : Prop :=
  ∀ (I X W : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → W → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → W)
      (M : LH.Nums) (lam n : ℕ) (dr : L.Draws lam) (κ₀ : ℝ≥0∞),
    1 ≤ κ₀ → dr.Good κ₀ → dr.TotLe n → L.PropsK Ryes Rno wit M →
    (L.draws dr).PropsK Ryes Rno (fun x o => wit x (Orcs.push (Samplers.ofDraws _ dr.B) o))
      (M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize)

end Spec

theorem read_push : Spec.read_push
  | [], _, _ => funext fun p => nomatch p
  | _ :: s, (_, σs), (_, _, τ) => funext fun p => match p with
    | .inl _ => rfl
    | .inr p => congrFun (read_push s σs τ) p

open Classical in
/-- The verifiers of `(Q.guard R wit).pull σ` and of
`(Q.pull σ).guard R (fun x o => wit x (Orcs.push σ o))` decide alike. -/
theorem KnowPull.accept_eq {X W : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof X E)
    (R : X → E.Str → W → Prop) (wit : X → Orcs Q.loc.shape → W) (σ : Samplers Q.loc.shape) :
    (fun (x : X) (y : E.Str) (τ : Tr (Q.loc.shape.pull σ)) =>
        Q.loc.accept x y (Tr.push σ τ) && !decide (R x y (wit x (Tr.push σ τ).read))) =
      fun x y τ =>
        Q.loc.accept x y (Tr.push σ τ) && !decide (R x y (wit x (Orcs.push σ τ.read))) := by
  funext x y τ
  rw [read_push]

theorem guard_pull : Spec.guard_pull := fun X _ E Q R wit σ =>
  congrArg (fun acc : X → E.Str → Tr (Q.loc.shape.pull σ) → Bool =>
      (⟨{ Q.loc.pull σ with accept := acc }, Q.ann.pull σ⟩ : BatchInteractiveOracleProof X E))
    (KnowPull.accept_eq Q R wit σ)

theorem sndBK_pull : Spec.sndBK_pull := by
  intro X W E Q σ hσ N early late R wit ε h
  have h' : ((Q.guard R wit).pull σ).SndBL N early late (fun _ _ => False) (Err.pull σ ε) :=
    BatchPull.sndBL_pull (Q := Q.guard R wit) hσ h
  exact cast
    (congrArg (fun acc : X → E.Str → Tr (Q.loc.shape.pull σ) → Bool =>
        (⟨{ Q.loc.pull σ with accept := acc }, Q.ann.pull σ⟩ : BatchInteractiveOracleProof X E).SndBL
          N early late (fun _ _ => False) (Err.pull σ ε))
      (KnowPull.accept_eq Q R wit σ)) h'

theorem soundK_pull : Spec.soundK_pull := by
  intro I X W L Rno wit εs σT σL σB κ K hT hL hB h
  exact
    ⟨let ⟨ε, hb, hs⟩ := h.sndT; ⟨Err.pull σT ε, hb.pull hT, hs.pull hT.fib⟩,
     let ⟨ε, hb, hs⟩ := h.sndL; ⟨Err.pull σL ε, hb.pull hL, hs.pull hL.fib⟩,
     let ⟨ε, hb, hs⟩ := h.sndB; ⟨Err.pull σB ε, hb.pull hB, sndBK_pull _ _ _ L.onlineBatch σB hB.fib _ _ _ _ _ _ hs⟩⟩

theorem soundK_draws : Spec.soundK_draws := by
  intro I X W L Rno wit εs lam n dr κ₀ h1 hg hn h
  exact soundK_pull I X W L Rno wit εs _ _ _ _ _
    (drawsGood lam κ₀ h1 _ dr.T hg.1 dr.K n (le_max_left _ _) hn.1)
    (drawsGood lam κ₀ h1 _ dr.Lk hg.2.1 dr.K n
      (le_trans (le_max_left _ _) (le_max_right _ _)) hn.2.1)
    (drawsGood lam κ₀ h1 _ dr.B hg.2.2 dr.K n
      (le_trans (le_max_right _ _) (le_max_right _ _)) hn.2.2) h

theorem soundK_draws_any : Spec.soundK_draws_any := by
  intro I X W L Rno wit εs lam dr κ₀ h1 hg h
  exact soundK_draws I X W L Rno wit εs lam
    (max (Shape.Draws.totB _ dr.T) (max (Shape.Draws.totB _ dr.Lk) (Shape.Draws.totB _ dr.B)))
    dr κ₀ h1 hg
    ⟨le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩ h

theorem propsK_draws : Spec.propsK_draws := by
  intro I X W L Ryes Rno wit M lam n dr κ₀ h1 hg hn h
  exact ⟨drawsPropsB I X L _ _ M lam n dr κ₀ h1 hg hn h.props,
    soundK_draws I X W L Rno wit M.εs lam n dr κ₀ h1 hg hn h.soundK⟩

end Iop
