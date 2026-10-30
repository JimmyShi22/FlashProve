-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowExtTo.lean: the natural witness extractor that follows the chain only as far as its
witness map reads.

This file is about witness extraction from a non-interactive argument in the random-oracle model: an
extractor without rewinding that looks up the Fiat-Shamir answers of the rounds before a given round
j alone.
Definitions and statements (the proofs: CompileK/KnowBindingTo.lean). Over the compiler's typed
oracles.
The extractor of CompileK/KnowExtT.lean follows the whole chain of the slot in its two traces and
says none if any query of it is missing, the last ones too. A witness map that decodes with samples
reads the seeds, which are early verifier messages; it does not read the last ones (draws of
positions). So:

Main names:
  `TrBlind j wit`: wit reads no verifier message from round j on (rounds counted from 0): two
    transcripts with the same oracle symbols and plain parts whose verifier messages agree before
    round j have the same value. For a map by parts it follows from `WitP.BlindFrom j` of
    Ior/KnowWidePass.lean (`trBlind_witOf`).
  `rhoTo W j tr cm x π`: the chain up to round j (CompileK/ChainTo.lean) followed in the trace: none
    if one of its queries is missing; fixed values stand for the verifier messages from round j on.
  `extractorBTo W j wit`, `extractorBKTo`: as `extractorBT`, with `rhoTo`: none if a chain query
    before round j is not in its traces, if the chain up to round j does not run to an end (to a
    result `some`), or if π has no slot's string. At j = 0 it says none only for a proof without a
    slot's string (CompileK/WideZero.lean).
  The statements, each under the hypotheses of its statement:
  `Spec.bindingBatchTo`, `Spec.bindingUpTo`: index binding (`HasIndexBindingWith`), as
    `Spec.bindingBatchT`, `Spec.bindingUpT` of CompileK/KnowExtT.lean, for this extractor, for every
    j and every map with `TrBlind j`: the same hypotheses, the same relation `optR Rno`, the same
    bound `epsB`.
  `Spec.some_of_chainTo`: when it does not say none: if the chain up to round j runs within trC ++
    trP to an end, and no point has two answers there.

Limits: how often the answer is none while the verifier accepts is not bounded here. The status
beside the written description and the limits (2 excepted) in the head of CompileK/KnowExtT.lean
hold here too.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowExtT
import CompileK.ChainTo
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop

/-- The witness map reads no verifier message from round j on. -/
def TrBlind {X Wn : Type} {E : ExtSpec} {s : Shape} (j : ℕ) (wit : X → E.Str → Tr s → Wn) : Prop :=
  ∀ x y (τ τ' : Tr s),
    τ.read = τ'.read → τ.plains = τ'.plains → Rho.AgreeTo j τ.rho τ'.rho → wit x y τ = wit x y τ'

theorem trBlind_witOf {X Wn : Type} {E : ExtSpec} {s : Shape} {j : ℕ}
    {w : WitP X E s Wn} (h : w.BlindFrom j) : TrBlind j (witOf w) := by
  intro x y τ τ' h1 h2 h3
  show w x y τ.read τ.plains τ.rho = w x y τ'.read τ'.plains τ'.rho
  rw [h1, h2]
  exact h x y _ _ _ _ h3

end Iop

namespace Compile.Batch
open Iop Rom ZKCP Compile.GenMap Compile.GenPub
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L)

/-- The chain of a slot's string up to round j. -/
abbrev chainSTo (j : ℕ) (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    TypedOracleComputation lam W.K L (Option (Rho L.onlineBatch.loc.shape)) :=
  chainTo Tag.onl [cm] (some x) π.salt π.rtreq j L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh id
    0 .first π.roots π.plains

/-- The verifier messages before round j, followed in a trace. -/
def rhoTo (j : ℕ) (tr : Tc W) (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    Option (Rho L.onlineBatch.loc.shape) :=
  ((chainSTo W j cm x π).follow tr).join

/-- The natural extractor, up to round j. -/
def extractorBTo (j : ℕ) (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) :
    ZKCP.Gen.Extractor (spec lam W.K L) I X (Option Wn) (IVK lam L) (Prf lam L) where
  Ei := fun v tr => L.decodeIndex (extEnc W tr v.cm)
  Ew := fun _ trC x π trP => π.piB.bind fun πB =>
    (rhoTo W j (trC ++ trP) π.cm x πB).map fun ρ =>
      wit x (extEnc W (trC ++ trP) π.cm) (starB W (trC ++ trP) πB ρ)

/-- The same for the scheme with the links in the verification key. -/
def extractorBKTo (j : ℕ) (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) :
    Gen.Extractor (spec lam W.K L) I X (Option Wn) (IVKK lam L) (PrfK lam L) :=
  pullE liftK (pubE pubK (extractorBTo W j wit))

namespace Spec

def bindingBatchTo : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (j : ℕ)
      (Ryes Rno : I → X → Wn → Prop) (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (N : LH.Nums) (hsub : ∀ i x w, Ryes i x w → Rno i x w),
    L.SoundKT Rno wit N.εs → TrBlind j wit → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    L.onlineBatch.ann.Coherent → W.OKG → L.onlineBatch.loc.shape ≠ [] →
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW (optR Ryes) (optR Rno) (optR_sub hsub))
      (ZKCP.Gen.withW (Option Wn) (argB W WP p)) (extractorBTo W j wit) (epsB W N)

def bindingUpTo : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (j : ℕ)
      (Ryes Rno : I → X → Wn → Prop) (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (N : LH.Nums) (hsub : ∀ i x w, Ryes i x w → Rno i x w),
    L.SoundKT Rno wit N.εs → TrBlind j wit → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    L.onlineBatch.ann.Coherent → W.OKG → L.onlineBatch.loc.shape ≠ [] →
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW (optR Ryes) (optR Rno) (optR_sub hsub))
      (ZKCP.Gen.withW (Option Wn) (argBKE W WP p)) (extractorBKTo W j wit) (epsB W N)

def some_of_chainTo : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (j : ℕ)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (v : IVK lam L) (trC trP : Tc W)
      (x : X) (π : Prf lam L) (πB : OneProtocolProof lam L.onlineBatch) (ρ : Rho L.onlineBatch.loc.shape),
    π.piB = some πB → Trace.Fun (trC ++ trP) →
    RunsIn (trC ++ trP) (chainSTo W j π.cm x πB) (some ρ) →
    (extractorBTo W j wit).Ew v trC x π trP =
      some (wit x (extEnc W (trC ++ trP) π.cm) (starB W (trC ++ trP) πB ρ))

end Spec
end Compile.Batch
