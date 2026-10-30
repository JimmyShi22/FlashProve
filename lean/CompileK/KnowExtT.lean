-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowExtT.lean: the natural witness extractor for a witness map that reads the whole local
transcript.

This file is about witness extraction from a non-interactive argument in the random-oracle model: an
extractor without rewinding, which reads the proof and the lists of queries of the committer and the
prover.
Definitions and statements (the proofs: CompileK/KnowSoundT.lean, CompileK/KnowBindingT.lean). Over
the compiler's typed oracles. The witness extractor is handed five things: the key, the committer's
trace, the instance, the proof, the prover's trace. No oracle, and not the verifier's queries. For a
witness map that reads oracles alone that is enough (CompileK/KnowExt.lean). A wide map
(Ior/KnowWide.lean, Hiop/KnowWide.lean) also reads plain parts, which stand in the proof, and
verifier messages, which are answers to the Fiat-Shamir queries of the slot's chain.

Main names:
  `rhoB W tr cm x π`: follow the slot's chain in the trace (CompileK/Follow.lean): the verifier's
    own algorithm for the chain, every answer looked up; none if a query of the chain does not stand
    in the trace.
  `starB W tr π ρ`: the extracted local transcript τ∗ (`trStar`, Compile/Batch/Runs.lean): oracles
    by Merkle extraction under the roots of π, the plain parts of π (of a component that is not
    sent, that of the fixed message), the verifier messages ρ.
  `extractorBT W wit`: E_i as in `extractorB` (Compile/Batch/SpecBinding.lean). E_w(key, trC, x, π,
    trP): follow the chain in trC ++ trP; if it is all there and runs to an end (`some`: no round's
    format is undefined, no root is missing): some (wit x y τ∗), y the encoded index extracted under
    the root on which the slot runs; if not, or if π has no slot's string: none ("the chain of this
    proof is not in my traces").
  `extractorBKT`: the same for the scheme with the links in the key (`argBKE`).
  `optR R`: the relation for such an answer: some w: R i x w; none: some witness exists.
  The statements, each under the hypotheses of its statement:
  `Spec.bindingBatchT`: index binding of the base scheme (`argB`), in the syntax with witnesses in
    `Option Wn`, for the relation `optR Rno`, with `extractorBT` and exactly the bound `epsB` of the
    theorem on languages (`bindingBatchAt`, Compile/Batch/GlueBinding.lean). In words: but for ε, an
    accepted (x, π) has an extracted index i, and the extractor either names a witness of (i, x),
    read off the transcript that the prover hashed and the challenges that it was given, or says
    that the chain is not in its traces, and then a witness exists.
  `Spec.bindingUpT`: the same for the scheme with the links in the key.
  `Spec.some_of_chain`: when it does not say none: if the slot's chain runs within trC ++ trP to an
    end, and no point has two answers there, the answer is some.

Limits: how often the answer is none while the verifier accepts is not bounded here. Nothing forces
a prover to ask the chain queries of its own proof, and for an arbitrary interface it cannot be
forced (take a verifier that ignores its last message). On such runs the statement says no more than
soundness. The bound needs more of the interface (the map reads nothing from the last draw of
positions on; fresh verifier messages rarely ask a given list of positions) and would be a lemma of
its own (as a hypothesis: `MissLe`, CompileK/TotalExt.lean).
Status beside the compilation of this protocol's technical report (lean/CREDITS.md; a comparison by
reading, of one of its prints, not held against the report's latest edition; that report is
unrefereed): at the time of writing its witness extractor recomputes the witness from the extracted
index and the instance, so this file renders no step of it. Here a
witness is read out of what the prover sent.
Limits of the form. (1) The answer is in Option, and `optR` is another relation than Rno: a step on
the way (the total form: CompileK/TotalExt.lean). (2) This extractor gives up if any query of the
chain is missing, the last ones too (up to a round: CompileK/KnowExtTo.lean). (3) E_i is `L.decodeIndex` of
the extracted string, and E_w of `extractorBT` does not read the key (that of `extractorBKT` takes
from the key's links the root of the pair that the proof names: `reK`, Compile/Batch/StarK.lean):
`L.decodeIndex` reads the encoded index alone. (4) The witness map is a parameter: that a given decoder is a
witness map with `BatchProtocol.SoundKT` is the interface's matter.
Not over one oracle: the passage to one oracle (Rom/Family.lean) asks that an extractor read
one-block answers only; a Fiat-Shamir answer has several blocks. This file says nothing on running
time. Equality of queries is decided classically. A session must have at least one round.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowStar
import CompileK.KnowBindingUp
import CompileK.Follow
import Hiop.KnowWide
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom ZKCP Compile.GenMap Compile.GenPub
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The relation for an extractor that may say "the chain is not in my traces". -/
def optR (R : I → X → Wn → Prop) : I → X → Option Wn → Prop
  | i, x, some w => R i x w
  | i, x, none => ∃ w, R i x w

theorem optR_sub {Ry Rno : I → X → Wn → Prop} (sub : ∀ i x w, Ry i x w → Rno i x w) :
    ∀ i x o, optR Ry i x o → optR Rno i x o
  | i, x, some w, h => sub i x w h
  | i, x, none, ⟨w, h⟩ => ⟨w, sub i x w h⟩

variable (W : QueryLayout lam L)

/-- The chain of a slot's string, as the verifier recomputes it. -/
abbrev chainS (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    TypedOracleComputation lam W.K L (Option (Rho L.onlineBatch.loc.shape × RootsOfChain lam L.onlineBatch.loc.shape × Phase lam)) :=
  recomputeChainOfProof Tag.onl L.onlineBatch W.B id some [cm] x π

/-- The verifier messages of the slot's chain, followed in a trace. -/
def rhoB (tr : Tc W) (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    Option (Rho L.onlineBatch.loc.shape) :=
  ((chainS W cm x π).follow tr).join.map fun z => z.1

/-- The extracted local transcript. -/
def starB (tr : Tc W) (π : OneProtocolProof lam L.onlineBatch) (ρ : Rho L.onlineBatch.loc.shape) :
    Tr L.onlineBatch.loc.shape :=
  trStar tr L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh (prjSym Tag.onl) (rtsB W π) π.plains ρ

/-- The natural extractor. -/
def extractorBT (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) :
    ZKCP.Gen.Extractor (spec lam W.K L) I X (Option Wn) (IVK lam L) (Prf lam L) where
  Ei := fun v tr => L.decodeIndex (extEnc W tr v.cm)
  Ew := fun _ trC x π trP => π.piB.bind fun πB =>
    (rhoB W (trC ++ trP) π.cm x πB).map fun ρ =>
      wit x (extEnc W (trC ++ trP) π.cm) (starB W (trC ++ trP) πB ρ)

/-- The same for the scheme with the links in the verification key. -/
def extractorBKT (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) :
    Gen.Extractor (spec lam W.K L) I X (Option Wn) (IVKK lam L) (PrfK lam L) :=
  pullE liftK (pubE pubK (extractorBT W wit))

namespace Spec

/-- Index binding with the natural extractor, base scheme, typed oracles, the bound of the theorem
on languages. (not all hypotheses are named here: see the statement below) -/
def bindingBatchT : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Wn → Prop) (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (N : LH.Nums) (hsub : ∀ i x w, Ryes i x w → Rno i x w),
    L.SoundKT Rno wit N.εs → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    L.onlineBatch.ann.Coherent → W.OKG → L.onlineBatch.loc.shape ≠ [] →
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW (optR Ryes) (optR Rno) (optR_sub hsub))
      (ZKCP.Gen.withW (Option Wn) (argB W WP p)) (extractorBT W wit) (epsB W N)

/-- The same for the scheme with the links in the key. (not all hypotheses are named here: see the
statement below) -/
def bindingUpT : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Wn → Prop) (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (N : LH.Nums) (hsub : ∀ i x w, Ryes i x w → Rno i x w),
    L.SoundKT Rno wit N.εs → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    L.onlineBatch.ann.Coherent → W.OKG → L.onlineBatch.loc.shape ≠ [] →
    ZKCP.Gen.HasIndexBindingWith (ZKCP.Gen.relPairW (optR Ryes) (optR Rno) (optR_sub hsub))
      (ZKCP.Gen.withW (Option Wn) (argBKE W WP p)) (extractorBKT W wit) (epsB W N)

/-- When the extractor does not say none. -/
def some_of_chain : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (v : IVK lam L) (trC trP : Tc W)
      (x : X) (π : Prf lam L) (πB : OneProtocolProof lam L.onlineBatch)
      (z : Rho L.onlineBatch.loc.shape × RootsOfChain lam L.onlineBatch.loc.shape × Phase lam),
    π.piB = some πB → Trace.Fun (trC ++ trP) → RunsIn (trC ++ trP) (chainS W π.cm x πB) (some z) →
    (extractorBT W wit).Ew v trC x π trP =
      some (wit x (extEnc W (trC ++ trP) π.cm) (starB W (trC ++ trP) πB z.1))

end Spec
end Compile.Batch
