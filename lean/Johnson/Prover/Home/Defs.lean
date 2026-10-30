-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Home/Defs.lean: THE HONEST PROVER OF A WHOLE REQUEST OVER ONE HASH FUNCTION, WHERE
THE VERIFIER's INPUT IS READ OFF THAT HASH FUNCTION: AT LETTERS: over a told record (LayoutsByPublicReading,
Johnson/Top/InnerCompiledVerifierByPublicReading.lean). A PROGRAM, and its value at a hash function.

It runs the public reading; at what that gives (d) it runs the typed runs of a whole request (allY,
Johnson/Prover/All/Defs.lean) at d's wire of the record and code of the answers, at the committer's
coins and a draw that may both hang on d, carried over the one hash function through the coding at
d; and prints what they yield.

ARGUMENTS, not chosen here: how a typed program is carried over the hash function (carry: the
library's overOne, or an exit that asks fewer blocks and has the same value); the printer; the
strategies; the coins as functions of d.

Main names.
  runsAt      the typed runs at d.
  proveForm   the program.
  det_proveForm   its value at a hash function: the print, at d := the reading's value, of the typed
    runs' value under the typed functions that the coding at d reads out of the hash function.

Limits. Definitions and one equation. No probability. Tied to no program of the release.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.Defs
import Johnson.Top.InnerCompiledVerifierByPublicReading

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) {Kap Form : Type} (b₀ : R.LeafBody) (st : Strats R.protocol Kap)
  (capT capL capB : ℕ → ℕ)

/-- The typed runs of a whole request at what the public reading gave. -/
def runsAt (d : T.D) (isk : R.Index × R.protocol.EncodingRandomness × (ℕ → Bits)) (x : R.Instance)
    (dw : Draw 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits Kap) :
    OComp (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) (Raw 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) :=
  allY R.queryLayout (T.Sd d) (T.cA d) R.fixedSample b₀ st capT capL capB isk x dw

/-- **The honest prover over one hash function**, behind its coins. -/
def proveForm
    (carry : (d : T.D) → OComp (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) (Raw 256 R.protocol R.offlineRoundSplits
                                                                                   R.linkRoundSplits) →
      OComp (rom 256) (Raw 256 R.protocol R.offlineRoundSplits R.linkRoundSplits))
    (iskOf : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits)) (x : R.Instance)
    (drawOf : T.D → Draw 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits Kap) (print : T.D → Raw 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → Form) :
    OComp (rom 256) Form :=
  T.Pub.bind fun d =>
    (carry d (runsAt T b₀ st capT capL capB d (iskOf d) x (drawOf d))).bind fun y =>
      .pure (print d y)

/-- Its value at a hash function. -/
theorem det_proveForm
    (carry : (d : T.D) → OComp (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) (Raw 256 R.protocol R.offlineRoundSplits
                                                                                   R.linkRoundSplits) →
      OComp (rom 256) (Raw 256 R.protocol R.offlineRoundSplits R.linkRoundSplits))
    (iskOf : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits)) (x : R.Instance)
    (drawOf : T.D → Draw 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits Kap) (print : T.D → Raw 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → Form)
    (g : Fam (rom 256))
    (hov : (carry (T.Pub.det g) (runsAt T b₀ st capT capL capB (T.Pub.det g) (iskOf (T.Pub.det g)) x
      (drawOf (T.Pub.det g)))).det g =
        (runsAt T b₀ st capT capL capB (T.Pub.det g) (iskOf (T.Pub.det g)) x
          (drawOf (T.Pub.det g))).det (readBlocks (T.m (T.Pub.det g)) g)) :
    (proveForm T b₀ st capT capL capB carry iskOf x drawOf print).det g =
      print (T.Pub.det g) ((runsAt T b₀ st capT capL capB (T.Pub.det g) (iskOf (T.Pub.det g)) x
        (drawOf (T.Pub.det g))).det (readBlocks (T.m (T.Pub.det g)) g)) := by
  unfold proveForm
  rw [OComp.det_bind, OComp.det_bind, hov]
  rfl

end OnBytes.Prover
