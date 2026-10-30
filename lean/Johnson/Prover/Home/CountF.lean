-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Home/CountF.lean: the honest prover over one hash function (proveForm,
Johnson/Prover/Home/Defs.lean) where the typed runs are carried by the first-block exit.

Main names.
  carryF T pass   the value for proveForm's letter carry: at what the public reading gave (d): the
                  first-block exit at the coding T.m d and the test moreP (pass d).
  det_carryF      det_proveForm's premise at it: at every hash function and every d the carried
                  runs' value is the typed runs' at the typed functions read out.
  queryBound_carryF, queryBound_proveForm   THE PROVER's PROGRAM ASKS THE HASH FUNCTION AT MOST
                  tP + n TIMES, ON EVERY PATH: tP bounds the public reading, n bounds allF
                  (Johnson/Prover/All/CountF.lean) at all that may be drawn.

Limits. pass is a letter, and may hang on d. FirstIs and PassFits at every d are premises. The
printer asks nothing: it is a function. No probability.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Home.Defs
import Johnson.Prover.All.CountF
import Run.OverOneFRun

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R)

/-- The first-block exit as proveForm's carry. -/
def carryF (pass : T.D → Pass 256 (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) {α : Type} (d : T.D)
    (c : OComp (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) α) : OComp (rom 256) α :=
  c.overOneF (T.m d) (moreP (pass d))

variable {Kap Form : Type} (b₀ : R.LeafBody) (st : Strats R.protocol Kap) (capT capL capB : ℕ → ℕ)
  {hK : 0 < R.queryLayout.K} {pass : T.D → Pass 256 (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)}

/-- **det_proveForm's premise at carryF.** -/
theorem det_carryF (F : ∀ d, FirstIs hK (T.m d)) (H : ∀ d, PassFits R.queryLayout (T.Sd d) hK (pass d))
    (g : Fam (rom 256)) (d : T.D) (isk : R.Index × R.protocol.EncodingRandomness × (ℕ → Bits)) (x : R.Instance)
    (dw : Draw 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits Kap) :
    (carryF T pass d (runsAt T b₀ st capT capL capB d isk x dw)).det g =
      (runsAt T b₀ st capT capL capB d isk x dw).det (readBlocks (T.m d) g) :=
  det_overOneF (T.m d) (moreP (pass d)) g _ (factorsF_of hK (pass d) (T.m d) (F d)
    (factors_allY (T.cA d) R.fixedSample b₀ st capT capL capB (H d) isk x dw))

/-- The carried runs' queries to the hash function. -/
theorem queryBound_carryF (F : ∀ d, FirstIs hK (T.m d))
    (H : ∀ d, PassFits R.queryLayout (T.Sd d) hK (pass d)) (d : T.D) (isk : R.Index × R.protocol.EncodingRandomness × (ℕ → Bits))
    (x : R.Instance) (dw : Draw 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits Kap) :
    (carryF T pass d (runsAt T b₀ st capT capL capB d isk x dw)).QueryBound
      (allF R.queryLayout capT capL capB dw) := by
  refine queryBound_overOneF (T.m d) (moreP (pass d)) _ _ ?_
  have e : costF (T.m d) (moreP (pass d)) = costP hK (pass d) := by
    funext o q r
    exact costF_eq_costP hK (pass d) (T.m d) (F d) o q r
  rw [e]
  exact costBound_allY (T.cA d) R.fixedSample b₀ st capT capL capB (H d) isk x dw

/-- **The prover's program asks the hash function at most tP + n times, on every path.** -/
theorem queryBound_proveForm (iskOf : T.D → R.Index × R.protocol.EncodingRandomness × (ℕ → Bits)) (x : R.Instance)
    (drawOf : T.D → Draw 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits Kap) (print : T.D → Raw 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → Form)
    (tP n : ℕ) (hP : T.Pub.QueryBound tP) (F : ∀ d, FirstIs hK (T.m d))
    (H : ∀ d, PassFits R.queryLayout (T.Sd d) hK (pass d))
    (hn : ∀ d, allF R.queryLayout capT capL capB (drawOf d) ≤ n) :
    (proveForm T b₀ st capT capL capB (fun d => carryF T pass d) iskOf x drawOf print).QueryBound
      (tP + n) :=
  OComp.QueryBound.bind hP fun d =>
    (OComp.QueryBound.bind (t := 0)
      (queryBound_carryF T b₀ st capT capL capB F H d (iskOf d) x (drawOf d))
      (by intro _; trivial)).mono (by have := hn d; omega)

end OnBytes.Prover

#print axioms OnBytes.Prover.det_carryF
#print axioms OnBytes.Prover.queryBound_carryF
#print axioms OnBytes.Prover.queryBound_proveForm
