-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/GrindMain.lean: the compiler with proof of work ("grinding").

Definitions; this file states no theorem on the scheme with work.
The compiler takes any holographic interface L with all properties with a witness (`BatchProtocol.PropsK`);
CompileK/Main.lean has no proof of work. Here every round of the three IOPs may be given a
number b of test bits. In a round with b > 0 test bits the prover's message ends in a nonce, the
hash that gives the verifier message gives b further bits, and the verifier rejects unless all of
them are 0 (the step on interfaces: Iop/Grind.lean, Iop/BatchGrind.lean; on wires:
Iop/GrindWire.lean; the honest prover tries nonces one after the other, up to a cap).
It was asked that soundness be measured round by round, each round counted WITH its work; this file
is that count carried to the compiled argument (lean/CREDITS.md).

Main names:
  `Work Nn L`: the data of the work (fields `Dg`, `nb`, `gT`, `gL`, `gB`).
  `D.LWk w`, `D.WWk w`, `D.WPWk w`: the interface and the wires: a block of its own gives the test
    bits.
  `schemeWk`, `extractorWk`, `simulatorWk`, `codingWk`: the scheme, the extractor, the simulator, a
    named coding over one oracle: the terms of CompileK/Main.lean at these wires. The witness
    extractor applies the same map wit to the same symbols: a nonce stands in the plain part of a
    message, in no oracle.
  `FitWk`: conditions on the work, to be discharged at the instance: every number of bits is at most
    nb ≤ λ; the numbers that are tried are read back from their nonces.
  `BatchProtocol.SoundKG L Rno wit gT gL gB c` (Hiop/GrindK.lean), the hypothesis on soundness: there are
    three lists of errors, one for each of L's three IOPs, at which `BatchProtocol.SoundAtK` holds
    (index-binding round-by-round knowledge soundness), and in these lists a round with b test bits
    has, as a probability, an error of at most c · 2^b (`Err.BelowG`). So with its work counted no
    round exceeds c. A round that has no test must itself be at most c: no other round's work helps
    it. From `BatchProtocol.PropsK` it holds at c = M.εs for every choice of bits (`Iop.soundKG_of_soundK`):
    then nothing is gained in ε. The gain: an interface whose bare errors are too large in some
    rounds (fewer opened positions, a smaller field) meets it at a small c if these rounds are given
    work.








The bounds, in the compiler's own terms at the wire with tests. (Each of them tied to the same term
at the wire without tests, closed forms, and the three bounds at lists of zeros:
CompileK/GrindCost.lean.)
  ε = `epsB` at κ₀^K · c: (tC + tP + tV + 1) · κ₀^K · c + 2 (tC + tP + tV + 2)² / 2^λ, tV the
    verifier's queries, as many as without work. Every try of a nonce is one of the cheat's tC + tP
    queries. The hash term gets no factor.
  α = that of the wire without tests + for each round with a test the chance
    (1 - 2^-b)^(cap on the tries) that no try passes: offline once, the link once, a session's
    rounds maxBatchSize times each (a union bound over the slots: a shared round too).
  ζ = that of the wire without tests + one term: (number of searches) · (number of Fiat-Shamir
    queries, every try of the honest side counted at its cap) / 2^min(sFS, λ). The part that is
    linear in the adversary's number of queries does not move.

Limits: what the head of CompileK/Main.lean lists as not said is not said here either.


  * At lists of zeros this is not the scheme without work: every answer of the
    Fiat-Shamir oracle has one block more, which nobody reads; the oracles' types differ. No lemma
    ties the two schemes. This file says nothing on "no work" as a case of its own:
    CompileK/GrindOpt.lean.


  * In the query model a query costs 1 whatever it is: b bits of work are b bits of the cheat's
    queries, no more. No number here is a security level. This file does not say what "128 bits
    with b bits of work" means and does not mean: the headers of Iop/Grind.lean and
    Compile/Batch/SpecGrind.lean.
  * A failed search gives no notice: the string is handed out all the same (and the verifier
    rejects it); a failed search of the committer leaves a bad key. That is inside α. This file
    says nothing on a prover that stops, nor on a committer that starts again.
  * This file says nothing on the mean number of tries, on running times, on sizes. It says nothing
    on the forms with work for the honest committer (CompileK/GrindHonest.lean) and for many pairs.


Terms: lean/GLOSSARY.md.
-/
import CompileK.Main
import Hiop.GrindK
import Iop.GrindPull
import Iop.GrindWire
import Iop.GrindData
import Compile.Batch.SimsGrind

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw
open Compile.BatchLife (Sims)
open scoped ENNReal

variable {I X : Type}

/-- The data of the work. Nn is the type of nonces. -/
structure Work (Nn : Type) (L : BatchProtocol I X) where
  /-- how many nonces are tried at most in a round with b test bits; the nonce for a number; the
  number of a nonce -/
  Dg : GrData Nn
  /-- a bound on all numbers of test bits -/
  nb : ℕ
  /-- the numbers of test bits: one for each round of the offline IOP, of the link IOP, of a
  session -/
  gT : GBits L.offline.shape
  gL : GBits L.link.shape
  gB : GBits L.onlineBatch.loc.shape

variable {L₀ : BatchProtocol I X} {lam : ℕ} {Nn : Type} [Inhabited Nn] (D : DataK L₀ lam) (w : Work Nn L₀)

/-- the three lists on the shapes after verifier messages are made from blocks: the same numbers -/
abbrev DataK.gTd : GBits D.L.offline.shape := w.gT.pull (Samplers.ofDraws _ D.dr.T)
abbrev DataK.gLd : GBits D.L.link.shape := w.gL.pull (Samplers.ofDraws _ D.dr.Lk)
abbrev DataK.gBd : GBits D.L.onlineBatch.loc.shape := w.gB.pull (Samplers.ofDraws _ D.dr.B)

/-- the interface: verifier messages from blocks, then the tests; its wires -/
abbrev DataK.LWk : BatchProtocol I X := D.L.grind Nn (D.gTd w) (D.gLd w) (D.gBd w)
abbrev DataK.WWk : QueryLayout lam (D.LWk w) := D.W.grind w.Dg (D.gTd w) (D.gLd w) (D.gBd w)
abbrev DataK.WPWk : WireBP (D.LWk w) := D.WP.grind (D.gTd w) (D.gLd w) (D.gBd w)

/-- the numbers after the blocks; c bounds every round's error of L₀ counting its work (in this
file's statements: by their hypothesis `BatchProtocol.SoundKG`) -/
abbrev DataK.numsWk (M : LH.Nums) (κ₀ : ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞) : LH.Nums :=
  { D.nums M κ₀ n with εs := κ₀ ^ D.dr.K * c }

/-- The scheme with work. -/
def schemeWk (Wn : Type) :
    Gen.Arg (spec lam (D.WWk w).K (D.LWk w)) I X Wn (IVKK lam (D.LWk w))
      (ISK lam (D.LWk w)) (PrfK lam (D.LWk w)) :=
  Gen.withW Wn (argBKE (D.WWk w) (D.WPWk w) D.p)

/-- The extractor: the same witness map on the same symbols. -/
def extractorWk {Wn : Type} (wit : X → Orcs L₀.onlineBatch.loc.shape → Wn) (w0 : Wn) :
    Gen.Extractor (spec lam (D.WWk w).K (D.LWk w)) I X Wn
      (IVKK lam (D.LWk w)) (PrfK lam (D.LWk w)) :=
  extractorBKW (D.WWk w)
    (fun x o => wit x (Orcs.push (Samplers.ofDraws _ D.dr.B) (Orcs.strip (D.gBd w) o))) w0

/-- The simulator, around simulators of the three IOPs of L₀. -/
def simulatorWk (Sm : Sims L₀) :
    Gen.Simulator (spec lam (D.WWk w).K (D.LWk w)) Unit (IVKK lam (D.LWk w))
      X (PrfK lam (D.LWk w)) :=
  simBKGr (D.WWk w) D.p ((simsD lam L₀ D.dr Sm).grind (D.gTd w) (D.gLd w) (D.gBd w)) D.i₀

/-- A named coding of typed queries as strings, from serialisers for the interface and for
nonces. -/
def codingWk (Se : SerLHB L₀) (sW : Ser Nn) : OracleCoding (spec lam (D.WWk w).K (D.LWk w)) lam :=
  implReal ((Se.pull (Samplers.ofDraws _ D.dr.T)
        (Samplers.ofDraws _ D.dr.Lk) (Samplers.ofDraws _ D.dr.B)).grind
      sW (D.gTd w) (D.gLd w) (D.gBd w))
    lam (D.WWk w).K

/-- Conditions on the work, to be discharged at the instance. -/
structure FitWk (lam : ℕ) (w : Work Nn L₀) : Prop where
  /-- the numbers that are tried in a round with at most nb test bits are read back from their
  nonces -/
  read : w.Dg.OK w.nb
  /-- one block gives the test bits -/
  le   : w.nb ≤ lam
  allT : w.gT.AllLe w.nb
  allL : w.gL.AllLe w.nb
  allB : w.gB.AllLe w.nb

namespace Spec

end Spec
end Compile.Batch
