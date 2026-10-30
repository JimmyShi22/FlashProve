-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecCompleteG.lean: towards completeness of the compiled scheme whose rounds may have
proof-of-work bits: two statements on small experiments. Statements only. (Words of this library:
lean/GLOSSARY.md.)

`Spec.unifTG`, `Spec.unifLG`: under `L.PropsNoAcc Ryes Rno M`, `W.OKG`, `GrFitB W Ryes` and `WP.OK`,
for every index i and lazily sampled oracles:
(T) `Ref.RT` (a fresh node and its Test) returns "bad" with probability at most pT plus `cFail` of
Test;
(L) `Ref.RL` (two fresh nodes and the Link from the first to the second) returns "bad" with
probability at most pL plus `cFail` of Link.
pT (pL) is the bound on the withheld set's probability in `L.PropsNoAcc`; `cFail` is the sum, over
the searches of one transcript, of (1 - 2^-b)^(more + 1).

Notation: "bad": the value `true` of `Ref.RT`, `Ref.RL` (`badAt`,
Compile/Batch/CompleteRefDefs.lean: "Is the proof string of slot number n `none`, or has a search
over nonces of its transcript failed"); `M`: an `LH.Nums` (Iop/InteractiveOracleProof.lean): "All numbers of the
interface"; pT, pL: its fields `M.pT`, `M.pL`, in `ℝ≥0∞`; b, more: fields of `GrW`
(Iop/BatchWire.lean): "the number of test bits"; "the honest prover tries the nonces 0, .., more: at
most more + 1 tries".

Limits: this file does not state completeness of the scheme, and it states nothing on the protocol
Batch. Further limits: the header of Compile/Batch/SpecGrind.lean.
-/
import Compile.Batch.StarX
import Compile.Batch.SpecGrind

noncomputable section

namespace Compile.Batch
open Iop Rom Prob Ref
open scoped ENNReal



def Spec.unifTG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Prop) (M : LH.Nums),
    L.PropsNoAcc Ryes Rno M → W.OKG → GrFitB W Ryes → WP.OK →
    ∀ i : I, pr (Ref.RT W WP p i).law {b | b = true} ≤ M.pT + cFail L.offline.shape _ W.T.sh

def Spec.unifLG : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Prop) (M : LH.Nums),
    L.PropsNoAcc Ryes Rno M → W.OKG → GrFitB W Ryes → WP.OK →
    ∀ i : I, pr (Ref.RL W WP p i).law {b | b = true} ≤ M.pL + cFail L.link.shape _ W.Lk.sh


end Compile.Batch
