-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecBinding.lean: extractor and bound for index binding of the compiled scheme.

The file has definitions only, for the scheme of Compile/Batch/Star.lean. The experiment of index
binding (ZKCP/Gen.lean) has one instance and one proof, whatever the number of slots: a proof holds
the proof string of one slot.

Names: `extractorB`, `tVQB`, `tVB`, and `epsB`, the bound.

Notation: `L`: an `BatchProtocol I X` (Iop/Batch.lean): "The five algorithms (I, D, Test, Link, Batch: `encodeIndex`,
`decodeIndex`, `offline`, `link`, `onlineBatch`), with the honest sides of the three protocols (`honestOfflineProver`, `honestLinkProver`, `honestOnlineBatchProver`)";
`W`: a `QueryLayout lam L` (Iop/BatchWire.lean): a wire record (lean/GLOSSARY.md: wire); `lam`: a natural
number: "Digests have `lam` bits" (the head of Compile/Batch/Oracles.lean); g: `OracleName.g t`, a
constructor of `OracleName` (Compile/Batch/Oracles.lean); `N.εs`: in `ℝ≥0∞`: a field of `LH.Nums`
(Iop/InteractiveOracleProof.lean), the third argument of `BatchProtocol.Sound` (Iop/Batch.lean); `tC`, `tP`: natural numbers:
in `HasIndexBindingWith` (ZKCP/Gen.lean): `Ct.QueryBound tC`, `(Pt st).QueryBound tP`.
-/
import Compile.Batch.Star
import Compile.Batch.Events

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- E_i: decode what the committer's trace determines under the root in ivk. E_w is empty. -/
def extractorB (W : QueryLayout lam L) :
    ZKCP.Gen.Extractor (spec lam W.K L) I X Unit (IVK lam L) (Prf lam L) where
  Ei := fun v tr => L.decodeIndex (extEnc W tr v.cm)
  Ew := fun _ _ _ _ _ => ()

/-- A bound on the queries of the verifier of one slot: one for each round, and one more to g in the
joining round; a leaf and a path for each opening; a leaf and a path in the request tree. -/
def tVQB {K : ℕ} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    (wq : ProtocolQueryLayout lam K Q) (depthReq : ℕ) : ℕ :=
  (Q.loc.shape.length + 1) + (wq.nOpen * (wq.maxDepth + 1) + (depthReq + 1))

/-- a bound on the queries of V on one proof: Test, Link, one slot of Batch -/
def tVB (W : QueryLayout lam L) : ℕ := tVQB W.T W.depthReq + tVQB W.Lk W.depthReq + tVQB W.B W.depthReq

def epsB (W : QueryLayout lam L) (N : LH.Nums) : ℕ → ℕ → ℝ≥0∞ := fun tC tP =>
  ((tC + tP + tVB W + 1 : ℕ) : ℝ≥0∞) * N.εs + 2 * ((tC + tP + tVB W + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

end Compile.Batch
