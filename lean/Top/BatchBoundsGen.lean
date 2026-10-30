-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Top/BatchBoundsGen.lean: a record of counts for the three protocols, and four formulas in it.

The bounds of the compiled scheme (Compile/Batch/) are monotone in a few numbers of the protocols
Test, Link and Batch (`BatchProtocol`, Iop/Batch.lean; a slot is one request's
part of Batch; other words of this library: lean/GLOSSARY.md). `CountNumsB` is a record of such
numbers:
  N            the number of slots;
  rT, rL, rO   rounds of Test, Link, Batch;
  dT, dL, dO   depths (the larger of the depth of an encoded index and of the protocol's deepest
               Merkle tree);
  dR           the depth of a request tree;
  lI           Merkle leaves of an encoded index;
  lT, lL       Merkle leaves of all trees of one execution of Test, Link;
  lJ, l0       Merkle leaves of the trees of one slot of a batch, and of its shared trees
               (Top/BatchLeaves.lean);
  e            the largest round-by-round error;
  pT, pL, pO   the probabilities that the honest prover aborts;
  zT, zL, zO   the simulation errors.
`CountsB L .. M c` states that `c.N` is the number of slots of the record of protocols `L`, and that
`c` bounds the other counts of `L` (with the depth of a request tree, from the argument `ax`) and
seven of the numbers in `M : LH.Nums`: εs, pT, pL, pO, zT, zL, zO. Four formulas in `c`, in the
numbers of opened positions and in the scheme's parameters `p`, are meant to bound terms of
Compile/Batch/: `tv` for `tVB`, `A` for `xTree`, `Bf` for `xFb`, `Rq` for `xReq` (see their
docstrings). In them n counts batches, and `p.leaves` is the number of copies of the encoded index,
not of Merkle leaves. Top/BatchBoundsGenDr.lean proves, under `CountsB` and for protocols with
challenge samplers, that the first three bound their terms and that the fourth equals its term.

Limits: All queries counted are queries to the typed oracles (one random oracle for each kind of
query: lean/GLOSSARY.md). That `tVB`, `xTree`, `xFb` and `xReq` bound what the docstrings
say is used inside the proofs of Compile/Batch/ and is not a statement here. The error, the
probabilities and the simulation errors are those before challenges are sampled from hash blocks;
the error is that of the protocols with batches. No statement here is a security level.
-/
import Rom.ExitPriv
import Iop.WireOf
import Iop.PullProofs
import Code.FieldEnum
import ZKCP.Defs
import Mathlib.Data.Matrix.Mul
import Code.RS
import Code.Field
import Iop.Univ
import Blocks.Opens
import Blocks.Numbering
import Blocks.LowerKit
import Blocks.SerS
import Iop.WireOK
import Blocks.Small
import Blocks.Leaves
import Compile.SizeAccepted
import Blocks.Sizes
import Compile.Batch.SizeAccepted
import Blocks.Batch.Numbering
import Blocks.Batch.Hvzk
import Blocks.Batch.Sound
import Blocks.Batch.One
import Iop.SerB
import Blocks.RootCount
import Blocks.Batch.Fmt
import Compile.Batch.CompleteRefStarG
import Compile.Batch.CompleteUnifG
import Compile.Batch.DisciplineChainAll
import Compile.Batch.EqBatch
import Compile.Batch.EqProve
import Compile.Batch.EqSetup
import Compile.Batch.GluePrivacy
import Compile.Batch.HopLate
import Compile.Batch.HopTot
import Compile.Batch.Late4
import Compile.Batch.LifeStar
import Compile.Batch.Lump
import Compile.Batch.OverrunGen
import Compile.Batch.Ser
import Compile.Batch.Sound
import Compile.Batch.WithinVCB
import Iop.BatchPullFmt
import Iop.BatchWireOK
import Iop.SerBPull
import Top.BatchLeaves
import Prob.Tail
import Rom.EagerAudited
import Compile.Extraction
import Top.Extraction
import Mathlib.Analysis.Complex.ExponentialBounds
import Prob.TailSharp
import Compile.AdaptiveExit
import Compile.CompleteAdaptive
import Compile.BindingManyExit
import ZKCP.RefinedOfPerfect
import Compile.Ser
import Compile.Batch.VCost
import Iop.BatchPullNamed
import Top.Simulator
import ZKCP.SpecialAny
import Mathlib.Data.FinEnum
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section

namespace Top
open Iop Rom ZKCP Compile Compile.Batch Blocks Top.BatchLeaves
open scoped ENNReal

/-- The counts of the three protocols. Numbers only. -/
structure CountNumsB where
  N : ℕ
  rT : ℕ
  rL : ℕ
  rO : ℕ
  dT : ℕ
  dL : ℕ
  dO : ℕ
  dR : ℕ
  lI : ℕ
  lT : ℕ
  lL : ℕ
  lJ : ℕ
  l0 : ℕ
  e : ℝ≥0∞
  pT : ℝ≥0∞
  pL : ℝ≥0∞
  pO : ℝ≥0∞
  zT : ℝ≥0∞
  zL : ℝ≥0∞
  zO : ℝ≥0∞

/-- What the record of counts must bound. -/
structure CountsB {I X : Type} (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint) (pL : L.link.shape.IsPoint)
    (pB : L.onlineBatch.loc.shape.IsPoint) (ax : L.Aux pT pL pB) (M : LH.Nums) (c : CountNumsB) : Prop where
  N : L.maxBatchSize = c.N
  rT : L.offline.shape.length ≤ c.rT
  rL : L.link.shape.length ≤ c.rL
  rO : L.onlineBatch.loc.shape.length ≤ c.rO
  dT : max (Nat.clog 2 L.wordLength) (depths L.offline.shape pT) ≤ c.dT
  dL : max (Nat.clog 2 L.wordLength) (depths L.link.shape pL) ≤ c.dL
  dO : max (Nat.clog 2 L.wordLength) (depths L.onlineBatch.loc.shape pB) ≤ c.dO
  dR : ax.depthReq ≤ c.dR
  lI : 2 ^ Nat.clog 2 L.wordLength ≤ c.lI
  lT : leaves L.offline.shape pT ≤ c.lT
  lL : leaves L.link.shape pL ≤ c.lL
  lJ : lvJ L.onlineBatch.loc.shape L.onlineBatch.ann pB ≤ c.lJ
  l0 : lv0 L.onlineBatch.loc.shape L.onlineBatch.ann pB ≤ c.l0
  e : M.εs ≤ c.e
  pT : M.pT ≤ c.pT
  pL : M.pL ≤ c.pL
  pO : M.pO ≤ c.pO
  zT : M.zT ≤ c.zT
  zL : M.zL ≤ c.zL
  zO : M.zO ≤ c.zO

namespace CountNumsB
variable (c : CountNumsB) (no : OpenNums) (p : Params) (lam n0 : ℕ)

/-- a bound for Compile.Batch's term tVB: the verifier's typed queries on one proof -/
def tv : ℕ :=
  ((c.rT + 1) + (no.T * (c.dT + 1) + (c.dR + 1))) +
    ((c.rL + 1) + (no.L * (c.dL + 1) + (c.dR + 1))) +
    ((c.rO + 1) + (no.O * (c.dO + 1) + (c.dR + 1)))
/-- a bound for xTree: leaves of all trees of the honest committer and prover in the set-up and n
batches -/
def A (n : ℕ) : ℕ :=
  (p.leaves + 1) * c.lI + (c.lT + c.rT) + p.leaves * (c.lL + c.rL) + n * (c.N * c.lJ + c.l0)
/-- a bound for xFb: Fiat-Shamir queries of the honest committer and prover in the set-up and n
batches -/
def Bf (n : ℕ) : ℕ := 2 * c.rT + p.leaves * (2 * c.rL) + n * ((c.N + 1) * c.rO)
/-- xReq: queries of the honest committer and prover to the typed oracle g (`OracleName.g`,
Compile/Batch/Oracles.lean) -/
def Rq (n : ℕ) : ℕ := n * c.N

end CountNumsB

theorem CountsB.arV {len n m dr len' m' dr' : ℕ} (h1 : len ≤ len') (h2 : m ≤ m') (h3 : dr ≤ dr') :
    (len + 1) + (n * (m + 1) + (dr + 1)) ≤ (len' + 1) + (n * (m' + 1) + (dr' + 1)) :=
  Nat.add_le_add (Nat.succ_le_succ h1)
    (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.succ_le_succ h2)) (Nat.succ_le_succ h3))

end Top
