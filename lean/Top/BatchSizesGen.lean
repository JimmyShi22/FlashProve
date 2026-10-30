-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Top/BatchSizesGen.lean: numbers for the sizes of keys and proofs of the compiled scheme, for every
  record of protocols `L : BatchProtocol I X` and its data. The numbers are those of `L` before the challenges
  of the three protocols are derived from hash blocks (`BatchProtocol.draws`, Iop/BatchWireDraw.lean).
    `SizeLB L D`                      The numbers of `L`: widths that its serializers keep and
                                      numbers of opened positions, round by round, with the proofs.




  (Terms: lean/GLOSSARY.md.)

  Notation: a slot's verifier: the ordinary IOP that, with an annotation of its rounds,
  is a protocol with slots (Iop/Batch.lean).


  Limits: This file holds numbers and no formula. It does not prove that a key or a proof is at
  most any size, and it proves nothing on the verifier's queries.
  In Compile/Batch/Size.lean a root is counted only for a prover message with an oracle (`cRoots`;
  `nOrc`, `nRootsB`: Blocks/RootCount.lean).
  Three clauses of `FitsB` there are not tight (that file's head): among them, a request path is
  counted for Test and Link too.
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
import Compile.Batch.VCost
import Iop.BatchPullNamed
import Compile.AdaptiveExit
import Compile.CompleteAdaptive
import Compile.BindingManyExit
import Top.Extraction
import ZKCP.RefinedOfPerfect
import Compile.Ser
import Top.Simulator
import Mathlib.Data.FinEnum
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

noncomputable section

namespace Top.Batch
open Iop Rom Compile Compile.Batch Blocks
open Ser (gam)



/-! ## Every record of protocols -/

section Gen
variable {I X : Type} (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
  (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums)
  (ax : L.Aux pT pL pB) (p : Params) (D : SerLHB L)

/-- The numbers of a record of protocols before the hash blocks, with their proofs. -/
structure SizeLB where
  bT : BitsS L.offline.shape
  bL : BitsS L.link.shape
  bO : BitsS L.onlineBatch.loc.shape
  oT : OpenList L.offline.shape
  oL : OpenList L.link.shape
  oO : OpenList L.onlineBatch.loc.shape
  /-- bounds on the external positions that Test, Link and a slot's verifier read -/
  eT : ℕ
  eL : ℕ
  eO : ℕ
  sgBits : ℕ
  withinT : SerS.Within _ D.T bT
  withinL : SerS.Within _ D.Lk bL
  withinO : SerS.Within _ D.O bO
  sg : ∀ a, (D.sg.put a).length ≤ sgBits
  opensT : L.offline.OpensLe oT
  opensL : L.link.OpensLe oL
  opensO : L.onlineBatch.loc.OpensLe oO
  extT : ∀ x ρ, (L.offline.extReads x ρ).card ≤ eT
  extL : ∀ x ρ, (L.link.extReads x ρ).card ≤ eL
  extO : ∀ x ρ, (L.onlineBatch.loc.extReads x ρ).card ≤ eO

variable {L D} (B : SizeLB L D)

end Gen

end Top.Batch
