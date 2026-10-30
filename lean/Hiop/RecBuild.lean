-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecBuild.lean: this file composes the building blocks of Hiop/RecSubs.lean into the holographic
interactive oracle proof, and bundles the hypotheses on them.

Terms only. `C : ConfigurationWithOutOfDomainSample` is a configuration (Hiop/RecConf.lean), `S : SubsR C` the four sub-protocols
(Hiop/RecSubs.lean), `HolographicProtocol` the type of the object (Hiop/RecInterface.lean).

A preamble is an interactive oracle reduction (`IOR`, Ior/Ior.lean) whose output is a statement of
the constraint relation (`Left.Rlin`, Hiop/RecConf.lean); the IOPP is an IOP on such statements.

Main names:
  `lhr`: the object. Its parts:
    committer: i, (η, r) ↦ the encoding of `hold i η` under r.
    record phase: seed s ↦ the answers of the message `hold i η` to s. After each encoded index,
      outside the three protocols.
    index decoder: `ConfigurationWithOutOfDomainSample.D`: none at a collision; else `held` of the message decoded with the
      record.
    offline IOP (`offline`), on a record rec: the preamble of weights-formedness, then the IOPP (one
      instance).
    link IOP, on (rec, rec'): the link.
    a session (`session`), on (x, rec) in every slot: the preamble of a request, then the IOPP for
      at most N instances.
    The honest prover of a slot uses the cells `trace i x` (why: CompileK/GenWit.lean).
  `wit`: the witness map of a session; see its docstring. It reads the slot's statement and its
    local transcript.
  `HypH`, `HypK`, `Hyp`: the hypotheses on the sub-protocols; see their docstrings.

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecSubs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Hiop
open Iop Prob
open scoped ENNReal

namespace SubsR
variable {C : ConfigurationWithOutOfDomainSample} (S : SubsR C)

/-- the offline IOP and its honest side -/
def offline : IOR C.Rec C.E0 Unit extNone := S.wf.seq S.linOff
def hOffline : S.offline.Honest C.PIdx Unit := S.hWf.seq S.hLinOff

/-- a session -/
def session : BIOP (C.X × C.Rec) C.E0 := online S.req S.linOn

/-- The witness map of a session: decode the oracles that the preamble leaves, with the samples in
the claims that the preamble's verifier outputs (`S.dOn` where they do not decode); then the
preamble's extractor `cellsOf`. `C.cells0` where that verifier rejects. -/
def wit : C.X × C.Rec → C.E0.Str → Tr (S.req.shape ++ S.linOn.ior.shape) → C.Cells :=
  witSeqT S.req S.cellsOf (fun a _ _ => S.on.decA S.dOn a.1.1 a.2) C.cells0

/-- The holographic IOP with an untrusted committer and a record phase after each encoded index. -/
def lhr : HolographicProtocol C.I C.X where
  wordLength := C.n
  Symbol := C.Sg
  EncodingRandomness := C.Pad × C.Rnd
  encodeIndex := fun i r => C.enc (C.hold i r.1) r.2
  OutOfDomainSeed := C.Seed
  OutOfDomainAnswer := C.Ans
  honestOutOfDomainAnswer := fun i r s => C.smp s (C.hold i r.1)
  hasCollisionAt := C.coll
  decodeIndex := C.D
  offline := S.offline.toInteractiveOracleProof
  link := S.link.toInteractiveOracleProof
  maxBatchSize := S.N
  onlineBatch := S.session.toBatch
  honestOfflineProver := S.hOffline.toProto (fun w => C.enc (C.hold w.1 w.2.1.1) w.2.1.2)
    (fun w _ => C.pidx w.1 w.2.1 w.2.2)
  honestLinkProver := S.hLink.toProto
    (fun w => (C.enc (C.hold w.1 w.2.1.1.1) w.2.1.1.2, C.enc (C.hold w.1 w.2.2.1.1) w.2.2.1.2))
    (fun w _ => (C.pidx w.1 w.2.1.1 w.2.1.2, C.pidx w.1 w.2.2.1 w.2.2.2))
  honestOnlineBatchProver := onlineHonest S.req S.linOn S.hReq S.hLinOn (fun w => C.enc (C.hold w.1 w.2.1.1) w.2.1.2)
    (fun w => C.pidx w.1 w.2.1 w.2.2) (fun w a => (C.pidx w.1 w.2.1 w.2.2, C.trace w.1 a.1))
  early := id
  late := none

/-- The numbers of the four parameter lists. -/
structure Nums where
  wf     : PreNums S.wf
  linOff : LinNumsR S.linOff.shape
  link   : LinkNums S.link.shape
  req    : PreNums S.req
  linOn  : LinBNums S.linOn.ior.shape S.N

variable {S}

open Classical in
/-- The four parameter lists without their items on knowledge soundness (the IOPP at its two
settings), and that the encodings of the oracles which a preamble leaves bear what the IOPP's
verifier reads of them (`fitOff`, `fitOn`). -/
structure HypH (P : S.Nums) : Prop where
  wf     : PreListR S.off S.wf S.hWf id id C.Rwf P.wf
  linOff : LinListR S.off S.linOff S.hLinOff P.linOff
  link   : LinkListR S.link S.hLink P.link
  req    : PreListR S.on S.req S.hReq Prod.snd Prod.fst C.Rreq P.req
  linOn  : LinBListR S.on S.linOn S.hLinOn S.N P.linOn
  fitOff : ∀ ρ₁ ρ₂, P.wf.bud ρ₁ ((S.linOff.extReads ρ₂).biUnion (S.wf.srcO ρ₁))
  fitOn  : ∀ ρ₁ ρ₂, P.req.bud ρ₁ ((S.linOn.ior.extReads ρ₂).biUnion (S.req.srcO ρ₁))

/-- The items on round-by-round knowledge soundness of the four parameter lists. Weights-formedness:
on statements without a collision. A request: on statements whose index decoder answers. -/
structure HypK (P : S.Nums) : Prop where
  wf     : PreKnowR S.off S.wf C.free C.RwfR (fun _ _ _ => ()) P.wf.err
  linOff : LinKnowR S.off S.linOff S.dOff P.linOff.err
  link   : LinkKnowR S.link P.link.err
  req    : PreKnowR S.on S.req (fun a => (C.D a.2 a.1.2).isSome) C.RreqR S.cellsOf P.req.err
  linOn  : LinBKnowR S.on S.linOn S.N S.dOn P.linOn.err

/-- The hypotheses on the sub-protocols in the conditional theorems: the four parameter lists, whole
(`HypH`, with its `fitOff` and `fitOn`, and `HypK`). -/
structure Hyp (P : S.Nums) : Prop where
  honest : S.HypH P
  know   : S.HypK P

/-- Every round-by-round error of the lists, as a probability, is at most εs. -/
structure Nums.Below (P : S.Nums) (εs : ℝ≥0∞) : Prop where
  wf     : Err.Below P.wf.err εs
  linOff : Err.Below P.linOff.err εs
  link   : Err.Below P.link.err εs
  req    : Err.Below P.req.err εs
  linOn  : Err.Below P.linOn.err εs

/-- The numbers of the holographic IOP. -/
def Nums.lh (P : S.Nums) (b : ℕ) (εs : ℝ≥0∞) : LH.Nums where
  b := b
  qT := P.linOff.q
  qpar := P.link.qpar
  qch := P.link.qch
  qon := P.linOn.q
  εs := εs
  zT := P.wf.pHid
  zL := 0
  zO := P.req.pHid
  pT := P.wf.pBad + P.wf.pHid + P.linOff.pBad
  pL := P.link.pBad
  pO := P.req.pBad + P.req.pHid + P.linOn.pBad

end SubsR
end Hiop
