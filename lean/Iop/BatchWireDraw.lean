-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchWireDraw.lean: the wire records of an `BatchProtocol` with arbitrary challenge samplers. (Words of
this library: lean/GLOSSARY.md.)

The file has definitions and statements; the proofs are in Iop/BatchWireDrawOK.lean. An `BatchProtocol`
(Iop/Batch.lean) holds an encoder, a decoder and the protocols Test, Link and Batch. A wire record
(Iop/BatchWire.lean) is what the compiler (Compile/) needs beside `BatchProtocol` in order to write down the
compiled batch verifier as a term; the prover's wire record is in Iop/BatchWireP.lean. A challenge
sampler (Iop/Draw.lean) says how a challenge is computed from hash blocks of λ bits.
After the pull-back (Iop/BatchPull.lean) the challenge of a round is its tuple of hash blocks, and
the round takes the first b of the K hash blocks of a random oracle's answer. So nothing in the
verifier's wire record depends on the sampler but the number of hash blocks of each round. The data
that do not depend on the sampler (positions, depths of trees, coins, decision procedures) are
`BatchProtocol.Aux` (Iop/BatchWireOf.lean) and `OpenNums` (Iop/WireOf.lean).
  `BatchProtocol.Draws`, `BatchProtocol.draws`            the samplers (`BS`, Iop/Draw.lean) of Test, Link and Batch;
      the record of protocols pulled back along them.
  `QueryLayout.ofDraws`, `WireBP.ofDraws`   the verifier's and the prover's wire record.
  `Spec.wireBDOK`                     they meet the conditions on wire records, if the verifiers
      open no more positions than announced and the number of slots is 2^depthReq.
  `Spec.drawsPropsB`                  under the hypotheses of its statement, the record of protocols
      keeps its properties, with the samplers' bias in the numbers.

Notation: slot: one of the places of a batch (lean/GLOSSARY.md); components: the shared part m_0 and
a slot's part m_j of a prover message (`RAnn`, Iop/Batch.lean); `own : r.Pos → Bool` (a field of
`RAnn`): does this oracle position lie in m_j (true) or in m_0 (false); `card0`, `cardJ`: natural
numbers (Iop/BatchWireOf.lean): the number of positions of the shared component m_0 of a round, of a
slot's component m_j; `has0`, `hasJ : Bool` (fields of `WireRB`, Iop/BatchWire.lean): is there a
tree over the shared component at all; the same for a slot's component; the pull-back (`InteractiveOracleProof.pull`,
Iop/Pull.lean): of a round (`Round.pull`), the same round with an element of the sampler's source
Src as challenge.
-/
import Iop.BatchWireOf
import Iop.Draw

namespace Iop
open Prob

/-! ## 1. The verifier's wire record -/

/-- One round of Batch: a position is at the leaf of its number, in the tree of its component. -/
def WireRB.ofDraw (lam K : ℕ) (r : Round) (a : RAnn r) (pt : r.IsPoint) (bs : BS lam r.Chal)
    (n0 : {p : r.Pos // a.own p = false} ≃ Fin (a.card0 pt))
    (nJ : {p : r.Pos // a.own p = true} ≃ Fin (a.cardJ pt)) :
    WireRB lam K (r.pull (bs.sampler)) (a.pull (bs.sampler)) where
  pt := { finPos := pt.finPos, decPos := pt.decPos, ofSyms := pt.ofSyms, rd_ofSyms := pt.rd_ofSyms,
          ofSyms_rd := pt.ofSyms_rd, zero := pt.zero }
  depth0 := Nat.clog 2 (a.card0 pt)
  depthJ := Nat.clog 2 (a.cardJ pt)
  has0 := decide (0 < a.card0 pt)
  hasJ := decide (0 < a.cardJ pt)
  place := fun p =>
    if h : a.own p = true then (nJ ⟨p, h⟩).val else (n0 ⟨p, Bool.eq_false_of_not_eq_true h⟩).val
  posAt0 := fun j => if h : j < a.card0 pt then some (n0.symm ⟨j, h⟩).1 else none
  posAtJ := fun j => if h : j < a.cardJ pt then some (nJ.symm ⟨j, h⟩).1 else none
  chal := firstBlocks lam K (bs.b)

def RoundsQueryLayout.ofDraws (lam K : ℕ) :
    (s : Shape) → (A : RoundSplits s) → (pts : s.IsPoint) → (ds : s.Draws lam) → s.NumPosB A pts →
    RoundsQueryLayout lam K (s.pull (Samplers.ofDraws s ds)) (A.pull (Samplers.ofDraws s ds))
  | [], _, _, _, _ => ()
  | r :: s, (a, A), (pt, pts), (bs, ds), (n0, nJ, nps) =>
    (WireRB.ofDraw lam K r a pt bs n0 nJ, RoundsQueryLayout.ofDraws lam K s A pts ds nps)

/-- A round of an ordinary IOP (Test, Link), taken as a local round: all positions are in one tree,
that of the slot's component; the other tree is empty. -/
def WireRB.ofLocalD (lam K : ℕ) (r : Round) (pt : r.IsPoint) (bs : BS lam r.Chal)
    (np : r.Pos ≃ Fin (@Fintype.card r.Pos pt.finPos)) :
    WireRB lam K (r.pull (bs.sampler)) (RAnn.allLocal (r.pull (bs.sampler))) :=
  letI := pt.finPos
  { pt :=
    { finPos := pt.finPos, decPos := pt.decPos, ofSyms := pt.ofSyms, rd_ofSyms := pt.rd_ofSyms,
      ofSyms_rd := pt.ofSyms_rd, zero := pt.zero }
    depth0 := 0
    depthJ := Nat.clog 2 (Fintype.card r.Pos)
    has0 := false
    hasJ := decide (0 < Fintype.card r.Pos)
    place := fun p => (np p).val
    posAt0 := fun _ => none
    posAtJ := fun j => if h : j < Fintype.card r.Pos then some (np.symm ⟨j, h⟩) else none
    chal := firstBlocks lam K (bs.b) }

def RoundsQueryLayout.ofLocalD (lam K : ℕ) :
    (s : Shape) → (pts : s.IsPoint) → (ds : s.Draws lam) → s.NumPos pts →
    RoundsQueryLayout lam K (s.pull (Samplers.ofDraws s ds)) (RoundSplits.allLocal (s.pull (Samplers.ofDraws s ds)))
  | [], _, _, _ => ()
  | r :: s, (pt, pts), (bs, ds), (np, nps) =>
    (WireRB.ofLocalD lam K r pt bs np, RoundsQueryLayout.ofLocalD lam K s pts ds nps)

variable {X : Type} {E : ExtSpec}

def ProtocolQueryLayout.ofDraws (lam K : ℕ) (Q : BatchInteractiveOracleProof X E) (pt : Q.loc.shape.IsPoint)
    (ds : Q.loc.shape.Draws lam) (nps : Q.loc.shape.NumPosB Q.ann pt) (we : WireE E) (nOpen d : ℕ) :
    ProtocolQueryLayout lam K (Q.pull (Samplers.ofDraws _ ds)) where
  sh := RoundsQueryLayout.ofDraws lam K Q.loc.shape Q.ann pt ds nps
  ext := we
  decO := letI := pt.decEqOPos; (OPos.pushEquiv (Samplers.ofDraws _ ds)).decidableEq
  nOpen := nOpen
  maxDepth := max d (RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofDraws lam K Q.loc.shape Q.ann pt ds nps))

def ProtocolQueryLayout.ofLocalD (lam K : ℕ) (Q : InteractiveOracleProof X E) (pt : Q.shape.IsPoint) (ds : Q.shape.Draws lam)
    (nps : Q.shape.NumPos pt) (we : WireE E) (nOpen d : ℕ) :
    ProtocolQueryLayout lam K (BatchInteractiveOracleProof.ofProto (Q.pull (Samplers.ofDraws _ ds))) where
  sh := RoundsQueryLayout.ofLocalD lam K Q.shape pt ds nps
  ext := we
  decO := letI := pt.decEqOPos; (OPos.pushEquiv (Samplers.ofDraws _ ds)).decidableEq
  nOpen := nOpen
  maxDepth := max d (RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofLocalD lam K Q.shape pt ds nps))

variable {I : Type}

/-- The challenge samplers of the three protocols. -/
structure BatchProtocol.Draws (L : BatchProtocol I X) (lam : ℕ) where
  T  : L.offline.shape.Draws lam
  Lk : L.link.shape.Draws lam
  B  : L.onlineBatch.loc.shape.Draws lam

/-- the largest number of hash blocks of a round -/
def BatchProtocol.Draws.K {L : BatchProtocol I X} {lam : ℕ} (dr : L.Draws lam) : ℕ :=
  max (Shape.Draws.maxB _ dr.T) (max (Shape.Draws.maxB _ dr.Lk) (Shape.Draws.maxB _ dr.B))

/-- a bound on the hash blocks of all rounds of one protocol -/
def BatchProtocol.Draws.TotLe {L : BatchProtocol I X} {lam : ℕ} (dr : L.Draws lam) (n : ℕ) : Prop :=
  Shape.Draws.totB _ dr.T ≤ n ∧ Shape.Draws.totB _ dr.Lk ≤ n ∧ Shape.Draws.totB _ dr.B ≤ n

/-- the sampler of every round of the three protocols satisfies `BS.Good`, with κ₀^b for b blocks -/
def BatchProtocol.Draws.Good {L : BatchProtocol I X} {lam : ℕ} (dr : L.Draws lam) (κ₀ : ENNReal) : Prop :=
  Shape.Draws.Good κ₀ _ dr.T ∧ Shape.Draws.Good κ₀ _ dr.Lk ∧ Shape.Draws.Good κ₀ _ dr.B

/-- The record of protocols with all challenges derived from hash blocks by the given samplers. -/
def BatchProtocol.draws (L : BatchProtocol I X) {lam : ℕ} (dr : L.Draws lam) : BatchProtocol I X :=
  L.pull (Samplers.ofDraws _ dr.T) (Samplers.ofDraws _ dr.Lk) (Samplers.ofDraws _ dr.B)

/-- The generic wire record of the verifier. -/
def QueryLayout.ofDraws (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
    (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums)
    (dr : L.Draws lam) (ax : L.Aux pT pL pB) : QueryLayout lam (L.draws dr) where
  K := dr.K
  T :=
    ProtocolQueryLayout.ofLocalD lam (dr.K) L.offline pT dr.T ax.posT (WireE.one L.wordLength L.Symbol z) no.T (Nat.clog 2 L.wordLength)
  Lk :=
    ProtocolQueryLayout.ofLocalD lam (dr.K) L.link pL dr.Lk ax.posL (WireE.two L.wordLength L.Symbol z) no.L (Nat.clog 2 L.wordLength)
  B := ProtocolQueryLayout.ofDraws lam (dr.K) L.onlineBatch pB dr.B ax.posB (WireE.one L.wordLength L.Symbol z) no.O (Nat.clog 2 L.wordLength)
  depth := Nat.clog 2 L.wordLength
  depthReq := ax.depthReq

/-! ## 2. The prover's wire record -/

def WirePB.ofLocalD (lam : ℕ) (Q : InteractiveOracleProof X E) {Wt : Type} (H : Honest Q Wt) (ds : Q.shape.Draws lam)
    (nc : H.Coin ≃ Fin (Fintype.card H.Coin)) (dW : ∀ w x ρ, Decidable (ρ ∈ H.withheld w x)) :
    WirePB (BatchInteractiveOracleProof.ofProto (Q.pull (Samplers.ofDraws _ ds)))
      (BatchHonestProver.ofHonest (H.pull (Samplers.ofDraws _ ds))) where
  coin0 := ⟨0, fun _ => ()⟩
  coin := Enum.ofNum H.Coin nc
  decW := fun w x ρ =>
    @decidable_of_iff _ _
      (Set.ext_iff.1 (BatchOne.ofHonest_withheld (H.pull (Samplers.ofDraws _ ds)) w x) ρ).symm
      (dW w x (Rho.push (Samplers.ofDraws _ ds) ρ))

def WirePB.ofDraws (lam : ℕ) (Q : BatchInteractiveOracleProof X E) {Wt : Type} (H : BatchHonestProver Q Wt)
    (ds : Q.loc.shape.Draws lam) (n0 : H.Coin0 ≃ Fin (Fintype.card H.Coin0))
    (nc : H.Coin ≃ Fin (Fintype.card H.Coin)) (dW : ∀ w x ρ, Decidable (ρ ∈ H.Bad ∪ H.Hid w x)) :
    WirePB (Q.pull (Samplers.ofDraws _ ds)) (H.pull (Samplers.ofDraws _ ds)) where
  coin0 := Enum.ofNum H.Coin0 n0
  coin := Enum.ofNum H.Coin nc
  decW := fun w x ρ =>
    @decidable_of_iff _
      (RhoLo.push (Samplers.ofDraws _ ds) (Rho.lo _ ρ) ∈ H.Bad ∪ H.Hid w x ∨
        H.stop0 (RhoSh.push (Samplers.ofDraws _ ds) (Rho.sh _ ρ)) = true)
      or_right_comm
      (@instDecidableOr _ _ (dW w x (RhoLo.push (Samplers.ofDraws _ ds) (Rho.lo _ ρ)))
        (instDecidableEqBool _ true))

/-- The generic wire record of the prover. -/
def WireBP.ofDraws (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint) (pL : L.link.shape.IsPoint)
    (pB : L.onlineBatch.loc.shape.IsPoint) (dr : L.Draws lam) (ax : L.Aux pT pL pB) :
    WireBP (L.draws dr) where
  T := WirePB.ofLocalD lam L.offline L.honestOfflineProver dr.T ax.numT ax.decT
  Lk := WirePB.ofLocalD lam L.link L.honestLinkProver dr.Lk ax.numL ax.decL
  B := WirePB.ofDraws lam L.onlineBatch L.honestOnlineBatchProver dr.B ax.numB0 ax.numB ax.decB
  ri := Enum.ofNum L.EncodingRandomness ax.numRI
  perm := Enum.ofNum (Equiv.Perm (Fin L.maxBatchSize)) (Num.ofFinEnum _)

namespace Spec

/-- The two wire records meet their conditions, whatever the samplers are, if the verifiers open no
more positions than announced and the number of slots is 2^depthReq. -/
def wireBDOK : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
      (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums)
      (dr : L.Draws lam) (ax : L.Aux pT pL pB),
    L.Opens no → L.maxBatchSize = 2 ^ ax.depthReq →
    (QueryLayout.ofDraws lam L pT pL pB z no dr ax).OK ∧ (WireBP.ofDraws lam L pT pL pB dr ax).OK

/-- All properties `BatchProtocol.Props` are preserved if the samplers satisfy `BatchProtocol.Draws.Good` with κ₀ ≥ 1:
round errors grow by κ₀^(largest number of hash blocks of a round), the probabilities of the abort
sets and the errors of simulation by κ₀^n, n a bound on the hash blocks of all rounds of a protocol;
Batch's error of simulation, which is for sets of slots, by (κ₀^n)^maxBatchSize. -/
def drawsPropsB : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Prop) (M : LH.Nums) (lam n : ℕ)
      (dr : L.Draws lam) (κ₀ : ENNReal),
    1 ≤ κ₀ → dr.Good κ₀ → dr.TotLe n → L.Props Ryes Rno M →
    (L.draws dr).Props Ryes Rno (M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize)

end Spec


end Iop
