-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchPull.lean: protocols with slots whose challenges are computed from other uniform strings
(for the compiler: from tuples of hash blocks of λ bits). Definitions and a statement. (Words of
this library: lean/GLOSSARY.md.)

As Iop/Pull.lean for ordinary IOPs. A protocol with slots is an ordinary IOP (a slot's verifier)
with an annotation of its rounds. So it is pulled back by pulling back the slot's verifier along one
sampler for each round (`InteractiveOracleProof.pull`: the verifier sends a uniform element of the sampler's source
set, and everything else uses its image), and the annotation is carried over unchanged: kinds,
components of the prover messages, positions. A shared challenge is sampled once, for all slots: in
a shared round the batch samples one source string and all slots see its image; in a local round it
samples one source string for each slot (`Kind.mapAll`).

The numbers, as the statement at the end of this file has them (proved in Iop/BatchPullProofs.lean).
The bias of a sampler is multiplicative for each sample (Iop/Pull.lean: at most κ for a round, at
most K for all rounds of one slot's transcript).
  * Round-by-round errors, the joint errors of the shared rounds included, grow by at most the
    factor κ: a joint error, too, is about one sample.
  * The probability of a slot's abort set (`Honest.withheld`) is measured on one slot's transcript:
    at most the factor K.
  * HVZK for sets of slots (`BatchHonestProver.HVZK`) measures a set of whole ρ = (ρ_0, ρ_1, .., ρ_N), and a
    local round samples N strings: at most the factor K^N (`LH.Nums.pullB`).
-/
import Iop.Batch
import Iop.Univ
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Challenges -/

namespace Kind
variable {C D : Type} (f : C → D)

/-- The image of a challenge of the whole batch: of the one value of a shared round, of each value
of a local round. -/
def mapAll {N : ℕ} : (k : Kind) → k.All N C → k.All N D
  | sh, c => f c
  | lo, c => fun j => f (c j)

/-- the image of the shared part of a challenge -/
def mapSh : (k : Kind) → k.Sh C → k.Sh D
  | sh, c => f c
  | lo, _ => ()

/-- the image of its local part -/
def mapLo : (k : Kind) → k.Lo C → k.Lo D
  | sh, _ => ()
  | lo, c => f c

end Kind

/-! ## 2. Annotations -/

/-- The annotation of the pulled-back round: nothing changes but the set of challenges. -/
def RAnn.pull {r : Round} (a : RAnn r) (σ : Sampler r) : RAnn (r.pull σ) where
  kind := a.kind
  M0 := a.M0
  Mj := a.Mj
  split := a.split
  P0 := a.P0
  Pj := a.Pj
  pl0 := a.pl0
  plj := a.plj
  plain := a.plain
  own := a.own

def RoundSplits.pull : {s : Shape} → (σ : Samplers s) → RoundSplits s → RoundSplits (s.pull σ)
  | [], _, _ => PUnit.unit
  | _ :: _, (σ, σs), (a, A) => (a.pull σ, RoundSplits.pull σs A)

/-- The verifier randomness of the whole batch, from the source strings. -/
def BRho.push {N : ℕ} :
    {s : Shape} → (σ : Samplers s) → {A : RoundSplits s} → BRho N (s.pull σ) (A.pull σ) → BRho N s A
  | [], _, _, _ => ()
  | _ :: _, (σ, σs), (a, _), (v, ρ) => (a.kind.mapAll σ.φ v, BRho.push σs ρ)

def RhoLo.push :
    {s : Shape} → (σ : Samplers s) → {A : RoundSplits s} → RhoLo (s.pull σ) (A.pull σ) → RhoLo s A
  | [], _, _, _ => ()
  | _ :: _, (σ, σs), (a, _), (c, ρ) => (a.kind.mapLo σ.φ c, RhoLo.push σs ρ)

def RhoSh.push :
    {s : Shape} → (σ : Samplers s) → {A : RoundSplits s} → RhoSh (s.pull σ) (A.pull σ) → RhoSh s A
  | [], _, _, _ => ()
  | _ :: _, (σ, σs), (a, _), (c, ρ) => (a.kind.mapSh σ.φ c, RhoSh.push σs ρ)

/-! ## 3. Protocols and honest provers -/

/-- The honest shared strategy after the pull-back: it sees the images of the shared source strings,
and still nothing else. -/
def SStrat.pull :
    {s : Shape} → (σ : Samplers s) → {A : RoundSplits s} → SStrat s A → SStrat (s.pull σ) (A.pull σ)
  | [], _, _, _ => ()
  | _ :: _, (σ, σs), (a, _), (m0, k) => (m0, fun c => SStrat.pull σs (k (a.kind.mapSh σ.φ c)))

/-- The honest strategy of a slot after the pull-back. -/
def LStrat.pull :
    {s : Shape} → (σ : Samplers s) → {A : RoundSplits s} → LStrat s A → LStrat (s.pull σ) (A.pull σ)
  | [], _, _, _ => ()
  | _ :: _, (σ, σs), (_, _), (mj, k) => (mj, fun c => LStrat.pull σs (k (σ.φ c)))

variable {X : Type} {E : ExtSpec}

/-- The protocol with slots pulled back along the samplers. -/
def BatchInteractiveOracleProof.pull (Q : BatchInteractiveOracleProof X E) (σ : Samplers Q.loc.shape) : BatchInteractiveOracleProof X E :=
  ⟨Q.loc.pull σ, Q.ann.pull σ⟩

def BatchHonestProver.pull {Q : BatchInteractiveOracleProof X E} {Wt : Type} (H : BatchHonestProver Q Wt) (σ : Samplers Q.loc.shape) :
    BatchHonestProver (Q.pull σ) Wt where
  Coin0 := H.Coin0
  Coin := H.Coin
  ext := H.ext
  strat0 := fun w c0 => SStrat.pull σ (H.strat0 w c0)
  strat := fun w c0 x c => LStrat.pull σ (H.strat w c0 x c)
  Bad := {ρ | RhoLo.push σ ρ ∈ H.Bad}
  Hid := fun w x => {ρ | RhoLo.push σ ρ ∈ H.Hid w x}
  stop0 := fun ρ => H.stop0 (RhoSh.push σ ρ)

/-- The record pulled back: encoder, decoder and the number of slots do not change. (The record: an
`BatchProtocol`, Iop/Batch.lean, holds an encoder, a decoder and the protocols Test, Link and Batch.) -/
def BatchProtocol.pull {I X : Type} (L : BatchProtocol I X) (σT : Samplers L.offline.shape)
    (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape) : BatchProtocol I X where
  wordLength := L.wordLength
  Symbol := L.Symbol
  EncodingRandomness := L.EncodingRandomness
  encodeIndex := L.encodeIndex
  decodeIndex := L.decodeIndex
  offline := L.offline.pull σT
  link := L.link.pull σL
  maxBatchSize := L.maxBatchSize
  onlineBatch := L.onlineBatch.pull σB
  honestOfflineProver := L.honestOfflineProver.pull σT
  honestLinkProver := L.honestLinkProver.pull σL
  honestOnlineBatchProver := L.honestOnlineBatchProver.pull σB
  early := L.early
  late := L.late

/-- The numbers after the pull-back, for N slots. -/
def LH.Nums.pullB (M : LH.Nums) (κ K : ℝ≥0∞) (N : ℕ) : LH.Nums :=
  { M.pull κ K with zO := K ^ N * M.zO }

namespace Spec

/-- For good samplers, `BatchProtocol.Props` is preserved, with the numbers of `LH.Nums.pullB`. (Good:
`Samplers.Good κ K`, all three lists; `BatchProtocol.Props`, Iop/Batch.lean: all properties together; the
shape (Sh) and `ExtShared` are not among them.) -/
def pullPropsB : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Prop) (M : LH.Nums) (σT : Samplers L.offline.shape)
      (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape) (κ K : ℝ≥0∞),
    σT.Good κ K → σL.Good κ K → σB.Good κ K → L.Props Ryes Rno M →
    (L.pull σT σL σB).Props Ryes Rno (M.pullB κ K L.maxBatchSize)


end Spec

end Iop
