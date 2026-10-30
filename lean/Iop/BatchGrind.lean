-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchGrind.lean: proof-of-work bits ("grinding") for protocols with slots and for `BatchProtocol`.

The file has definitions and statements; the proofs are in Iop/BatchGrindProofs.lean. The header of
Iop/Grind.lean says what the construction is, where it comes from, and what "128 bits" means after
it. A protocol with slots is the verifier of one slot with an annotation of its rounds; an `BatchProtocol`
holds an encoder, a decoder and the protocols Test, Link and Batch (Iop/Batch.lean). So the
transformer is that of Iop/Grind.lean on the slot's verifier, along a list g of numbers of
proof-of-work bits, for any type W of nonces with a fixed element, and what is new is which
component of a prover message holds the nonce. It is the component in the Fiat-Shamir query whose
answer is the round's challenge: the slot's component in a local round, the shared component in a
shared round. A shared round has one vector of proof-of-work bits and one nonce for all slots, so an
attempt costs one query, and no slot's message or tree is made again.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

  `BatchProtocol.grind`          the record of protocols with proof-of-work bits in Test, Link and Batch.
  `sndB_grind`, `sndBL_grind`   (Iop/BatchGrindProofs.lean) round-by-round soundness of a protocol
      with slots, (Snd-B), and its late form are preserved with the same error counts, in local and
      in shared rounds, with no hypothesis on g, N or ε. The new state is the old state of the
      stripped transcript, and all proof-of-work bits so far are 0: Theorem 6's state function, in
      the form for all rounds (whose Theorem 6: the header of Iop/Grind.lean). For after a failed
      test, that is a proof-of-work bit that is 1, the old state may be 1: only the conjunction over
      all earlier rounds keeps 0 at 0.
  `Spec.grindSoundB`   if L is sound with explicit error lists e (`BatchProtocol.SoundAt`, Iop/SoundAt.lean)
      and e_i ≤ εs' · 2^b_i · |C_i| in every round, then `BatchProtocol.Sound` of `L.grind` holds with the
      bound εs'.
  `Spec.grindPropsB`   all clauses of `BatchProtocol.Props` but completeness, (Acc), are preserved with the
      same numbers, for every g (`BatchProtocol.PropsNoAcc`); soundness is a hypothesis.

Limits:
* Completeness is not preserved. As in Iop/Grind.lean nothing of the honest prover looks at the
  proof-of-work bits, and a bit that is 1 does not put the randomness into the abort set; this holds
  in shared rounds too, where `BatchHonestProver.stop0` (Iop/Batch.lean, (D7)) is the old check. So
  `BatchProtocol.Props` of `L.grind` is false, whatever the numbers, as soon as in one of the three protocols
  a round has a proof-of-work bit and some verifier randomness of some valid input is outside the
  abort set (this is not proved). A theorem of the compiler that assumes `BatchProtocol.Props` cannot be
  applied to `L.grind`: each clause has to be taken by itself.
* What Iop/Grind.lean does not say, this file does not say either. Above all: the clause on hiding
  (`Spec.grindSimB`) is about nonces given in advance, the same in all slots: `DView.fillJ` and
  `simGrindB` take nonces slot by slot, but no statement here uses different nonces in different
  slots. The implementation's public stop after a failed search is not modelled.
* Nothing is said on what happens to a batch whose shared proof-of-work check never succeeds.
* It is not stated that the pattern of local and shared rounds, (Sh) (`RoundSplits.OneBlock`), which no
  proof of the compiler uses, is preserved.

(Words of this library: lean/GLOSSARY.md.)
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Iop.Grind
import Iop.BatchPull
import Iop.BatchFmt
import Iop.SoundAt
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Which component holds the nonce -/

/-- The number of proof-of-work bits that counts for the shared component of a prover message: b in
a shared round, 0 in a local one. -/
def Kind.b0 (k : Kind) : ℕ → ℕ
  | 0 => 0
  | b + 1 => match k with
    | .sh => b + 1
    | .lo => 0

/-- The number of proof-of-work bits that counts for the slot's component: b in a local round, 0 in
a shared one. -/
def Kind.bJ (k : Kind) : ℕ → ℕ
  | 0 => 0
  | b + 1 => match k with
    | .sh => 0
    | .lo => b + 1

namespace GPlain
variable {W : Type}

/-- a bijection on the old plain parts, carried to those with a nonce -/
def congr {P P' : Type} (e : P ≃ P') : (b : ℕ) → GPlain W b P ≃ GPlain W b P'
  | 0 => e
  | _ + 1 => Equiv.prodCongr e (Equiv.refl (W))

/-- the nonce goes with the second coordinate -/
def prodR (A B : Type) : (b : ℕ) → GPlain W b (A × B) ≃ A × GPlain W b B
  | 0 => Equiv.refl (A × B)
  | _ + 1 => Equiv.prodAssoc A B (W)

/-- A pair with a nonce is a pair of components, one of which has the nonce: the first in a shared
round, the second in a local one. -/
def comps (A B : Type) (k : Kind) :
    (b : ℕ) → GPlain W b (A × B) ≃ GPlain W (k.b0 b) A × GPlain W (k.bJ b) B
  | 0 => Equiv.refl (A × B)
  | _ + 1 => match k with
    | .sh =>
      ⟨fun z : (A × B) × W => ((z.1.1, z.2), z.1.2),
        fun z : (A × W) × B => ((z.1.1, z.2), z.1.2),
        fun _ => rfl, fun _ => rfl⟩
    | .lo => Equiv.prodAssoc A B (W)

end GPlain

/-- The annotation of the round with b proof-of-work bits. -/
def RAnn.grind (W : Type) [Inhabited W] {r : Round} (a : RAnn r) (b : ℕ) : RAnn (r.grind W b) where
  kind := a.kind
  M0 := GPlain W (a.kind.b0 b) a.M0
  Mj := GPlain W (a.kind.bJ b) a.Mj
  split := (GPlain.prodR r.Orc r.Plain b).symm.trans
    ((GPlain.congr a.split b).trans (GPlain.comps a.M0 a.Mj a.kind b))
  P0 := GPlain W (a.kind.b0 b) a.P0
  Pj := GPlain W (a.kind.bJ b) a.Pj
  pl0 := GPlain.map a.pl0
  plj := GPlain.map a.plj
  plain := (GPlain.congr a.plain b).trans (GPlain.comps a.P0 a.Pj a.kind b)
  own := a.own

variable {W : Type} [Inhabited W]

/-- At b = 0 the annotation is the annotation itself, by definition. -/
theorem RAnn.grind_zero {r : Round} (a : RAnn r) : a.grind W 0 = a := rfl

/-- The annotation of the new list of rounds. -/
def RoundSplits.grind (W : Type) [Inhabited W] : {s : Shape} → RoundSplits s → (g : GBits s) → RoundSplits (s.grind W g)
  | [], _, _ => PUnit.unit
  | _ :: _, (a, A), (b, g) => (a.grind W b, RoundSplits.grind W A g)

/-! ## 2. Verifier randomness -/


/-- The stripped verifier randomness of the whole batch: the proof-of-work bits are dropped. -/
def BRho.strip {N : ℕ} :
    {s : Shape} → (g : GBits s) → {A : RoundSplits s} → BRho N (s.grind W g) (A.grind W g) → BRho N s A
  | [], _, _, _ => ()
  | _ :: _, (_, g), (a, _), (v, ρ) => (a.kind.mapAll GChal.old v, BRho.strip g ρ)

/-- The stripped local challenges of a slot. -/
def RhoLo.strip :
    {s : Shape} → (g : GBits s) → {A : RoundSplits s} → RhoLo (s.grind W g) (A.grind W g) → RhoLo s A
  | [], _, _, _ => ()
  | _ :: _, (_, g), (a, _), (c, ρ) => (a.kind.mapLo GChal.old c, RhoLo.strip g ρ)

/-- The stripped shared challenges. -/
def RhoSh.strip :
    {s : Shape} → (g : GBits s) → {A : RoundSplits s} → RhoSh (s.grind W g) (A.grind W g) → RhoSh s A
  | [], _, _, _ => ()
  | _ :: _, (_, g), (a, _), (c, ρ) => (a.kind.mapSh GChal.old c, RhoSh.strip g ρ)


/-! ## 3. Protocols and honest provers -/

/-- The honest shared component: it sends the nonces of the shared rounds, and still sees the shared
challenges only. It does not look at the proof-of-work bits. -/
def SStrat.grind :
    {s : Shape} → (g : GBits s) → {A : RoundSplits s} → SStrat s A →
    GNon W s → SStrat (s.grind W g) (A.grind W g)
  | [], _, _, _, _ => ()
  | _ :: _, (b, g), (a, _), (m0, k), (ν, νs) =>
    (GPlain.mk (a.kind.b0 b) m0 ν, fun c => SStrat.grind g (k (a.kind.mapSh GChal.old c)) νs)

/-- The honest component of a slot: it sends the nonces of the local rounds. -/
def LStrat.grind :
    {s : Shape} → (g : GBits s) → {A : RoundSplits s} → LStrat s A →
    GNon W s → LStrat (s.grind W g) (A.grind W g)
  | [], _, _, _, _ => ()
  | _ :: _, (b, g), (a, _), (mj, k), (ν, νs) =>
    (GPlain.mk (a.kind.bJ b) mj ν, fun c => LStrat.grind g (k (GChal.old c)) νs)

variable {X : Type} {E : ExtSpec}

/-- The protocol with slots, with proof-of-work bits. -/
def BatchInteractiveOracleProof.grind (W : Type) [Inhabited W] (Q : BatchInteractiveOracleProof X E) (g : GBits Q.loc.shape) :
    BatchInteractiveOracleProof X E :=
  ⟨Q.loc.grind W g, Q.ann.grind W g⟩

/-- The honest prover: the same coins and the same external string; the nonces are ν, given in
advance, the same in all slots. A value of a slot's local challenges is in the abort set if its
stripped value is. A proof-of-work bit that is 1 does not put it there. -/
def BatchHonestProver.grind {Q : BatchInteractiveOracleProof X E} {Wt : Type} (H : BatchHonestProver Q Wt)
    (g : GBits Q.loc.shape) (ν : GNon W Q.loc.shape) : BatchHonestProver (Q.grind W g) Wt where
  Coin0 := H.Coin0
  Coin := H.Coin
  ext := H.ext
  strat0 := fun w c0 => SStrat.grind g (H.strat0 w c0) ν
  strat := fun w c0 x c => LStrat.grind g (H.strat w c0 x c) ν
  Bad := {ρ | RhoLo.strip g ρ ∈ H.Bad}
  Hid := fun w x => {ρ | RhoLo.strip g ρ ∈ H.Hid w x}
  stop0 := fun ρ => H.stop0 (RhoSh.strip g ρ)

/-- The record of protocols: encoder, decoder, the number of slots and the fields `early` and `late`
do not change (the rounds keep their numbers). The honest provers of the interactive protocols send
the fixed nonce. -/
def BatchProtocol.grind (W : Type) [Inhabited W] {I X : Type} (L : BatchProtocol I X) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) : BatchProtocol I X where
  wordLength := L.wordLength
  Symbol := L.Symbol
  EncodingRandomness := L.EncodingRandomness
  encodeIndex := L.encodeIndex
  decodeIndex := L.decodeIndex
  offline := L.offline.grind W gT
  link := L.link.grind W gL
  maxBatchSize := L.maxBatchSize
  onlineBatch := L.onlineBatch.grind W gB
  honestOfflineProver := L.honestOfflineProver.grind gT (GNon.nil W _)
  honestLinkProver := L.honestLinkProver.grind gL (GNon.nil W _)
  honestOnlineBatchProver := L.honestOnlineBatchProver.grind gB (GNon.nil W _)
  early := L.early
  late := L.late

/-- The output for a set of slots, with nonces put in: slot j gets the nonces ν j. -/
def DView.fillJ {Q : InteractiveOracleProof X E} (g : GBits Q.shape) {N : ℕ} {J : Finset (Fin N)}
    (ν : J → GNon W Q.shape) (v : J → Option (DView Q)) :
    J → Option (DView (Q.grind W g)) :=
  fun j => (v j).map (DView.fill g (ν j))

/-- The simulator for sets of slots: the old simulator at the stripped randomness, then
`DView.fillJ`. It does not look at the proof-of-work bits. -/
def simGrindB {Q : BatchInteractiveOracleProof X E} (g : GBits Q.loc.shape) {N : ℕ}
    (ν : (J : Finset (Fin N)) → J → GNon W Q.loc.shape)
    (Sim : (J : Finset (Fin N)) → (J → X) → (J → Rho Q.loc.shape) →
      (E.Pos → Option E.Sym) → PMF (J → Option (DView Q.loc))) :
    (J : Finset (Fin N)) → (J → X) → (J → Rho (Q.grind W g).loc.shape) → (E.Pos → Option E.Sym) →
    PMF (J → Option (DView (Q.grind W g).loc)) :=
  fun J xs ρs a => (Sim J xs (fun j => Rho.strip g (ρs j)) a).map (DView.fillJ g (ν J))

/-- All properties of a record of protocols but completeness, (Acc): the clauses of `BatchProtocol.Props`,
with those of `BatchProtocol.Complete` written out, without `accT`, `accL`, `accB`. -/
structure BatchProtocol.PropsNoAcc {I X : Type} (L : BatchProtocol I X) (Ryes Rno : I → X → Prop) (M : LH.Nums) :
    Prop where
  sub      : ∀ i x, Ryes i x → Rno i x
  wired    : L.Wired
  sound    : L.Sound Rno M.εs
  reads    : L.Reads M.b M.qT M.qpar M.qch M.qon
  hidden   : L.Hiding Ryes M.zT M.zL M.zO
  prT      : ∀ w x, prRho (L.honestOfflineProver.withheld w x) ≤ M.pT
  prL      : ∀ w x, prRho (L.honestLinkProver.withheld w x) ≤ M.pL
  prB      : ∀ w x, Ryes w.1 x → prRho (L.honestOnlineBatchProver.one.withheld w x) ≤ M.pO
  localT   : L.offline.IsLocal
  localL   : L.link.IsLocal
  localB   : L.onlineBatch.loc.IsLocal
  cohB     : L.onlineBatch.ann.Coherent
  pointT   : Nonempty L.offline.shape.IsPoint
  pointL   : Nonempty L.link.shape.IsPoint
  pointB   : Nonempty L.onlineBatch.loc.shape.IsPoint

/-! ## 4. The statements -/

namespace Spec



/-- `BatchProtocol.Sound` of `L.grind` at the bound εs', if L is sound with explicit lists e (`BatchProtocol.SoundAt`)
and in every round e_i ≤ εs' * (2^b_i * card C_i). -/
def grindSoundB : Prop :=
  ∀ (W : Type) [Inhabited W] (I X : Type) (L : BatchProtocol I X) (Rno : I → X → Prop)
      (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs' : ℝ≥0∞),
    L.SoundAt Rno εT εL εB → Err.BelowG gT εT εs' → Err.BelowG gL εL εs' →
    Err.BelowG gB εB εs' → (L.grind W gT gL gB).Sound Rno εs'



/-- The simulator is exact wherever the old one is exact at the stripped randomness, whatever the
proof-of-work bits are. (`simGrindB g (fun _ _ => ν) Sim`; Limits: the head.) -/
def grindSimB : Prop :=
  ∀ (W : Type) [Inhabited W] (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (Wt : Type)
      (H : BatchHonestProver Q Wt) (g : GBits Q.loc.shape) (ν : GNon W Q.loc.shape) (N : ℕ)
      (Sim : (J : Finset (Fin N)) → (J → X) → (J → Rho Q.loc.shape) →
        (E.Pos → Option E.Sym) → PMF (J → Option (DView Q.loc)))
      (w : Wt) (x : Fin N → Option X) (ρ : BRho N (Q.loc.shape.grind W g) (Q.ann.grind W g))
      (J : Finset (Fin N)) (xs : J → X),
    H.output w x (BRho.strip g ρ) J =
      Sim J xs (fun j => (BRho.strip g ρ).slot j.1)
        (Q.extAnsJ J xs (fun j => (BRho.strip g ρ).slot j.1) (H.ext w)) →
    (H.grind g ν).output w x ρ J =
      simGrindB g (fun _ _ => ν) Sim J xs (fun j => ρ.slot j.1)
        ((Q.grind W g).extAnsJ J xs (fun j => ρ.slot j.1) ((H.grind g ν).ext w))

/-- If the new verifier randomness of the batch is uniform, the stripped randomness is uniform. -/
def grindUnifB : Prop :=
  ∀ (W : Type) [Inhabited W] (N : ℕ) (s : Shape) (A : RoundSplits s) (g : GBits s) (S : Set (BRho N s A)),
    prBRho {ρ : BRho N (s.grind W g) (A.grind W g) | BRho.strip g ρ ∈ S} = prBRho S

/-- All clauses of `BatchProtocol.Props` but completeness, (Acc), are preserved with the same numbers, for
every g. Soundness at the bound εs' is a hypothesis (`Spec.grindSoundB` gives it). The numbers p and
z are probabilities under uniform challenges, proof-of-work bits included; the sets that they
measure do not depend on these bits. -/
def grindPropsB : Prop :=
  ∀ (W : Type) [Inhabited W] (I X : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Prop) (M : LH.Nums)
      (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (εs' : ℝ≥0∞),
    L.Props Ryes Rno M → (L.grind W gT gL gB).Sound Rno εs' →
    (L.grind W gT gL gB).PropsNoAcc Ryes Rno { M with εs := εs' }

end Spec

end Iop
