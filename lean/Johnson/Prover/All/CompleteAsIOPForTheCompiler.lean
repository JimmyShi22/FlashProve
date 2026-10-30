-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/All/CompleteAsIOPForTheCompiler.lean: what the compiler's theorem on completeness
takes from completeness as an IOP (Johnson/Face/CompleteAsIOP.lean). It states no goal.

  FailsRarelyAtEveryCoin, CompleteAtEveryCoin   a stronger form, at every coin of the prover, which
    the compiler's proof spends, since complete_argW bounds at each listed coin. It is no part of
    what «complete as an IOP» means.


  EveryCoinGivesFailsRarely   states that the stronger form gives the definition's.
  workOfWire, partsWorkOfWire   the work bits as the rounds' wires declare them. Of a wire only its
    tests are read: which bits of a challenge are work bits, and where a nonce is written.
  rejectingFalls   the sets at which acceptance is not owed: the failures themselves.
  PartsGiveCompilerPremise   at every coin, the parts give AccLaws, the premise of complete_argW,
    with no seed set aside.
-/
import Johnson.Face.CompleteAsIOP
import Johnson.WholeKey.CompleteOfRecs

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.Compilation (CompleteInParts HonestProvers)

/-- At every coin of the prover the run fails with chance at most error, over the challenges that
pass. -/
def FailsRarelyAtEveryCoin {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type} (H : Honest Q Wt)
    (work : WorkBits Q.shape) (y : E.Str) (w : Wt) (x : Y) (error : ℝ≥0∞) : Prop :=
  ∀ c : H.Coin, chanceAtPassing work (FailsAt H work y w x c) ≤ error

/-- States that a bound at every coin is a bound over coins and challenges together. -/
def EveryCoinGivesFailsRarely : Prop :=
  ∀ {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type} (H : Honest Q Wt)
    (work : WorkBits Q.shape) (y : E.Str) (w : Wt) (x : Y) (error : ℝ≥0∞),
    FailsRarelyAtEveryCoin H work y w x error → FailsRarely H work y w x error

variable {Index Request : Type}

/-- The same three provers, in the type that the compiler's theorems take. -/
def toRecs {L : HolographicProtocol Index Request} (prover : HonestProvers L) : ThreeProvers L :=
  ⟨prover.offlineProver, prover.linkProver, prover.onlineProver⟩

/-- The three provers of the compiler's type, as HonestProvers. -/
def ofRecs {L : HolographicProtocol Index Request} (prover : ThreeProvers L) : HonestProvers L :=
  ⟨prover.T, prover.Lk, prover.B⟩

/-- The three accepted clauses of CompleteInParts at every coin. -/
structure CompleteAtEveryCoin (L : HolographicProtocol Index Request) (prover : HonestProvers L) (work : PartsWork L)
    (Relation : Index → Request → Prop) (offlineError linkError onlineError : ℝ≥0∞) : Prop where
  offline : ∀ i x r e, Relation i x →
    FailsRarelyAtEveryCoin prover.offlineProver work.offline (L.encodeIndex i r) (i, r, e) (L.recOf i r e) offlineError
  link : ∀ i x r e r' e', Relation i x →
    FailsRarelyAtEveryCoin prover.linkProver work.link (L.encodeIndex i r, L.encodeIndex i r') (i, (r, e), (r', e'))
      (L.recOf i r e, L.recOf i r' e') linkError
  online : ∀ i x r e n, Relation i x →
    FailsRarelyAtEveryCoin prover.onlineProver work.online (L.encodeIndex i r) (i, r, e, n) (x, L.recOf i r e)
      onlineError

/-- The work bits as the rounds' wires declare them. -/
def workOfWire {lam K : ℕ} {s : Shape} (A : RoundSplits s) (wire : RoundsQueryLayout lam K s A) : WorkBits s where
  passes := RoundsQueryLayout.pass s A wire
  cleared := RoundsQueryLayout.zero s A wire
  sameButForNonces := Puts s A wire

/-- The same for the three parts. -/
def partsWorkOfWire {lam : ℕ} {L : HolographicProtocol Index Request} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) : PartsWork L where
  offline := workOfWire aT (wTC W).sh
  link := workOfWire aL (wLC W).sh
  online := workOfWire L.onlineBatch.ann (wBC W).sh

/-- The sets at which acceptance is not owed, read off the verifier: the challenges at which the run
fails. -/
def rejectingFalls {L : HolographicProtocol Index Request} (prover : HonestProvers L) (work : PartsWork L) :
    Falls (toRecs prover) where
  T := fun w x c => {ρ | FailsAt prover.offlineProver work.offline (L.encodeIndex w.1 w.2.1) w x c ρ}
  Lk := fun w x c =>
    {ρ | FailsAt prover.linkProver work.link (L.encodeIndex w.1 w.2.1.1, L.encodeIndex w.1 w.2.2.1) w x c ρ}
  B := fun w x c => {ρ | FailsAt prover.onlineProver work.online (L.encodeIndex w.1 w.2.1) w x c ρ}

/-- States that the parts, at every coin, give AccLaws at the wires' work bits. -/
def PartsGiveCompilerPremise : Prop :=
  ∀ {Index Request : Type} {lam : ℕ} {L : HolographicProtocol Index Request} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (prover : HonestProvers L) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (Relation : Index → Request → Prop)
    (offlineError linkError onlineError : ℝ≥0∞),
    CompleteInParts L prover (partsWorkOfWire (aT := aT) (aL := aL) W) S.num Relation
      offlineError linkError onlineError →
    CompleteAtEveryCoin L prover (partsWorkOfWire (aT := aT) (aL := aL) W) Relation
      offlineError linkError onlineError →
    AccLaws W S (toRecs prover).strats Relation
      (OnBytes.WholeKey.badsOf (lam := lam) (Bd := Bd) (aT := aT) (aL := aL) (toRecs prover)
        (rejectingFalls prover (partsWorkOfWire (aT := aT) (aL := aL) W)) fun _ _ => ∅)
      0 0 offlineError linkError onlineError

end OnBytes.Prover
