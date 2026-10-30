-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/CompleteCore.lean: the words in which completeness as an IOP is stated: work bits, a failed
run, and its chance. What they are for: Johnson/Face/CompleteAsIOP.lean, whose head says it in
ten lines. General definitions over the library's IOPs alone: no compiler lies beneath this file.
Definitions only: nothing is proved here.
-/
import Iop.InteractiveOracleProof
import Hiop.RecInterface

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace Iop
open Prob

/-- **Which part of a protocol's challenges is proof of work.** Public data; it reads no prover. -/
structure WorkBits (s : Shape) where
  /-- all work bits of these challenges are 0 -/
  passes : Rho s → Bool
  /-- these challenges with all work bits set to 0 -/
  cleared : Rho s → Rho s
  /-- the second transcript is the first with other nonces written in -/
  sameButForNonces : Tr s → Tr s → Prop

/-- A protocol without proof of work. At this value the definitions below are the textbook ones. -/
def WorkBits.none (s : Shape) : WorkBits s := ⟨fun _ => true, id, fun τ τ' => τ' = τ⟩

/-- The chance of an event over the challenges that pass: uniform challenges with the work bits set
to 0. -/
def chanceAtPassing {s : Shape} (work : WorkBits s) (event : Rho s → Prop) : ℝ≥0∞ :=
  prRho {ρ : Rho s | event (work.cleared ρ)}

/-- **What makes the work bits a protocol's own.** Public: it reads no prover. Above all
clearedIsConditioned: uniform challenges with the work bits set to 0 are uniform challenges
conditioned on passing. -/
structure WorkBitsFaithful {Y : Type} {E : ExtSpec} (Q : InteractiveOracleProof Y E) (work : WorkBits Q.shape) :
    Prop where
  /-- the verifier accepts no transcript whose work bits are not all 0 -/
  verifierAsksTheWork : ∀ (x : Y) (y : E.Str) (τ : Tr Q.shape),
    Q.accept x y τ = true → work.passes τ.rho = true
  clearedPasses : ∀ ρ : Rho Q.shape, work.passes (work.cleared ρ) = true
  passingStays : ∀ ρ : Rho Q.shape, work.passes ρ = true → work.cleared ρ = ρ
  clearedIsConditioned : ∀ S : Set (Rho Q.shape),
    prRho {ρ : Rho Q.shape | work.passes ρ = true} * prRho {ρ : Rho Q.shape | work.cleared ρ ∈ S} =
      prRho {ρ : Rho Q.shape | work.passes ρ = true ∧ ρ ∈ S}
  /-- a nonce is no challenge -/
  noncesKeepChallenges : ∀ τ τ' : Tr Q.shape, work.sameButForNonces τ τ' → τ'.rho = τ.rho
  /-- the nonces that a transcript has are among the choices -/
  ownNonces : ∀ τ : Tr Q.shape, work.sameButForNonces τ τ

variable {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type}

/-- **The honest run fails at these challenges**: the prover aborts there, or the verifier, reading
the oracle y, rejects its run there under some choice of nonces. w: the prover's private input.
x: the instance. c: its coin. -/
def FailsAt (H : Honest Q Wt) (work : WorkBits Q.shape) (y : E.Str) (w : Wt) (x : Y) (c : H.Coin)
    (ρ : Rho Q.shape) : Prop :=
  ρ ∈ H.withheld w x ∨
    ∃ τ : Tr Q.shape, work.sameButForNonces ((H.strat w x c).run ρ).1 τ ∧ Q.accept x y τ = false

/-- Over the prover's uniform coins and the challenges that pass, the run fails with chance at most
error. -/
def FailsRarely (H : Honest Q Wt) (work : WorkBits Q.shape) (y : E.Str) (w : Wt) (x : Y)
    (error : ℝ≥0∞) : Prop :=
  pr (unif (H.Coin × Rho Q.shape)) {d | FailsAt H work y w x d.1 (work.cleared d.2)} ≤ error

variable {Index Request : Type}

/-- The work bits of the three parts of a protocol. L.offline is the offline part, L.link the link,
L.onlineBatch.loc the online part. -/
structure PartsWork (L : HolographicProtocol Index Request) where
  offline : WorkBits L.offline.shape
  link : WorkBits L.link.shape
  online : WorkBits L.onlineBatch.loc.shape

/-- All three are the protocol's own. -/
structure PartsWork.Faithful {L : HolographicProtocol Index Request} (work : PartsWork L) : Prop where
  offline : WorkBitsFaithful L.offline work.offline
  link : WorkBitsFaithful L.link work.link
  online : WorkBitsFaithful L.onlineBatch.loc work.online

end Iop
