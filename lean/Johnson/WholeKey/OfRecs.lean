-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/OfRecs.lean: THE STRATEGIES AND THE TESTS FOR A STOP of the scheme with the whole
key published (Plays, Johnson/WholeKey/Defs.lean) FROM THREE HONEST SIDES THAT ARE ARGUMENTS
(ThreeProvers, Johnson/Prover/All/OfHonest.lean): values of the library's type of an honest prover (Honest,
Iop/InteractiveOracleProof.lean) for the three protocols of an object with out-of-domain samples.

General definitions and one equation that holds by unfolding. This file states no goal of the
release.

Why. A statement on hiding and a statement on completeness say something together only if they speak
of THE SAME honest provers, and of the provers that the scheme runs. An object's own three fields
for honest provers may hold silent placeholders. So the honest sides are arguments, and here the
scheme's letters are read off them: the strategies are their strategies; a run's messages are
withheld exactly at their own abort sets (Honest.withheld), at the private input and the
instance of that run. These are the sets of which the library's honest-verifier zero knowledge
speaks (Honest.output is "none" there) and the sets that the accept laws of
Johnson/Prover/All/OfHonest.lean name (ThreeProvers.bads).

THE COPY's NUMBER. The session's honest side has ONE type of coins for all numbers: it is one value,
whose private input ends with the number (as in ThreeProvers). The library's honest-verifier zero knowledge
has one simulator for all private inputs, which is not told the private input; the session's plain
parts hold the number. So a premise on hiding is to be asked of THE HONEST SIDE AT A FIXED NUMBER
(sessionAt Hs n), for each n: one simulator for each number. The number is public (HonestSide.nm).

Main names (namespace OnBytes.WholeKey).
  Decs Hs        the three decisions "do these verifier messages lie in the abort set?", as data.
  Plays.ofRecs   the strategies and tests.
  ofRecs_joint   the strategies as one family are ThreeProvers.strats: by unfolding.
  sessionAt      the session's honest side at a fixed number of the copy.

Limits. Definitions. No law is asked of the honest sides.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Defs
import Johnson.Prover.All.OfHonest

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {L : HolographicProtocol I X}

/-- The decisions as data: for each of the three honest sides, whether given verifier messages lie
in the abort set at a private input and an instance. -/
structure Decs (Hs : ThreeProvers L) where
  T : ∀ w x ρ, Decidable (ρ ∈ Hs.T.withheld w x)
  Lk : ∀ w x ρ, Decidable (ρ ∈ Hs.Lk.withheld w x)
  B : ∀ w x ρ, Decidable (ρ ∈ Hs.B.withheld w x)

/-- **The strategies and the tests for a stop, off three honest sides.** -/
def Plays.ofRecs (Hs : ThreeProvers L) (dc : Decs Hs) : Plays L Hs.T.Coin Hs.Lk.Coin Hs.B.Coin where
  T := fun i r e κ => Hs.T.strat (i, r, e) (L.recOf i r e) κ
  Lk := fun i a b κ => Hs.Lk.strat (i, a, b) (L.recOf i a.1 a.2, L.recOf i b.1 b.2) κ
  B := fun i r e x n κ => Hs.B.strat (i, r, e, n) (x, L.recOf i r e) κ
  stopT := fun i r e ρ => @decide _ (dc.T (i, r, e) (L.recOf i r e) ρ)
  stopL := fun i a b ρ => @decide _ (dc.Lk (i, a, b) (L.recOf i a.1 a.2, L.recOf i b.1 b.2) ρ)
  stopB := fun i r e x n ρ => @decide _ (dc.B (i, r, e, n) (x, L.recOf i r e) ρ)

/-- As one family in the triple of the coins they are the strategies that the accept laws speak of.
-/
theorem ofRecs_joint (Hs : ThreeProvers L) (dc : Decs Hs) : (Plays.ofRecs Hs dc).joint = Hs.strats := rfl

/-- The session's honest side at a fixed number of the copy: the same coins, strategy and abort
sets, the private input without the number. -/
def sessionAt (Hs : ThreeProvers L) (n : ℕ) : Honest L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed) where
  Coin := Hs.B.Coin
  ext := fun w => Hs.B.ext (w.1, w.2.1, w.2.2, n)
  strat := fun w x c => Hs.B.strat (w.1, w.2.1, w.2.2, n) x c
  Bad := Hs.B.Bad
  Hid := fun w x => Hs.B.Hid (w.1, w.2.1, w.2.2, n) x

end OnBytes.WholeKey
