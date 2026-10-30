-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/SaidMono.lean: A DEBT FROM THE PAIR GOES OVER TO EVERY
STRONGER LETTER `Said`. The file's rules ask the members' debts at the chain's WHOLE letter: the
conjunction of the kinds' authors' clauses and `SaidOk`. An author states its law at its own clause,
or at `SaidOk`. Each debt has the pair `ThrS T Said` among its premises alone: so it is the weaker,
the more the letter says. Here that step, for the five debts (Honest/Thread/PaysS.lean), the two
shares and the laying of a rider's clause (Honest/Thread/SharesS.lean): a cold reader's find: no
lemma carried them. (For `OnFromS` it lies: `onFromS_mono`, Honest/Thread/OnSaid.lean.) Calls of the
premise alone.

  `thrS_mono`
  `playsS_mono`, `behindS_mono`, `exchangeS_mono`, `ridesPastS_mono`, `acceptedS_mono`
  `exchangeAtS_mono`, `ridesPastAtS_mono`, `laysAtS_mono`

Limits. None is one of the library's goals. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  {Said Said' : Nat → Coins Bk → Mid W X → Prop}

theorem thrS_mono (hS : ∀ b k m, Said' b k m → Said b k m) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid W X} {E : Env} (h : ThrS T Said' b k s m E) : ThrS T Said b k s m E :=
  ⟨h.1, hS _ _ _ h.2⟩

theorem playsS_mono (hS : ∀ b k m, Said' b k m → Said b k m) {b : Nat}
    (h : PlaysS T Said b) : PlaysS T Said' b :=
  fun blk hblk k s m E ds l hA => h blk hblk k s m E ds l (thrS_mono T hS hA)

theorem behindS_mono (hS : ∀ b k m, Said' b k m → Said b k m) {b : Nat}
    (h : BehindS T Said b) : BehindS T Said' b :=
  fun blk hblk k s m E ds y cols s' hA => h blk hblk k s m E ds y cols s' (thrS_mono T hS hA)

theorem exchangeS_mono (hS : ∀ b k m, Said' b k m → Said b k m) {b : Nat}
    (h : ExchangeS T Said b) : ExchangeS T Said' b :=
  fun blk hblk k s m E ds y cols s' hA => h blk hblk k s m E ds y cols s' (thrS_mono T hS hA)

theorem ridesPastS_mono (hS : ∀ b k m, Said' b k m → Said b k m) {b : Nat}
    (h : RidesPastS T Said b) : RidesPastS T Said' b :=
  fun k s m E s' ps i v hA => h k s m E s' ps i v (thrS_mono T hS hA)

theorem acceptedS_mono (hS : ∀ b k m, Said' b k m → Said b k m)
    {fall : Nat → S → List Fmt.Drawn → Option String} {b : Nat}
    (h : AcceptedS T Said fall b) : AcceptedS T Said' fall b :=
  fun blk hblk k s m E ds y cols hA => h blk hblk k s m E ds y cols (thrS_mono T hS hA)

theorem exchangeAtS_mono (hS : ∀ b k m, Said' b k m → Said b k m) {b : Nat} {i : T.ι}
    (h : ExchangeAtS T Said b i) : ExchangeAtS T Said' b i :=
  fun blk hblk k s m E ds y cols s' hA => h blk hblk k s m E ds y cols s' (thrS_mono T hS hA)

theorem ridesPastAtS_mono (hS : ∀ b k m, Said' b k m → Said b k m) {b : Nat} {i : T.ι}
    (h : RidesPastAtS T Said b i) : RidesPastAtS T Said' b i :=
  fun k s m E s' ps v hA => h k s m E s' ps v (thrS_mono T hS hA)

theorem laysAtS_mono (hS : ∀ b k m, Said' b k m → Said b k m) {b : Nat} {c : RiderCl W S}
    (h : LaysAtS T Said b c) : LaysAtS T Said' b c :=
  fun blk hblk k s m E ds y cols s' hA => h blk hblk k s m E ds y cols s' (thrS_mono T hS hA)

end ProofFile.Honest

#print axioms ProofFile.Honest.thrS_mono
#print axioms ProofFile.Honest.playsS_mono
#print axioms ProofFile.Honest.behindS_mono
#print axioms ProofFile.Honest.exchangeS_mono
#print axioms ProofFile.Honest.ridesPastS_mono
#print axioms ProofFile.Honest.acceptedS_mono
#print axioms ProofFile.Honest.exchangeAtS_mono
#print axioms ProofFile.Honest.ridesPastAtS_mono
#print axioms ProofFile.Honest.laysAtS_mono
