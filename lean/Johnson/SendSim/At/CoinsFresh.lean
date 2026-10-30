-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/CoinsFresh.lean: if an address is clear (SpenderClear) and the entries that
concern it are within the sender's number of coins, then over the sender's uniform coins the runs
that it spends are uniform and independent of the known runs. The proof of Spec.coinsFresh. It
claims no property of the protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file proves.
  coinsFresh   Spec.coinsFresh, which is written out in Johnson/SendSim/At/JoinFresh.lean: under
               WithinAt and SpenderClear (Johnson/SendSim/At/Fresh.lean, "clear"), an equation on
               the pair (the runs that p spends, the known runs) over uniform coins.
  apart_clear  At an address that is clear, no two spent entries share a coin's number.
  spent_known_e, spent_known_f   And none shares a number with a known entry, in either field.

Limits. The statement speaks only of coins: no message, symbol or answer of a sender is in it. The
conditions on the book are public. What is proved of them with a coin spent:
Johnson/SendSim/At/Fresh.lean, Limits.

How it fits. Spec.coinsFresh is stated in Johnson/SendSim/At/JoinFresh.lean. coinsFresh serves
sendFreshAtP (Johnson/SendSim/At/FreshAtMember.lean) at a job that does not fit its place: there
what is disclosed is the error value, so fresh reduces to this statement on coins. coinsFreshWide
(Johnson/SendSim/At/FreshWideProofs.lean), which serves sendFreshAtWide, applies it too. It rests on
runs_apart (Johnson/SendSim/At/WriteAll.lean) and apart_spent (Johnson/SendSim/At/SpentUnif.lean).

Notes. sendFits is not a premise. Of SpenderClear the proof uses the fields apart, noF and unknown
of MaskSpender and, of FoldSpender, the field unknown and that p spends by one entry, which holds no
coin of the base field.
-/
import Johnson.SendSim.At.WriteAll
import Johnson.SendSim.At.SpentUnif
import Johnson.SendSim.At.JoinFresh

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc Prob

variable {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}

/-- If p is clear (SpenderClear), no two of the entries by which p spends share a coin's number. -/
theorem apart_clear (h : SpenderClear P ride Bk ord o p) : ApartAll (Bk.spentBy o p) := by
  rcases h with h0 | h
  · unfold ApartAll
    rw [h0]
    exact List.Pairwise.nil
  · exact apart_spent h

/-- If p is clear (SpenderClear), no spent entry shares a number of a coin of the extension field
with a known entry. -/
theorem spent_known_e (h : SpenderClear P ride Bk ord o p) :
    Disjoint (eAll (Bk.spentBy o p)) (eAll (Bk.knownBy ord o p)) := by
  rcases h with h0 | M | F
  · rw [h0]
    exact Finset.disjoint_empty_left _
  · exact M.unknown
  · exact F.unknown

/-- If p is clear (SpenderClear), no spent entry shares a number of a coin of the base field with a
known entry. -/
theorem spent_known_f (h : SpenderClear P ride Bk ord o p) :
    Disjoint (fAll (Bk.spentBy o p)) (fAll (Bk.knownBy ord o p)) := by
  rcases h with h0 | M | F
  · rw [h0]
    exact Finset.disjoint_empty_left _
  · rw [M.noF]
    exact Finset.disjoint_empty_left _
  · obtain ⟨_, R, e, _, _, _, hsp, hc, _⟩ := F.one
    have h0 : fAll (Bk.spentBy o p) = ∅ := by
      rw [hsp]
      simp [fAll, fOf, hc]
    rw [h0]
    exact Finset.disjoint_empty_left _

/-- Proof of Spec.coinsFresh (Johnson/SendSim/At/JoinFresh.lean): if WithinAt and SpenderClear hold
at p, then over uniform coins the runs that p spends can be replaced by fresh uniform values,
independent of the known runs, without changing the distribution of the pair. -/
theorem coinsFresh : Spec.coinsFresh := fun _ _ Bk ord o p hW h =>
  runs_apart (Bk.spentBy o p) (Bk.knownBy ord o p) (fun e he => hW e (.inl he)) (apart_clear h)
    (spent_known_e h) (spent_known_f h)

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.coinsFresh
