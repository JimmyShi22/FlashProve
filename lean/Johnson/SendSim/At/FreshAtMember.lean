-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/FreshAtMember.lean: at every Seated side the honest sender has the field fresh of
Good, with the bound budAt on queried positions, under public conditions on the book: at each
address that is clear (SpenderClear) and whose entries are within the sender's number of coins, and
at all addresses if the book is clear (BookClear). It claims no property of the protocol: not
hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file proves. σ is any side that is Seated at a job J, Bk any book and ord any order.
  sendFreshAtP  Spec.sendFreshAtP. Let p be an address that is clear (SpenderClear), and let the
                entries that concern p be within the sender's number of coins (WithinAt). Then for
                every state, all challenges that σ's two rounds can sample (drawsFit) and all
                queried positions within the bound (budAt): over the sender's uniform coins, the
                triple (the runs that p spends, what the sender discloses, the known runs) has the
                same distribution as when the first is replaced by fresh uniform values, independent
                of the rest. The field's other parameters play no part: the sender spends and
                carries no run and never aborts.
  sendFreshAt   Spec.sendFreshAt. If the book is clear at the sender (BookClear), this holds at
                every address p: σ has the field fresh, with the bound budAt.
  good_seated   If the book is clear at the sender (BookClear), σ has Good at On := True and the
                bound budAt. Its predicates A and B never hold, so its fields plays (the row can be
                played) and acc (the verifier accepts) hold vacuously.

Limits.
  - Where the premises are met. That a book of the release is clear in the strict form, at a spender
    (`SpenderClear`) or at the sender (`BookClear`), is proved in no file of this folder; of the
    wider condition: the table of premises in Johnson/SendSim/Defs.lean, "the book is clear". Where
    each premise is proved for the release's files: the table of premises in
    Johnson/SendSim/Defs.lean. At the descriptions of the release's files, Seated is proved only for
    the sides at the places of the kind K1 that result
    (3) of Johnson/SendSim/Defs.lean names (seatedAt_job, if the maker of the proof file's
    description succeeds; seatedAt_key). The other sendings of that kind are not covered.
  - sendFreshAt and good_seated are all or nothing. They take BookClear, so one address that is not
    clear makes them vacuous for every spender of this owner.
  - One owner and one spender: nothing is said on the runs of two owners together, or on what a
    later part makes of the spent coins. A table of more than one row that is sent along is excluded
    by a premise; sendFreshAtPWide (Johnson/SendSim/At/FreshWideProofs.lean) admits it. All three
    are stated in full in the Limits of Johnson/SendSim/At/Fresh.lean.

How it fits. The two statements are in Johnson/SendSim/At/Fresh.lean. sendFreshAtP follows from
rowsFresh (Johnson/SendSim/At/RowsFresh.lean) and coinsFresh (Johnson/SendSim/At/CoinsFresh.lean) by
sendFreshAtP_of_rows (Johnson/SendSim/At/JoinFresh.lean); good_seated adds sendExactAt
(Johnson/SendSim/At/ExactAt.lean). Johnson/SendSim/At/SpendersAloneProofs.lean uses sendFreshAtP.
Spec.fieldsAtLots rests not on these but on sendFreshAtWide
(Johnson/SendSim/Seat/HandedWideProofs.lean), the same under the wider condition.
-/
import Johnson.SendSim.At.RowsFresh
import Johnson.SendSim.At.CoinsFresh
import Johnson.SendSim.At.ExactAt
import Johnson.SendSim.At.GoodOf

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

variable {S Cl V W X Pb : Type}

/-- Proof of Spec.sendFreshAtP (Johnson/SendSim/At/Fresh.lean): a Seated side has the field fresh of
Good at one address (FreshAtP, with the bound budAt) if that address is clear (SpenderClear) and the
entries that concern it are within the sender's number of coins (WithinAt). -/
theorem sendFreshAtP : Spec.sendFreshAtP := sendFreshAtP_of_rows rowsFresh coinsFresh

/-- Proof of Spec.sendFreshAt (Johnson/SendSim/At/Fresh.lean): a Seated side has the field fresh of
Good, with the bound budAt, if the book is clear at the sender (BookClear). -/
theorem sendFreshAt : Spec.sendFreshAt := sendFreshAt_of_each sendFreshAtP

/-- A Seated side has the structure Good if the book is clear at the sender (BookClear), at
On := True and the bound budAt. The predicates A and B are those that never hold, so the fields
plays and acc hold vacuously.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
theorem good_seated {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X) (Bk : ProverCoinCounts)
    (ord : List Place) (chain firstTree : Nat) (h : Seated σ J)
    (hB : BookClear J.P J.ride Bk ord ⟨σ.block.place, 0⟩) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) fun _ _ asks => budAt J.P asks :=
  good_of_specs sendExactAt sendFreshAt φ σ J Bk ord chain firstTree h hB

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.sendFreshAtP
#print axioms OnBytes.SendSim.At.sendFreshAt
#print axioms OnBytes.SendSim.At.good_seated
