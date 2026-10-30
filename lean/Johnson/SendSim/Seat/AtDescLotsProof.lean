-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtDescLotsProof.lean: wherever the maker returns (IM.Open), at every job of
lotJobs and wJobs the first chain has a member, the side there has fits and exact, and it has fresh
if the book is clear (BookClearAny). It claims no property of the protocol: not hiding, not zero
knowledge. The proofs of the three statements of AtDescLots.lean and AtDescOwn.lean, one application
each.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has.
  fieldsAtLots   Spec.fieldsAtLots. Wherever the maker of the proof file's description returns
                 (IM.Open), for every job J of lotJobs and wJobs, three things hold. The first chain
                 has a member at J's place. Every side that Side.seated returns there for our row
                 has fits and exact. For every book and order at which the book is clear at J's
                 sender (BookClearAny), that side has fresh.
  handAtLots     Spec.handAtLots: the last two parts in the form that the rule asks of one row. It
                 says no more than the first.
  fieldsAtOwn    Spec.fieldsAtOwn: the like at any sub-protocol of K1's own lot and any job with its
                 place, rounds and oracle messages.

How it fits. The first is fieldsAtLots_of at sendExactAt (Johnson/SendSim/At/ExactAt.lean) and
sendFreshAtWide (Johnson/SendSim/Seat/HandedWideProofs.lean). Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

Limits. The statements' own: all limits of AtDescLots.lean and AtDescOwn.lean.
-/
import Johnson.SendSim.Seat.AtDescLots
import Johnson.SendSim.Seat.HandedWideProofs

set_option autoImplicit false

namespace OnBytes.SendSim.Seat

/-- **Where the description's maker returns, at every job of the two lots: a member is at the place;
every side there has fits and exact; and, if a book is clear at that sender, fresh at that book.**
-/
theorem fieldsAtLots : Spec.fieldsAtLots := fieldsAtLots_of At.sendExactAt At.sendFreshAtWide

/-- The same in the form that the rule asks of one row. -/
theorem handAtLots : Spec.handAtLots := handAtLots_of_fields fieldsAtLots

/-- The like at any sub-protocol of K1's own lot and any job with its place, rounds and oracle
messages. -/
theorem fieldsAtOwn : Spec.fieldsAtOwn := fieldsAtOwn_of At.sendExactAt At.sendFreshAtWide

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.fieldsAtLots
#print axioms OnBytes.SendSim.Seat.handAtLots
#print axioms OnBytes.SendSim.Seat.fieldsAtOwn
