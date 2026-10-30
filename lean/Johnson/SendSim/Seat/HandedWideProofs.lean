-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/HandedWideProofs.lean: at every Seated side, if the book is clear at the sender
in the wider sense (BookClearAny), the honest sender has the field fresh of Good, with the bound
budAt on queried positions, and the side has Good at predicates A and B that never hold, so that
plays and acc hold vacuously. It claims no property of the protocol: not hiding, not zero knowledge.
The proofs of the two statements of Johnson/SendSim/At/BookWide.lean and of the two of
HandedWide.lean.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean; for the row and the
rule, Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves.
  sendFreshAtWide   Spec.sendFreshAtWide. Let σ be a side that is Seated at a job J, and let the
                    book satisfy BookClearAny at the sender (Johnson/SendSim/At/Fresh.lean,
                    "clear"). Then σ has the field fresh, with the bound budAt. That is: for every
                    address p, every state, all challenges that σ's two rounds can sample (drawsFit)
                    and all queried positions within the bound, over the sender's uniform coins the
                    triple (the runs that p spends, what the sender discloses, the known runs) has
                    the same distribution as when the first is replaced by fresh uniform values,
                    independent of the rest. The field's other parameters play no part: the sender
                    spends and carries no run and never aborts.
  goodSeatedWide    Spec.goodSeatedWide. Under the same premises σ has Good, at On := True and the
                    bound budAt, with the predicates A and B that never hold, so that plays and acc
                    hold vacuously.
  goodHandedWide    Spec.goodHandedWide. The same for a side that Side.seated returns for the
                    sender's row (sendRow, "our row"), if its sub-protocol has K1's two rounds and
                    oracle messages at J.P.
  handHandedWide    Spec.handHandedWide. Under the premises of the third, every side of the row,
                    with the rule's predicates substituted (Unlettered.lay), has Good for some A₁
                    and B₁; in the proof these are the two that never hold.

Limits.
  - Where the premises are met. That the book which the maker onlineProverFromPublicFiles returns satisfies BookClearAny
    at the opening's sender, at the returned description's own order of places, is proved in the
    side library, in scope, where the gate accepts (clear_at_opening,
    AtFullSide/K1/BookAtOpening.lean); the rest: the table of premises in Johnson/SendSim/Defs.lean,
    "the book is clear". Where each premise is proved for the release's files: the table of premises
    in Johnson/SendSim/Defs.lean. At the descriptions of the release's files, Seated is proved only
    for the sides at the places of the kind K1 that result (3) of Johnson/SendSim/Defs.lean names
    (seatedAt_job, if the maker of the proof file's description succeeds; seatedAt_key). The other
    sendings of that kind are not covered.
  - All four are all or nothing: one address that does not satisfy SpenderClearAny makes them
    vacuous for every spender of that owner.
  - The three on Good hold at predicates A and B that never hold. The last says "for some A₁ and
    B₁"; in its proof they are these two. So nothing is said on the fields plays (the row can be
    played) and acc (the verifier accepts).
  - Each statement speaks of one owner of coins. The rule requires the same of every other row of
    its chain.

How it fits. sendFreshAtWide follows from sendFreshAtPWide
(Johnson/SendSim/At/FreshWideProofs.lean), goodSeatedWide from it and sendExactAt
(Johnson/SendSim/At/ExactAt.lean), the third from the second, the fourth from the third by
hand_of_house (Johnson/Desc/ProofFile/Honest/Thread/RowsMore.lean). fieldsAtLots
(AtDescLotsProof.lean) and AtKey.lean use
sendFreshAtWide.
-/
import Johnson.SendSim.Seat.HandedWide
import Johnson.SendSim.At.FreshWideProofs
import Johnson.SendSim.At.ExactAt

set_option autoImplicit false

namespace OnBytes.SendSim.At

/-- Proof of Spec.sendFreshAtWide (Johnson/SendSim/At/BookWide.lean): a Seated side has the field
fresh of Good, with the bound budAt, at every book that satisfies BookClearAny at the sender. -/
theorem sendFreshAtWide : Spec.sendFreshAtWide := sendFreshAtWide_of_each sendFreshAtPWide

/-- Proof of Spec.goodSeatedWide (Johnson/SendSim/At/BookWide.lean): a Seated side has the structure
Good at every book that satisfies BookClearAny at the sender, with predicates A and B that never
hold, so that plays and acc hold vacuously. -/
theorem goodSeatedWide : Spec.goodSeatedWide := goodSeatedWide_of sendExactAt sendFreshAtWide

end OnBytes.SendSim.At

namespace OnBytes.SendSim.Seat

/-- Proof of Spec.goodHandedWide (Johnson/SendSim/Seat/HandedWide.lean): the same for a side that
Side.seated returns for our row, if its sub-protocol has K1's two rounds and oracle messages at J.P
and the book satisfies BookClearAny at (a, 0). -/
theorem goodHandedWide : Spec.goodHandedWide := goodHandedWide_of At.goodSeatedWide

/-- Proof of Spec.handHandedWide (Johnson/SendSim/Seat/HandedWide.lean): under the premises of
Spec.goodHandedWide, every side of our row with the rule's predicates substituted has Good for some
A₁ and B₁; in the proof these are the two that never hold, so plays and acc hold vacuously. -/
theorem handHandedWide : Spec.handHandedWide := handHandedWide_of goodHandedWide

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.At.sendFreshAtWide
#print axioms OnBytes.SendSim.At.goodSeatedWide
#print axioms OnBytes.SendSim.Seat.goodHandedWide
#print axioms OnBytes.SendSim.Seat.handHandedWide
