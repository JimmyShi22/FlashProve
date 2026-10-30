-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/ExactAt.lean: at every Seated side, for challenges that its rounds can sample and
queried positions within the bound (budAt), what the honest sender discloses has the distribution of
its simulator's output. It claims no property of the protocol: not hiding, not zero knowledge. The
proofs of Spec.exactOut and Spec.sendExactAt.
Terms: Johnson/SendSim/At/Sim.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves.
  exactOut      At every side that is Seated, for every state, every front, all challenges that the
                side's two rounds can sample (drawsFit) and all queried positions within the bound
                (budAt): the distribution of what the sender discloses, over its own coins, is the
                distribution of what sendSim outputs, over its own. There is no further premise.
  sendExactAt   The same in the form ExactAt (with On := True), which has three more premises
                (m.seen = front.seen; front.holds; no abort by hid), so exactOut is the stronger
                statement. The field exact of the structure Good has a fourth, on the opened
                columns; ExactAt gives the field at every pre (Johnson/SendSim/At/Sim.lean).

Limits.
  - exact is never to be quoted without fresh (sendFreshAt, sendFreshAtWide), which requires more:
    conditions on the book. A sender that is modified in one of two ways would still satisfy exact's
    equation: the tail of a table that is sent along is set to 0; or the pad of an answer that also
    reads a free entry is set to 0. This is not proved. The argument is not written down here. At
    small examples fresh's equation is false where such a tail or pad is known: the tail's, if a
    position is queried; the pad's, if the seed's weight on the free entry is not 0 (said here
    without a theorem). That a coin set to 0 is as good as known is a reading, not a theorem.
  - That the positions which an execution queries are within the bound is a premise. Where each
    premise is proved for the release's files: the table of premises in Johnson/SendSim/Defs.lean.
  - At the descriptions of the release's files, Seated is proved only for the sides at the places of
    the kind K1 that result (3) of Johnson/SendSim/Defs.lean names (seatedAt_job, if the maker of
    the proof file's description succeeds; seatedAt_key). The other sendings of that kind are not
    covered.
  - sendFits is not a premise. Where the job does not fit its place both sides are the error value,
    and the statements say nothing. The other limits of the two statements are in
    Johnson/SendSim/At/Sim.lean and Johnson/SendSim/At/RowsExact.lean.

How it fits. Spec.exactOut is stated in Johnson/SendSim/At/Member.lean, Spec.sendExactAt in
Johnson/SendSim/At/Sim.lean. Each proof is one line: exactOut from rowsExact
(Johnson/SendSim/At/RowsExact.lean), sendExactAt from exactOut, by the implications of
Johnson/SendSim/At/Joins.lean. fieldsAtLots (Johnson/SendSim/Seat/AtDescLotsProof.lean) uses
sendExactAt. sendFreshAt is in Johnson/SendSim/At/FreshAtMember.lean, sendFreshAtWide in
Johnson/SendSim/Seat/HandedWideProofs.lean, seatedAt_job in Johnson/SendSim/Seat/AtDescStands.lean,
seatedAt_key in Johnson/SendSim/Seat/AtKeyStands.lean.
-/
import Johnson.SendSim.At.Joins
import Johnson.SendSim.At.RowsExact

set_option autoImplicit false

namespace OnBytes.SendSim.At

/-- At the one member of a Seated side, for challenges that the rounds can sample and queried
positions within the bound budAt, what the honest sender discloses has the distribution of the
simulator's output. -/
theorem exactOut : Spec.exactOut := exactOut_of_rows rowsExact

/-- ExactAt holds at every Seated side, with On := True and the bound budAt. -/
theorem sendExactAt : Spec.sendExactAt := sendExactAt_of_out exactOut

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.exactOut
#print axioms OnBytes.SendSim.At.sendExactAt
