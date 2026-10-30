-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Hash/Query.lean: the step of a chain, in the form for compiled code.

A chain is the hash chain that replaces the verifier of one interactive protocol (Fiat-Shamir). In
a round of a chain the verifier's message is drawn from the answers to several calls of the hash
(format page docs/format/FORMAT.md, R5.x). All calls of a round hash the same 16 bytes of
the hash's label and the same message of the prover, and differ only in their last sixteen bytes. So
the whole 128-byte blocks of what they share are hashed once, the state after them is kept, and each
call is finished from that state. `Fmt.Chain.queryF` (Fmt/Rules5Fast.lean) does this, and `queryH`
is that function. The C++ counterparts are ChainAbsorbT and chain_call in blocks/hash/hash.h.

Main definitions: `queryH`.

This file holds no theorem. That `queryH` equals `Fmt.Chain.query` is proved in
OnBytes/Hash/QueryEq.lean. Tests: OnBytes/Hash/TestBlake2b.lean.
-/
import Fmt.Rules5Fast
import Fmt.Rules8Fast

namespace OnBytes

/-- The step of a chain, one round: the same function as `Fmt.Chain.query` (proved in
OnBytes/Hash/QueryEq.lean). The result is none if the round's data are outside the bounds of R5.7
(`Fmt.askOK`) or the work test of R5.5 fails (`Fmt.passesA`). Otherwise it is the chain with its
next value and round number, and the K blocks of 32 bytes of the verifier's message (R5.4). -/
def queryH : Fmt.Qry := fun c msg kind work nonce K => c.queryF msg kind work nonce K

end OnBytes
