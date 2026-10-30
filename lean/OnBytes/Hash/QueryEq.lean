-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Hash/QueryEq.lean: the step of a chain of OnBytes/Hash/Query.lean is the one of
Fmt/Rules5.lean.

A step draws the verifier's message of one round from the hash (OnBytes/Hash/Query.lean says how).
`Fmt.Chain.query` states it call by call. `queryH` is the form for compiled code, which hashes what
a round's calls share only once. The program calls `queryH`; Fmt/ states the format with
`Fmt.Chain.query`.

Main theorems: `queryH_eq` (for all arguments), `queryH_eq_query` (as functions). Both rest on
`Fmt.queryF_eq` (Fmt/Rules5Fast.lean). Nothing is claimed here on BLAKE2b or on the strength of the
hash.
-/
import OnBytes.Hash.Query

namespace OnBytes

open Fmt

/-- `queryH` gives what `Fmt.Chain.query` gives, for all arguments. -/
theorem queryH_eq (c : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat) :
    queryH c msg kind work nonce K = c.query msg kind work nonce K :=
  queryF_eq c msg kind work nonce K

/-- `queryH` and `Fmt.Chain.query` are the same function. -/
theorem queryH_eq_query : queryH = Chain.query := by
  funext c msg kind work nonce K
  exact queryH_eq c msg kind work nonce K

end OnBytes

#print axioms OnBytes.queryH_eq_query
