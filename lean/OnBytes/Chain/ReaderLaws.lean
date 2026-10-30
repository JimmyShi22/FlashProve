-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/ReaderLaws.lean: the reader that the program runs is the strict reader of Fmt/.

Main theorems: `readChain_eq`, `viewOf_eq`.
-/
import OnBytes.Chain.Reader
import OnBytes.Chain.EngineLaws
import OnBytes.Hash.HEq
import OnBytes.Hash.QueryEq

namespace OnBytes

/-- The reader that the program runs is the strict reader at the format's hash. -/
theorem readChain_eq (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    readChain S seen b i = Fmt.readChainX (m := Id) Fmt.formatHash S seen b i := by
  unfold readChain
  rw [readChainK_eq, queryH_eq_query, formatHashFastForm_eq_formatHash]
  exact readChainQ_eq S seen b i

/-- The view that the program makes is the view of Fmt/. -/
theorem viewOf_eq (S : Fmt.SpecX) (o : Fmt.ChainOut) : viewOf S o = Fmt.viewX S o :=
  viewF_eq S o

end OnBytes
