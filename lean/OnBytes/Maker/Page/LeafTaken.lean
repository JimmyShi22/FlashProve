-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/LeafTaken.lean: the page's own call of a leaf query (`leafCall`,
OnBytes/Maker/Page/Trees.lean) is the call that the code of leaf queries over strings of bits spells
(`call2`, OnBytes/TypedOracleCompiler/StringsBoth.lean), wherever that one gives a call.

So a taken spelling of leaves that writes the bits of the string of `call2`'s call, and nothing
else, is "silent or agreeing" in the sense of OnBytes/Maker/Page/LeafAgree.lean.

Main names.
  `readBody_rd2`: on a body of at least 128 bits `readBody` gives what `rd2` reads.
  `leafCall_of_call2`: `call2 L q = some c → leafCall q.body q.salt = some c`.
  `agrees_of_call2`: if s is the bits of the string of `call2`'s call at q, and the page's own call
    at q is c, then the bytes of s are the string of c.

Limits: of a code of leaves it is asked, not shown, that what it writes is the bits of the string of
`call2`'s call. Where `call2` gives no call nothing is said. `gJ P O` is a function of the typed
query, no one-to-one coding. Nothing on soundness.


-/
import OnBytes.Maker.Page.LeafAgree
import OnBytes.TypedOracleCompiler.StringsBoth

set_option autoImplicit false

namespace OnBytes.Maker.Page
open _root_.Run TypedOracleCompiler.Strings

/-- On a body of at least 128 bits `readBody` gives what `rd2` reads. -/
theorem readBody_rd2 (b : List Bool) (h : 128 ≤ b.length) : readBody b = some (rd2 b) := by
  unfold readBody
  rw [if_pos h]
  rfl

variable {I X : Type} (L : _root_.Iop.BatchProtocol I X)

/-- Where `call2` gives a call, the page's own call is that one. -/
theorem leafCall_of_call2 (q : TypedOracleCompiler.Compile.Batch.LeafIn (strung L)) (c : Fmt.OQ)
    (h : call2 L q = some c) : leafCall q.body q.salt = some c := by
  unfold call2 at h
  by_cases hk : ok2 q.body = true
  · rw [if_pos hk] at h
    unfold leafCall
    rw [readBody_rd2 _ ((ok2_iff _).1 hk).1.2]
    exact h
  · rw [if_neg hk] at h
    cases h

/-- A string that is the bits of the string of `call2`'s call agrees with the page's own call. -/
theorem agrees_of_call2 (q : TypedOracleCompiler.Compile.Batch.LeafIn (strung L)) (s : List Bool)
    (hs : ∃ c, call2 L q = some c ∧ s = bytesToBits (strOf c)) (c' : Fmt.OQ)
    (hc : leafCall q.body q.salt = some c') : bitsToBytes s = strOf c' := by
  obtain ⟨c, h1, rfl⟩ := hs
  rw [leafCall_of_call2 L q c h1] at hc
  rw [bitsToBytes_bytesToBits, Option.some.inj hc]

end OnBytes.Maker.Page
