-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38A/ForkOfLink.lean: where the verifier's state has an open segment, it has that
segment's ledger: what `S.fork?` reads, the slots of the segment's hidden scalars and its arrays.
One lemma for the law on the digits behind the approximate range proof's draw.

  `fork_of_link`: `s.link? = some L` gives some F with `s.fork? = some F`. The two readers
    (Johnson/Desc/First/State.lean) have the same three arms: by cases on where the state stands.

Limits. General: no public file, no written value, no head of conditions is read. Nothing on
soundness.
-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- **Where a segment is open, its ledger is there.** -/
theorem fork_of_link (s : S) (L : LinkCtx) (h : s.link? = some L) : ∃ F, s.fork? = some F := by
  unfold S.link? at h
  unfold S.fork?
  cases hh : s.here with
  | head a => by_cases ho : a.opened <;> simp [hh, ho] at h ⊢
  | lay a => simp
  | att a => simp
  | between => simp [hh] at h
  | fin a => simp [hh] at h
  | mem a => simp [hh] at h

end Q38

#print axioms Q38.fork_of_link
