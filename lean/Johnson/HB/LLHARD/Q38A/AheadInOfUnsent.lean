-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38A/AheadInOfUnsent.lean: the value of the reader of arrays that are still ahead,
at an array of the open segment whose oracle message is not yet sent.

  `aheadIn_of_unsent`: under the premises h2 to h8 of `near_of_unsent`
    (Johnson/Desc/First/Batch/SmallNear.lean), `aheadIn sent own a (a.L.check.frame.link, name) =
    some ⟨A, x, M.shape⟩`. That theorem proves this equation inside and ends in a test's accept, so
    the value is lost to a caller: here the inner step stands as a statement, with its proof as it
    compiled there.

Limits. General: no public file, no written value, no head of conditions is read. Nothing on
soundness.
-/
import Johnson.Desc.First.Batch.SmallNear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9

/-- **What the reader of arrays ahead returns at an array that is not yet sent.** -/
theorem aheadIn_of_unsent (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))
    (a : VerifiableInference.Desc.K9.Part)
    (name : String) (A : Params.ReqArray) (sh : Params.ReqLink) (M : Params.ReqMessage)
    (x : Nat × Nat)
    (h2 : reqArray a.L.check.rows.layout a.L.check.frame.link name = some A)
    (h3 : a.L.check.frame.own.size ≤ A.message)
    (h4 : a.L.check.frame.shape.link[a.L.check.frame.link]? = some sh)
    (h5 : sh.messages[A.message]? = some M) (h6 : M.moment ≠ 0)
    (h7 : (sent M.moment)[((sh.messages.take A.message).filter fun y =>
      y.moment == M.moment).length]? = some x)
    (h8 : x ∈ own) :
    aheadIn sent own a (a.L.check.frame.link, name) = some ⟨A, x, M.shape⟩ := by
  unfold aheadIn aheadOf
  simp only [beq_self_eq_true, if_true, h2, Option.bind_some, whereIs_none _ _ h3, h4,
    Option.map_some, h5, h7]
  rw [if_neg (by simpa using h6)]
  simp [h8]

end Q38

#print axioms Q38.aheadIn_of_unsent
