-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/BeforeOfAll.lean: where all sub-protocols of the shared chain's own kind
(`blocksOr P`, Johnson/Desc/K14/Blocks.lean; our files call a sub-protocol a block) pass their own
tests on the list of rounds, the parameter `P.beforePoint` is not empty: it names a message of the
first chain that is fixed before the shared point is drawn. Two statements with their proofs.

Why it holds. The sub-protocol "LIN point" asks, among its tests on the list of rounds, that the
parameter is not empty (`empty_before_refused`, Johnson/Desc/K14/Law/BeforeNamed.lean). Where the
eight sub-protocols cannot be made, `blocksOr` is one sub-protocol that fails its test.

  `before_of_all`: the statement, at any parameters.
  `before_at_seat`: at the parameters of which the shared chain's seat is made (`p14Of` at
    `beforePointOf N`, Johnson/Desc/ProofFile/Lot/K14SeatAtZ.lean).

For whom. The field "before" of `Written Z x` (Johnson/Goal/Numbers/WrittenAtZ.lean): with a law
that gives the premise from "the IOP as written in Lean passes its tests on the list of rounds"
(`blocksOr_ok` is meant; it is not imported here).
Can the premise be met? Not shown here: it is a test on the list of rounds at the public files.
Limits. Nothing on which message is named. Nothing on soundness.
-/
import Johnson.Desc.K14.Law.BeforeNamed
import Johnson.Desc.ProofFile.Lot.K14SeatAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.OnPublicFiles

/-- **Where all of the kind's sub-protocols pass their own tests on the list of rounds, the
parameter names a message that is fixed before the shared point is drawn.** -/
theorem before_of_all (P : P14) (h : (blocksOr P).all (·.planOk) = true) :
    P.beforePoint ≠ [] := by
  intro he
  unfold blocksOr at h
  cases hb : blocks P with
  | none =>
    rw [hb] at h
    cases h
  | some l =>
    rw [hb] at h
    cases l with
    | nil =>
      unfold blocks at hb
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hb
      obtain ⟨_, _, hn⟩ := hb
      cases hn
    | cons b1 l' =>
      have h1 : b1.planOk = true := (List.all_eq_true.1 h) b1 List.mem_cons_self
      rw [empty_before_refused P b1 l' hb he] at h1
      cases h1

/-- The same at the parameters that the shared chain's seat is made of. -/
theorem before_at_seat (c : Model.Verify.Chains) (N : H2U.Places4)
    (h : (blocksOr (p14Of c (beforePointOf N))).all (·.planOk) = true) : beforePointOf N ≠ [] :=
  before_of_all (p14Of c (beforePointOf N)) h

end Desc.K14.Law
