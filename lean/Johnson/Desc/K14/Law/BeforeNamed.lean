-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/BeforeNamed.lean: the block "LIN point", which draws the shared point psi_sh,
names a message that must be fixed before that draw, or fails its test on the plan. Theorems.

  before_is_the_parameter   what the block names in "before" is the parameter beforePoint.
  empty_before_refused      with an empty beforePoint the block's test on the plan says no: THE
                            CONTROL: a description that names no message is refused on the plan.
  named_of_planOk           the block's test on the plan says yes: "before" names a message.
What is not claimed. WHICH message is named: a wrong one passes here; that is a table's matter, off
the plan, made elsewhere (the format's owedOk). THAT A NAMED MESSAGE OF AN EARLIER CHAIN IS
FIXED BEFORE THE DRAW: of such a message the format's beforeOk asks only that it is sent; that the
shared chain's draws hang on the first chain's messages is the compiler's matter. Nothing on
soundness.

-/
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block)

/-- What "LIN point" names in "before" is the parameter. -/
theorem before_is_the_parameter (P : P14) (b1 : Block St Unit) (l : List (Block St Unit))
    (hb : blocks P = some (b1 :: l)) : b1.before = P.beforePoint := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq] at hb
  obtain ⟨_, _, rfl, _⟩ := hb
  rfl

/-- **With no message named the block fails its test on the plan.** -/
theorem empty_before_refused (P : P14) (b1 : Block St Unit) (l : List (Block St Unit))
    (hb : blocks P = some (b1 :: l)) (he : P.beforePoint = []) : b1.planOk = false := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq] at hb
  obtain ⟨_, _, rfl, _⟩ := hb
  simp [he]

/-- The block's test on the plan says yes: it names a message. -/
theorem named_of_planOk (P : P14) (b1 : Block St Unit) (l : List (Block St Unit))
    (hb : blocks P = some (b1 :: l)) (hp : b1.planOk = true) : b1.before ≠ [] := by
  intro he
  rw [before_is_the_parameter P b1 l hb] at he
  rw [empty_before_refused P b1 l hb he] at hp
  cases hp

end Desc.K14.Law
