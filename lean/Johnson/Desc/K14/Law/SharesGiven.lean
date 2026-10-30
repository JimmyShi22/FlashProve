--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharesGiven.lean: EACH BLOCK OF THE SHARED CHAIN THAT BEARS A SHARE OF THE
TESTS ON THE PLAN ASKS THAT SHARE. Theorems.

WHY. A block's share is dealt BY ITS NAME: At.ofBlock (Johnson/Desc/OnPlan/OkShare.lean) compares
the name with four strings and says true at every other. So a block whose name were turned by a
letter would lose its share, and no test would notice. These lemmas are the lock: each is proved by
evaluating ofBlock at the name that the block bears in Johnson/Desc/K14/Blocks.lean: turn a letter
in either file and the proof fails.
  point_given    "LIN point": its test on the plan gives At.linPoint P.codes P.S (and a message is
                 fixed before the point).
  sendU_given    "send o_u": its test gives At.sending P.codes (At.withU P.S).
  sendO_given    "send o_omega": its test gives At.sending P.codes (linMessageOmega P.S).
  names_are      the eight names, in order.
  withU_said     where At.linPoint says yes, At.withU's stand-by value (getD #[]) is not taken: what
                 goes out beside the folded row is said.
Two examples show the ground: at "LIN point" ofBlock IS linPoint; at a name with one letter turned
it is true.
The fourth share, "SPLIT"'s: split_given (Johnson/Desc/K14/Law/SplitGiven.lean).
What is not claimed. That some plan passes. Nothing on soundness.

-/
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.OnPublicFiles

/-- **What "LIN point"'s test on the plan gives.** -/
theorem point_given (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hp : b1.planOk = true) :
    OkD.At.linPoint P.codes P.S = true ∧ P.beforePoint ≠ [] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  have h : (OkD.At.linPoint P.codes P.S && !P.beforePoint.isEmpty) = true := hp
  rw [Bool.and_eq_true] at h
  refine ⟨h.1, fun e => ?_⟩
  rw [e] at h
  exact absurd h.2 (by decide)

/-- **What "send o_u"'s test on the plan gives.** -/
theorem sendU_given (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hp : b2.planOk = true) :
    OkD.At.sending P.codes (OkD.At.withU P.S) = true := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  have h : (_ && OkD.At.sending P.codes (OkD.At.withU P.S) && _) = true := hp
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

/-- **What "send o_omega"'s test on the plan gives.** -/
theorem sendO_given (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hp : b5.planOk = true) :
    OkD.At.sending P.codes (linMessageOmega P.S) = true := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  have h : (_ && OkD.At.sending P.codes (linMessageOmega P.S) && _) = true := hp
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

/-- The eight names, in order. -/
theorem names_are (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    [b1, b2, b3, b4, b5, b6, b7, b8].map (·.name) =
      ["LIN point", "send o_u", "(rec_gamma)", "LOC", "send o_omega", "joins", "LIN zeta",
        "SPLIT"] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  rfl

/-- Where "LIN point"'s share says yes, the sending's notices are said, not stood in for. -/
theorem withU_said (codes : Codes) (S : LinShape) (h : OkD.At.linPoint codes S = true) :
    ∃ w, linWithU S = some w ∧
      OkD.At.withU S = #[(⟨S.fold.u, S.fold.leafClass⟩ : OracleNotice)] ++ w := by
  unfold OkD.At.linPoint at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 h.1.1.1.1
  exact ⟨w, hw, by unfold OkD.At.withU; rw [hw]; rfl⟩

example (c : Codes) (S : LinShape) : OkD.At.ofBlock "LIN point" c S = OkD.At.linPoint c S := rfl
example (c : Codes) (S : LinShape) : OkD.At.ofBlock "LIN p0int" c S = true := rfl

end Desc.K14.Law
