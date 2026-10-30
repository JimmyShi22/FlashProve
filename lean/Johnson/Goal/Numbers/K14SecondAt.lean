-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K14SecondAt.lean: the kind K14's second part
(Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean: batchLinearConstraintsSecondPart, the first block of the last chain), at the release's
numbers: it has no round, and its test on the plan says yes.

The kind K14 has the linear claim's shared part and a second part.
Johnson/Goal/Numbers/K14CondAt.lean and K14RoundsAt.lean speak of the
shared part. Here the second.
  second_no_round: the block declares no round, names no oracle and fixes nothing: so the verifier
      draws nothing in it, and no error and no work is to be counted
  secondB: its test on the plan, as a function of the codes and the shape: the codes' message
      lengths are powers of two; the shape is lawful at the codes; it does not split the row (Dot)
  second_planOk: the block's test on the plan is that function
  real_test2, key_test2: it says yes: evaluations in Lean's kernel (decide +kernel)
  K14SecondAt codes S: at every parameter with these codes and this shape: no round, and the test on
      the plan says yes
  k14_second_real, k14_second_key, k14_second_key_at_scope
  teeth2: at no codes the test says no

What is not claimed. The last chain's other rounds: they are the own test's (K12) and its code
switches' sendings (K1: Johnson/Desc/K1/Law/CondReal.lean ties the proof file's four, K01KeyAt.lean
the key file's four, to their records). The law of the block's decision. That the typed numbers are
the parameters at a description's own place. With which parameters a description of a key file calls
the block. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K01KeyAt
import Johnson.Desc.Third.K14BatchLinearConstraintsSecondPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third
open OnBytes OnBytes.Params OnBytes.Params.Prices Johnson.G
open VerifiableInference.Desc.K1 (realSized k01_real)
open Lk6.AtPlan (keyFull key_eq_at_scope)

/-- The block has no round. -/
theorem second_no_round {Cl : Type} (p : P₁₄) :
    (batchLinearConstraintsSecondPart (Cl := Cl) p).rounds = [] ∧ (batchLinearConstraintsSecondPart (Cl := Cl) p).oracles = [] ∧
      (batchLinearConstraintsSecondPart (Cl := Cl) p).before = [] := ⟨rfl, rfl, rfl⟩

/-- Its test on the plan. -/
def secondB (codes : Codes) (S : LinShape) : Bool :=
  codes.lengthsOk && linOk codes S && plainArm S

theorem second_planOk {Cl : Type} (p : P₁₄) :
    (batchLinearConstraintsSecondPart (Cl := Cl) p).planOk = secondB p.codes p.S := rfl

/-- **The second part at codes and a shape.** -/
def K14SecondAt (codes : Codes) (S : LinShape) : Prop :=
  ∀ (Cl : Type) (p : P₁₄), p.codes = codes → p.S = S →
    (batchLinearConstraintsSecondPart (Cl := Cl) p).rounds = [] ∧ (batchLinearConstraintsSecondPart (Cl := Cl) p).planOk = true

theorem secondAt_of {codes : Codes} {S : LinShape} (h : secondB codes S = true) :
    K14SecondAt codes S := fun Cl p h1 h2 => by
  refine ⟨rfl, ?_⟩
  rw [second_planOk, h1, h2]
  exact h

theorem real_test2 : (realSized.any fun p => secondB p.2 p.1.shape) = true := by decide +kernel

theorem key_test2 : secondB keyFull.codes keyFull.once.shape = true := by decide +kernel

/-- **In a proof file.** -/
theorem k14_second_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    K14SecondAt codesFull2 x.shape := by
  obtain ⟨x, -, -, a1, a2, -⟩ := k01_real
  have h := real_test2
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, a2, secondAt_of h⟩

/-- **In a key file.** -/
theorem k14_second_key : K14SecondAt keyFull.codes keyFull.once.shape := secondAt_of key_test2

theorem k14_second_key_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    K14SecondAt p.chains.made.sized.key.codes p.chains.made.sized.key.once.shape := by
  rw [key_eq_at_scope hZ hp]
  exact k14_second_key

/-- The test can say no: at no codes. -/
theorem teeth2 : secondB {} keyFull.once.shape = false := by decide +kernel

end VerifiableInference.Desc.Third
