-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Bridge/GlCodesProvedCheck.lean: what Lean reports about `Cb.Gl.bchks46At` and about the two
theorems adapted from ArkLib (ThirdParty/ArkLib) on which it rests, checked when this file compiles.
Every #check and #print axioms below stands under #guard_msgs. So the build fails if a statement
prints differently, or if a proof depends on anything besides Lean's three standard axioms (propext,
Classical.choice, Quot.sound). A guard that passes prints nothing: the doc comment above each
command is Lean's output. No guard says that an adapted statement says what its source says: AI
systems adapted the files under ThirdParty/ from ArkLib and Mathlib (lean/LIMITS.md, L15).

-/
import Cb.Bridge.GlCodesProved

/-- Lean must accept `Cb.Gl.bchks46At` as a proof of the statement under its name. -/
example : Cb.BCHKS46At Cb.Gl.F Cb.Gl.E := Cb.Gl.bchks46At

/-- The statement at the two fields, with the body of `Cb.BCHKS46At` written out. Lean must accept
`Cb.Gl.bchks46At` as a proof of it. So this file stops compiling if that definition is changed to
say something else. (`Cb.OnRS`, `Cb.bchksBound` and `Prob.cnt` stand under their names.) -/
example : ∀ (n k e : ℕ) (x : Fin n → Cb.Gl.F), Function.Injective x → 0 < k → 0 < e →
    n * k < (n - e) ^ 2 →
    ∀ u₀ u₁ : Fin n → Cb.Gl.E,
      (Prob.cnt (fun z : Cb.Gl.E => ∃ A : Finset (Fin n), n ≤ A.card + e ∧
        Cb.OnRS (fun j => algebraMap Cb.Gl.F Cb.Gl.E (x j)) k (fun j => u₀ j + z * u₁ j) A ∧
        ¬ (Cb.OnRS (fun j => algebraMap Cb.Gl.F Cb.Gl.E (x j)) k u₀ A ∧
          Cb.OnRS (fun j => algebraMap Cb.Gl.F Cb.Gl.E (x j)) k u₁ A)) : ℝ) ≤
        Cb.bchksBound n k e :=
  Cb.Gl.bchks46At

set_option pp.fullNames true in
/--
info: Cb.Gl.bchks46At : Cb.BCHKS46At Cb.Gl.F Cb.Gl.E
-/
#guard_msgs (whitespace := lax) in
#check @Cb.Gl.bchks46At

set_option pp.fullNames true in
/--
info: Cb.Bridge.bchks46At : ∀ (F E : Type) [inst : Field F] [inst_1 : Field E] [inst_2 : Finite E]
[inst_3 : Algebra F E],
  Cb.BCHKS46At F E
-/
#guard_msgs (whitespace := lax) in
#check @Cb.Bridge.bchks46At

set_option pp.fullNames true in
/--
info: Cb.Bridge.bchks46 : Cb.BCHKS46
-/
#guard_msgs (whitespace := lax) in
#check @Cb.Bridge.bchks46

/--
info: 'Cb.Gl.bchks46At' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cb.Gl.bchks46At

/--
info: 'Cb.Bridge.bchks46At' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cb.Bridge.bchks46At

/--
info: 'Cb.Bridge.bchks46' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cb.Bridge.bchks46

/--
info: 'Cb.Bridge.lineFact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cb.Bridge.lineFact

/--
info: 'Cb.Bridge.bchks46_of_lineFact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cb.Bridge.bchks46_of_lineFact

/--
info: 'Cb.Bridge.arkLibEstimate_eq_bchksBound' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cb.Bridge.arkLibEstimate_eq_bchksBound

/--
info: 'ReedSolomon.exists_johnson_line_exactCorrelatedPair' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_johnson_line_exactCorrelatedPair

/--
info: 'ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate
