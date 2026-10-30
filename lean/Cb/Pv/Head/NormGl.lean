-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/NormGl.lean: the soundness properties of the final norm's chains over the protocol's
challenge field.

The theorems hNorm (Cb/Pv/Head/Norm.lean) and hNorm2 (Cb/Pv/Head/Norm2.lean) ask that 2 is not 0 in
the field. Here that is shown of the challenge field Cb.Gl.E, whose characteristic is the prime
2^64 - 2^32 + 1, and the two properties are stated over it without that premise.

Main theorems: gl_two_ne_zero, hNorm_gl, hNorm2_gl.

What is not claimed. As in Norm.lean and Norm2.lean.


-/
import Cb.Pv.Head.Norm2
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head
open Iop Inst.Model

/-- 2 is not 0 in the challenge field. -/
theorem gl_two_ne_zero : (2 : Cb.Gl.E) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : Cb.Gl.E) = 0 := by exact_mod_cast h
  have hd : Cb.Gl.p ∣ 2 := (CharP.cast_eq_zero_iff Cb.Gl.E Cb.Gl.p 2).1 h2
  have hle : Cb.Gl.p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  have hp : Cb.Gl.p = 18446744069414584321 := Code.pGold_eq
  rw [hp] at hle
  exact absurd hle (by norm_num)

section
variable {J P M Wp Kc : Type} [Fintype J] [DecidableEq J]
variable (np : NormPar) (limb : (J → Cb.Gl.E) → ℕ → ℕ → Cb.Gl.E)
  (dig : (J → Cb.Gl.E) → ℕ → ℕ → Cb.Gl.E)
variable (Ex : ExtSpec) (msg : M → J → Cb.Gl.E) (Q : IOR.Rels Kc P Ex (M × Wp))

/-- The chain up to the round LINE, over the challenge field. -/
theorem hNorm_gl (slot : ℕ → J) : HNorm np limb dig slot Ex msg Q :=
  hNorm np limb dig slot Ex msg Q gl_two_ne_zero

/-- The chain up to the token sumcheck of the row products, over the challenge field. -/
theorem hNorm2_gl (msk : ℕ → J) : HNorm2 np limb dig msk Ex msg Q :=
  hNorm2 np limb dig msk Ex msg Q gl_two_ne_zero

end

end Cb.Pv.Head

#print axioms Cb.Pv.Head.gl_two_ne_zero
#print axioms Cb.Pv.Head.hNorm_gl
#print axioms Cb.Pv.Head.hNorm2_gl
