-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WorldTie.lean: K06Statement.lean's `atWorld` IS THE LIBRARY's VALUE OF A FORM IN THE LIBRARY's
WORLD OF A LEDGER. `worldE_eq`: K06Glue.lean's
`worldE F mask ent` is HideLaws.lean's `Fork.worldOf` at the reading in the field, the mask entries
and the sent reads read there. `rd_atWorld_landed`: so `atWorld F mask ent f`, read in the field, is
`Aff.value` of f in that world: the world of which the rule of composition's files, the masked
sumcheck's law and the ledger's lemma speak.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06Glue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork Reading World)

/-- The two defaults are read alike. -/
theorem rd_getD (a : Array E) (j : Nat) : rd (a.getD j (0 : E)) = rd (a.getD j zeroE) := by
  by_cases h : j < a.size
  · simp [Array.getD, h]
  · simp only [Array.getD, h, dif_neg, not_false_eq_true]
    rw [rd_zero]
    exact Reading.gl.zero.symm

theorem worldE_eq (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) :
    worldE F mask ent
      = F.worldOf Reading.gl (fun j => rd (mask j)) (fun t r i => rd (ent t r i)) := by
  have hs : (fun j => rd (hidden F mask j)) = fun j =>
      Reading.gl.val (F.vp.getD j zeroE) - Reading.gl.val (F.mf.getD j zeroE) * rd (mask j) := by
    funext j
    unfold hidden
    rw [rd_sub, rd_mul, rd_getD, rd_getD]
    rfl
  unfold worldE Fork.worldOf
  rw [hs]

/-- **atWorld, read in the field, is the library's value in the library's world.** -/
theorem rd_atWorld_landed (F : Fork) (mask : Nat → E) (ent : Nat → Nat → Nat → E) (f : Form) :
    rd (atWorld F mask ent f) = Aff.value Reading.gl
      (F.worldOf Reading.gl (fun j => rd (mask j)) (fun t r i => rd (ent t r i))) f := by
  rw [rd_atWorld, worldE_eq]
  rfl

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.rd_atWorld_landed
