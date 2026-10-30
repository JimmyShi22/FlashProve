-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Exp/Digest.lean: **the digest of the verifier's table of exponentials, at S = 12 and
rx = 8, is 32 written bytes**: `exp_digest`: where `Attention.expTable 12 8` returns Tt,
`secondHashFunction 72` of the bytes that `tableHeld` and `tableHeldO` make of Tt is `D` (Closed.lean).
`exp_returns`: and it does return such a Tt.
How. `tableDigest_list`; `OnBytes.Road.L5.expTable_ref` (Johnson/Road/Lane5AttExp.lean): the table's
entries are the list `refL` of the library's stored words; `refL_eq`: that list is
`fromTo expW 0 2307`; one closed fact by Lean's kernel (Closed.lean).
Limits. At these numbers alone. That the stored full-size files give them, and that `D` is what the
parameter file's words `texp` spell, is not said here.

-/
import Johnson.Unfolds.Exp.Closed
import Johnson.Road.Lane5AttExp

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Unfolds.Exp
open OnBytes.Road.L5 (refL refL_length expTable_ref)

theorem refL_eq : refL = fromTo expW 0 2307 := by
  rw [fromTo_eq_map, ← List.range_eq_range']
  rfl

/-- The digest of any array whose entries are `refL`. -/
theorem digest_of_list (Tt : Array Nat) (h : Tt.toList = refL) :
    OnBytes.secondHashFunction 72 (Tt.foldl (fun b x => b ++ OnBytes.word32 x) ByteArray.empty) = D := by
  have hs : Tt.size = 2307 := by rw [← Array.length_toList, h, refL_length]
  rw [tableDigest_list, hs, h, refL_eq, digestL]

/-- **THE DIGEST OF THE TABLE OF EXPONENTIALS.** -/
theorem exp_digest (Tt : Array Nat) (h : OnBytes.Attention.expTable 12 8 = some Tt) :
    OnBytes.secondHashFunction 72 (Tt.foldl (fun b x => b ++ OnBytes.word32 x) ByteArray.empty) = D := by
  have e := expTable_ref
  rw [h] at e
  exact digest_of_list Tt (Option.some.inj e)

/-- **And the table returns**: so `exp_digest` is not empty. -/
theorem exp_returns : ∃ Tt, OnBytes.Attention.expTable 12 8 = some Tt ∧
    OnBytes.secondHashFunction 72 (Tt.foldl (fun b x => b ++ OnBytes.word32 x) ByteArray.empty) = D := by
  obtain ⟨Tt, h, -⟩ := Option.map_eq_some_iff.1 expTable_ref
  exact ⟨Tt, h, exp_digest Tt h⟩

end Johnson.Unfolds.Exp

#print axioms Johnson.Unfolds.Exp.refL_eq
#print axioms Johnson.Unfolds.Exp.digest_of_list
#print axioms Johnson.Unfolds.Exp.exp_digest
#print axioms Johnson.Unfolds.Exp.exp_returns
