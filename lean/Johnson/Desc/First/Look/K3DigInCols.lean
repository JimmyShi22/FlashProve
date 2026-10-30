-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigInCols.lean: the lookup on the
digits of a segment's approximate range proof: WHAT IT PROVES OF THE WITNESS (DgP.DigIn: every entry
of ZZ's low half is a low digit, every entry of its high half a high one, column by column) SAID AS
THE APPROXIMATE RANGE PROOF's ROW SPENDS IT: matrix by matrix, row of cells by row of cells, at the
columns that the verifier's own zzCol gives. One theorem. NO SOUNDNESS IS CLAIMED.

Main name.
  digIn_digitsOf: DgP.colsTest tl = true → DgP.DigIn tl en ν → DigitsOf tl (fun t u c => ν (en (t,
    u, c))) (Johnson/Desc/First/K8/DigitsOf.lean: the approximate range proof's authors' own
    definition, in a light file).
HOW. A re-indexing: the column of (μ, i) is off μ + i, below mz under colsTest (dgP_col_lt,
OnBytes/Tie/Pv/Lookup/Digits/PortCols.lean). The two tables' sizes are 2 ^ t2D0 and 2 ^ t2D1 by the
make of sizeOf (OnBytes/Tie/Pv/Tail/SizeOf.lean).
OBJECT. No block's text: two sentences on a reading ν of entries.
USER. Whoever spends constr m lookDigits (digitsPart_at, K3FillDigits.lean, hands DigIn):
K3DigitsOfAt.lean.
LETTERS. tl, en, ν.
IS IT EMPTY? colsTest is a Bool on the approximate range proof's parameters tl, as the plan has
them: IT IS NO CONJUNCT OF digB: evaluated by us at no stored set.

Compiled with the whole library.
Limits. One way alone (the way the spender needs). That the spender's table of cells is fun t u c =>
ν (en (t, u, c)) at the array ZZ is its authors' one equation: not said here.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Digits.PortKnow
import OnBytes.Tie.Pv.Lookup.Digits.PortCols
import Johnson.Desc.First.K8.DigitsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model

/-- **DigIn, matrix by matrix.** -/
theorem digIn_digitsOf {J : Type} (tl : HTailF2) (en : DgP.Ent3 → J) (ν : J → Cb.Gl.E)
    (hc : DgP.colsTest tl = true) (h : DgP.DigIn tl en ν) :
    Desc.First.K8.DigitsOf tl (fun t u c => ν (en (t, u, c))) := by
  intro μ hμ u hu i hi
  have hlt : DgP.offOf tl μ + i < tl.mz := DgP.dgP_col_lt hc hμ hi
  have h0 : 0 < (tl.mats.getD μ {}).m := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have z0 : (tl.zzCol μ 0 0).getD 0 = DgP.offOf tl μ := by
    unfold HTailF2.zzCol
    simp only [hμ, h0, decide_true, Bool.and_self, if_true, Nat.zero_le, Nat.zero_mul,
      Nat.zero_add, Nat.add_zero]
    rfl
  have z1 : (tl.zzCol μ 1 0).getD 0 = tl.mz + DgP.offOf tl μ := by
    unfold HTailF2.zzCol
    simp only [hμ, h0, decide_true, Bool.and_self, if_true, Nat.le_refl, Nat.one_mul,
      Nat.add_zero]
    rfl
  refine ⟨?_, ?_⟩
  · rw [z0]
    exact h.1 (⟨DgP.offOf tl μ + i, hlt⟩, ⟨u, hu⟩)
  · rw [z1, Nat.add_assoc]
    exact h.2 (⟨DgP.offOf tl μ + i, hlt⟩, ⟨u, hu⟩)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digIn_digitsOf
