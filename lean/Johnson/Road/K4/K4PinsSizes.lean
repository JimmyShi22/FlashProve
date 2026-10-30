-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsSizes.lean: TWO MORE FIELDS OF `K4PlanFit` (Johnson/Road/K4/K4PinsEnd.lean)
THAT ARE NO TESTS AT THE RIGHT LETTERS: size, at s := the meaning's authors' own sizes off the
public parameters (`Meaning.sizesOf X`, Johnson/Goal/Meaning/HidPlan.lean); covers, at the least
bounds that the smallness test's structure allows. By unfolding. No draw, no count.

  **`size_sizesOf`**: `szOf p.hp.tl = Meaning.sizesOf X (2 * p.g)`, from: X's plan of group p.g is
    p.hp · p.g < 12.
  **`covers_top`**: `Covers tl nM nR nC` at nM := tl's number of matrices, nR := the greatest number
    of rows, nC := the greatest number of columns among them.

OBJECT: none of its own. USER: none yet; meant: the assembly of K4's law: it may fill the letters s,
nM, nR, nC of `k4_own_end` so. LETTERS: X, p, tl: free.

Limits. K04_law IS NOT PROVED BY THIS. THAT THE LETTERS s, nM, nR, nC ARE FILLED SO IS THE
ASSEMBLY's CHOICE: s is shared with `SymsOne`, `SeamFit` and the equation on what the prover hides
(`K4MeanEqs`' field hidIs): they must be met at the same s.
-/
import Johnson.Road.K4.K4PinsPlanes
import Johnson.Goal.Meaning.HidPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Model (HTailF2)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First.Look (cellJ szOf)

/-- **The field size, at the meaning's authors' own sizes.** -/
theorem size_sizesOf {X : Public} {p : Par} (hG : X.G[p.g]? = some p.hp) (hg : p.g < 12) :
    szOf p.hp.tl = _root_.Meaning.sizesOf X (2 * p.g) := by
  unfold _root_.Meaning.sizesOf _root_.Meaning.tlAt
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    Nat.mul_div_cancel_left _ (by decide), hG]
  rfl

/-- **The field covers, at the least bounds.** -/
theorem covers_top (tl : HTailF2) :
    Covers tl (szOf tl).NM ((Finset.range (szOf tl).NM).sup (szOf tl).m)
      ((Finset.range (szOf tl).NM).sup (szOf tl).k) := by
  intro a r c hs
  unfold cellJ at hs
  by_cases hc : a < (szOf tl).NM ∧ c < (szOf tl).k a ∧ r < (szOf tl).m a
  · exact ⟨hc.1,
      Nat.lt_of_lt_of_le hc.2.2 (Finset.le_sup (f := (szOf tl).m) (Finset.mem_range.2 hc.1)),
      Nat.lt_of_lt_of_le hc.2.1 (Finset.le_sup (f := (szOf tl).k) (Finset.mem_range.2 hc.1))⟩
  · rw [dif_neg hc] at hs
    exact absurd hs Bool.false_ne_true

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.size_sizesOf
#print axioms OnBytes.Road.K4.covers_top
