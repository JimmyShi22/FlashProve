-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ClaimsNums.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: FOUR FACTS ON NUMBERS
THAT THE TEST claimsB NEEDS, EACH OFF A TEST OF THE PROGRAM's OWN FUNCTIONS. Where `layout` returns:
a group has at most 2 ^ 6 layers (`ll_le_six`: the layout's second test refuses more); so the plan's
function for the number of weight claims, `nclOf`, is at most 4096 (`ncl_le`); and a block's bits
are at most the bits of the model's width (`ls_le_lPd`). Where `wsLayOf` returns: the vocabulary is
not empty (`vocab_pos`: its second test asks that the vocabulary's size has at least one bit).
Statements and proofs. General in the sizes.

  `ll_le_six_base`, `ll_le_six`   h.ll ≤ 6.
  `ncl_le`      nclOf y g ≤ 4096.
  `ls_le_lPd`   y.ls ≤ y.lPd.
  `vocab_pos`   0 < s.V.

Not shown here. That either function returns at any shape: hypotheses. Public numbers alone.
No property is claimed.
-/
import Johnson.Road.K4.PlanClauses
import Johnson.Road.FormsKeysLaid
import Johnson.Road.FormsKeysWLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay layout layoutBase nclOf)

/-- The first half of the layout refuses a group of more than 2 ^ 6 layers. -/
theorem ll_le_six_base {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) : h.ll ≤ 6 := by
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e2, -⟩ := ok_of_refuse hy
  have a1 := or_false_split e2
  have a2 := or_false_split a1.1
  have a3 := or_false_split a2.1
  have a5 := or_false_split a3.1
  have a6 := or_false_split a5.1
  have a7 := or_false_split a6.1
  exact le_of_gt_false a7.2

/-- **A group has at most 2 ^ 6 layers.** CONDITIONAL: on the return. -/
theorem ll_le_six {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : h.ll ≤ 6 := by
  unfold layout at hy
  obtain ⟨y0, h0, -⟩ := ok_of_bind hy
  exact ll_le_six_base h0

/-- **The plan's function for the number of weight claims is at most 4096.** CONDITIONAL: on the
return. -/
theorem ncl_le {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (g : ℕ) : nclOf y g ≤ 4096 := by
  have L := OnBytes.Road.K4.laySizes_of_layout hy
  have h6 : 2 ^ h.ll ≤ 64 :=
    Nat.le_trans (Nat.pow_le_pow_right (by norm_num) (ll_le_six hy)) (by norm_num)
  have hM : y.LamM ≤ 64 := by
    rw [L.LamM]
    exact Nat.le_trans (Nat.div_le_self _ _) h6
  have hL : y.Lam ≤ 64 := by
    rw [L.Lam]
    exact h6
  unfold nclOf
  split_ifs <;> omega

/-- **A block's bits are at most the bits of the model's width.** CONDITIONAL: on the return. -/
theorem ls_le_lPd {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : y.ls ≤ y.lPd := by
  have M := OnBytes.Road.K4.layMore_of_layout hy
  rw [(OnBytes.Road.K4.laySizes_of_layout hy).lPd, OnBytes.Road.ceilLog2_eq_clog]
  exact OnBytes.Road.K4.le_clog_of_dvd M.bd M.d0

/-- **The vocabulary is not empty.** CONDITIONAL: on the return. -/
theorem vocab_pos {s : WsShape} {p3 : Bool} {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s p3 lk = .ok lay) : 0 < s.V := by
  unfold wsLayOf at h
  obtain ⟨-, h⟩ := okGuard h
  obtain ⟨g2, -⟩ := okGuard h
  have t : tokenFactorTaken s.V lk = true := by
    cases e : tokenFactorTaken s.V lk with
    | true => rfl
    | false =>
      rw [e] at g2
      exact absurd rfl g2
  unfold tokenFactorTaken at t
  rw [Bool.and_eq_true, decide_eq_true_eq] at t
  have t1 : 1 ≤ ceilLog2 s.V := t.1
  rcases Nat.eq_zero_or_pos s.V with e | e
  · rw [e, OnBytes.Road.ceilLog2_eq_clog, Nat.clog_zero_right] at t1
    omega
  · exact e

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.ll_le_six_base
#print axioms OnBytes.Road.K4.C.ll_le_six
#print axioms OnBytes.Road.K4.C.ncl_le
#print axioms OnBytes.Road.K4.C.ls_le_lPd
#print axioms OnBytes.Road.K4.C.vocab_pos
