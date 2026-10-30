-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Order/E3O65.lean.
The orders of a small whole lookup of the key file's kind (16 keys, 2 rows, 8 planes), as terms.

ordKeyW is the key file's rule as one total function of the public numbers. o65K, o65T, o65E, o65B
are the orders of the key levels, the table's level, the leaves and the bits at that size, with
variable 1 named for the last key level. In these names 65 is the length of TwPlan.entN at that size
(OnBytes/Tie/Pv/Lookup/Lists/TwPlan.lean, v' = 3, d = 1, w = 3, n = 6); no statement here says so.
The lists of bound variables are evaluated, and five lemmas say that the orders of key level 2, of
the table's level and of the leaves are not the identity, and that the order of the last key level
is neither the identity nor the reversal.
Limits: where the named variables are not lawful the program refuses the public inputs
(Public.orderOK); ordKeyW gives the reversal there. That ordKeyW is the program's choice
(`levelChain`, OnBytes/Iop/Lkp.lean) is read off its text: no statement here says so.

-/
import OnBytes.Tie.Pv.Lookup.Port.E3OrdKey
set_option autoImplicit false
namespace E3

/-- The rule of the key file's lookup (`levelChain`, OnBytes/Iop/Lkp.lean): at the last key level
the named variables first, elsewhere from the highest down. Where the names are not lawful
(Public.orderOK) the program refuses; here the reversal stands. -/
def ordKeyW (v : ℕ) (first : List ℕ) (k : ℕ) : Equiv.Perm (Fin k) :=
  if h : k + 1 = v ∧ (∀ j ∈ first, j < k) ∧ first.Nodup then ordBegin first k h.2.1 h.2.2 else
      ordDefault k

def o65K (l : ℕ) : Equiv.Perm (Fin (0 + l)) := ordKeyW 4 [1] (0 + l)
def o65T (l : ℕ) : Equiv.Perm (Fin (3 + l)) := ordDefault (3 + l)
def o65E : Equiv.Perm (Fin (3 + 1)) := ordDefault (3 + 1)
def o65B : Equiv.Perm (Fin (3 + 1)) := ordDefault (3 + 1)

/-- round by round: which variable is bound -/
def asList {k : ℕ} (σ : Equiv.Perm (Fin k)) : List ℕ := (List.finRange k).map fun j => ((σ j : Fin
    k) : ℕ)

-- which variables are bound, round by round
example : asList (o65K 0) = [] := by decide
example : asList (o65K 1) = [0] := by decide
example : asList (o65K 2) = [1, 0] := by decide
example : asList (o65K 3) = [1, 2, 0] := by decide
example : asList (o65T 0) = [2, 1, 0] := by decide
example : asList o65E = [3, 2, 1, 0] := by decide
example : asList o65B = [3, 2, 1, 0] := by decide

-- The order at key level 2 is not the identity; at the last key level it is neither the identity
-- nor the reversal; at the table's level and at the leaves it is not the identity.
theorem o65K_two_ne_one : o65K 2 ≠ 1 := by decide
theorem o65K_last_ne_one : o65K 3 ≠ 1 := by decide
theorem o65K_last_ne_rev : o65K 3 ≠ Fin.revPerm := by decide
theorem o65T_ne_one : o65T 0 ≠ 1 := by decide
theorem o65E_ne_one : o65E ≠ 1 := by decide

end E3
