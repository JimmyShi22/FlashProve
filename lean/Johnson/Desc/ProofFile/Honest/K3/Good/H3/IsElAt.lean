-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/IsElAt.lean: which elements of a round are drawn by the
even rule (`P1K8.IsEl`, Johnson/P1K8R/KitCount.lean; the term:
Honest/K3/Good/H3/Defs.lean), read off the entry's numbers. General in the entry.
Theorems on public data.

What is shown.
  `isEl_dsOf`: at a kind other than "seeds": the first drawE - drawNZ elements.
Helpers: `isEl_pos` (the positions in front are passed over), `isEl_elem`.

Hypotheses that remain. `hk`: the kind is not "seeds". `hi`: the number is below drawE - drawNZ.

Users. Honest/K3/Good/H3/FewOfCap.lean and LeafOfCap.lean.

Limits. One direction alone. Nothing at the kind "seeds". That the hypothesis `hi` is needed is
tried in Honest/K3/Good/H3/Teeth.lean [not in this library].
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.P1K8R.KitCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good

/-- Positions in front are passed over. -/
theorem isEl_pos (n k : ℕ) (ds : List Fmt.Draw) (i : ℕ) (h : P1K8.IsEl ds i) :
    P1K8.IsEl (List.replicate n (Fmt.Draw.pos k) ++ ds) i := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    exact ih

/-- A run of elements drawn by the even rule. -/
theorem isEl_elem (n : ℕ) (ds : List Fmt.Draw) :
    ∀ i, i < n → P1K8.IsEl (List.replicate n Fmt.Draw.elem ++ ds) i := by
  induction n with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    rw [List.replicate_succ, List.cons_append]
    cases i with
    | zero => exact trivial
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

/-- At a kind other than seeds, the first drawE - drawNZ elements of a round are drawn by the even
rule. -/
theorem isEl_dsOf (e : Fmt.Entry) (k : Fmt.Kind) (hk : k ≠ .seeds) (i : ℕ)
    (hi : i < e.drawE - e.drawNZ) : P1K8.IsEl (Fmt.dsOf e k) i := by
  unfold Fmt.dsOf Fmt.dsElems
  rw [if_neg hk]
  refine isEl_pos _ _ _ _ ?_
  rw [List.append_assoc]
  exact isEl_elem _ _ i hi

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.isEl_pos
#print axioms ProofFile.Honest.K3.Good.isEl_elem
#print axioms ProofFile.Honest.K3.Good.isEl_dsOf
