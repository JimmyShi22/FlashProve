-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Join.lean: the coefficients of the two forms that are no
single slot: the form behind a level, and the one claim on the planes' roots. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there form, slot, level and planes. In this file: `sc` and `vl`
are the coefficient and the reading of Honest/K3/Good/Coef.lean; `lineForm` is the form behind a
level (Honest/K3/Good/Levels.lean); `joinForm` is the claim on the planes' roots
(Honest/K3/Law/Forward.lean).

What is shown.
  `sc_line`, `sc_line_first`, `sc_line_second`: the form behind a level: 1 - xi on its first slot,
    xi on its second.
  `sum_single`: a sum with one term that is not 0.
  `sc_join`: the claim on the planes' roots: on the slot of plane j the equality weight of j, where
    the slots differ.
  `eqW_ne`, `weight_ne`: no equality weight is 0 at a point none of whose coordinates is 0 or 1.
Helpers: `vl_sub`, `sc_join_fold`.

Hypotheses that remain.
  `h0`, `hp`, `inj`: (in `sc_join`) j0 is a plane's number; there are at most 2 ^ mu planes; no
    other plane has the slot of plane j0.
  `hj`, `hx`: (in `weight_ne`) j < 2 ^ (the point's number of coordinates); no coordinate reads as 0
    or 1.
  Without a name, in front of arrows: in `sum_single`: no member twice; j0 is a member; every other
    term is 0; in `eqW_ne`: r is not 0, and no coordinate is 0 or 1.

Users. Honest/K3/Good/Walk.lean imports this file.

Limits. Rules on two forms.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Trees
import Johnson.Desc.First.Look.KeyLaw.Mid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Aff Reading eqTab)
open ProofFile.Honest.K3.Forward (joinForm)
open Lk6.PortSim (eqW)

/-! ## The form behind a level -/

theorem vl_sub (a b : E) : vl (subE a b) = vl a - vl b := Reading.gl.sub a b

theorem sc_line (sE : Nat) (xi : E) (j : Nat) :
    sc (lineForm sE xi) j =
      (1 - vl xi) * (if sE = j then 1 else 0) + vl xi * (if sE + 1 = j then 1 else 0) := by
  unfold lineForm
  rw [sc_add, sc_scale, sc_scale, sc_slot, sc_slot, vl_sub, vl_one]

theorem sc_line_first (sE : Nat) (xi : E) : sc (lineForm sE xi) sE = 1 - vl xi := by
  rw [sc_line, if_pos rfl, if_neg (by omega)]
  ring

theorem sc_line_second (sE : Nat) (xi : E) : sc (lineForm sE xi) (sE + 1) = vl xi := by
  rw [sc_line, if_neg (by omega), if_pos rfl]
  ring

/-! ## The claim on the planes' roots -/

theorem sum_single (t : Nat → GE) (j0 : Nat) : ∀ (l : List Nat), l.Nodup → j0 ∈ l →
    (∀ j ∈ l, j ≠ j0 → t j = 0) → (l.map t).sum = t j0
  | [], _, h, _ => by simp at h
  | a :: l, hn, hm, hz => by
    rw [List.map_cons, List.sum_cons]
    obtain ⟨hna, hnl⟩ := List.nodup_cons.1 hn
    by_cases ha : a = j0
    · subst ha
      have : (l.map t).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        exact hz x (List.mem_cons_of_mem _ hx) (fun e => hna (e ▸ hx))
      rw [this, add_zero]
    · have hm' : j0 ∈ l := by
        rcases List.mem_cons.1 hm with h1 | h1
        · exact absurd h1.symm ha
        · exact h1
      rw [hz a (by simp) ha, zero_add]
      exact sum_single t j0 l hnl hm' (fun j hj => hz j (List.mem_cons_of_mem _ hj))

theorem sc_join_fold (f : LFace) (sG : Array Nat) (ej : Array E) (x : Nat) : ∀ (l : List Nat)
    (c : Aff),
    sc (l.foldl (fun (c : Aff) j =>
      if j < f.planes then Aff.addMul c (Aff.slot (sG.getD j 0)) (ej.getD j zeroE)
      else c + Aff.ofConst (ej.getD j zeroE)) c) x =
      sc c x + (l.map fun j =>
        if j < f.planes ∧ sG.getD j 0 = x then vl (ej.getD j zeroE) else 0).sum
  | [], c => by simp
  | j :: l, c => by
    rw [List.foldl_cons, sc_join_fold f sG ej x l, List.map_cons, List.sum_cons]
    by_cases hj : j < f.planes
    · rw [if_pos hj, sc_addMul, sc_slot]
      by_cases hx : sG.getD j 0 = x
      · rw [if_pos hx, if_pos ⟨hj, hx⟩]
        ring
      · rw [if_neg hx, if_neg (fun h => hx h.2)]
        ring
    · rw [if_neg hj, sc_add, sc_ofConst, if_neg (fun h => hj h.1)]
      ring

/-- **On plane j0's slot the claim on the planes' roots has the equality weight of j0**, where no
other real plane has that slot. -/
theorem sc_join (f : LFace) (sG : Array Nat) (rho : Array E) {j0 : Nat} (h0 : j0 < f.planes)
    (hp : f.planes ≤ 2 ^ f.mu) (inj : ∀ j, j < f.planes → sG.getD j 0 = sG.getD j0 0 → j = j0) :
    sc (joinForm f sG rho) (sG.getD j0 0) = vl ((eqTab rho).getD j0 zeroE) := by
  unfold joinForm
  rw [sc_join_fold, sc_ofConst, zero_add,
    sum_single _ j0 _ List.nodup_range (List.mem_range.2 (by omega))
      (fun j _ hne => if_neg (fun h => hne (inj j h.1 h.2))),
    if_pos ⟨h0, rfl⟩]

/-! ## The weights -/

theorem eqW_ne : ∀ (xs : List GE) (j : Nat) (r : GE), r ≠ 0 → (∀ x ∈ xs, x ≠ 0 ∧ x ≠ 1) →
    eqW xs j r ≠ 0
  | [], _, _, hr, _ => hr
  | x :: xs, j, r, hr, hx => by
    show eqW xs (j / 2) (r * (if j % 2 == 1 then x else 1 - x)) ≠ 0
    refine eqW_ne xs _ _ (mul_ne_zero hr ?_) (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    obtain ⟨h0, h1⟩ := hx x (by simp)
    split
    · exact h0
    · exact sub_ne_zero.2 (Ne.symm h1)

/-- **No equality weight is 0** at the reverse of a list of coordinates none of which is 0 or 1. -/
theorem weight_ne (x : Array E) {j : Nat} (hj : j < 2 ^ x.size)
    (hx : ∀ y ∈ x.toList, vl y ≠ 0 ∧ vl y ≠ 1) : vl ((eqTab x.reverse).getD j zeroE) ≠ 0 := by
  have e := VerifiableInference.Desc.K3.KeyLaw.eqTab_read x j hj
  show OnBytes.Slice.readE _ ≠ 0
  rw [e]
  refine eqW_ne _ _ _ one_ne_zero ?_
  intro y hy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  exact hx z hz

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.vl_sub
#print axioms ProofFile.Honest.K3.Good.sc_line
#print axioms ProofFile.Honest.K3.Good.sc_line_first
#print axioms ProofFile.Honest.K3.Good.sc_line_second
#print axioms ProofFile.Honest.K3.Good.sum_single
#print axioms ProofFile.Honest.K3.Good.sc_join_fold
#print axioms ProofFile.Honest.K3.Good.sc_join
#print axioms ProofFile.Honest.K3.Good.eqW_ne
#print axioms ProofFile.Honest.K3.Good.weight_ne
