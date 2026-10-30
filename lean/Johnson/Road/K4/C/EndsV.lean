-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/EndsV.lean: how the honest side lays the weight claims' end values.

What is here. The layers' own rounds (sub-protocol K4), the prover's side, the batched sumcheck:
the loop in endsAt (Johnson/Desc/K4/Honest/Stack.lean) that lays the end values of the weight
claims writes each place once: where each panel's first weight claim has the running number (the
library's WalkL, Johnson/Road/K4/WalkV0.lean), the array holds at a panel's places what that
panel's step wrote. Definitions; statements and proofs.

  `vTri`, `vRow`    what is written for a panel with the selector; for row i of a panel without.
  `vStep`           one panel's step of the loop.
  `set_run`         a run of writes at v0, v0 + 1, ...
  `vStep_size`, `vStep_other`, `vStep_tri`, `vStep_row`   one step.
  **`walk_V`**        the whole loop.

Not shown here. What a value means: these are laws on a loop over the panels. That the panels'
numbers of their first weight claims are running sums (WalkL) is a premise.
No property is claimed.
-/
import Johnson.Road.K4.C.StackEnds
import Johnson.Road.K4.WalkV0
import Johnson.Road.FormsKeysQK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk)
open OnBytes.Road.K4 (WalkL incV)
open OnBytes.Desc.First.K4.Honest

/-- What is written for a panel with the selector. -/
def vTri (D : StackData) (rs : Array E) (b : SBlk) (v0 : ℕ) : E :=
  StackData.under (eqLow rs b.wy b.w) (eqLow rs 0 b.wy) b.ni b.ny
    (at2 (D.F.getD v0 #[]) (D.S.kkOf v0))

/-- What is written for row i of a panel without the selector. -/
def vRow (D : StackData) (rs : Array E) (b : SBlk) (v0 i : ℕ) : E :=
  StackData.under #[oneE] (eqLow rs 0 b.wy) 1 b.ny
    fun _ yv => at2 (D.F.getD (v0 + i) #[]) (D.S.kkOf (v0 + i)) 0 yv

/-- One panel's step of the loop that lays the weight claims' end values. -/
def vStep (D : StackData) (rs : Array E) (V : Array E) (b : SBlk) : Array E :=
  match b.v0 with
  | none => V
  | some v0 =>
    if b.tri then V.setIfInBounds v0 (vTri D rs b v0)
    else (List.range b.ni).foldl (fun V i => V.setIfInBounds (v0 + i) (vRow D rs b v0 i)) V

/-- A run of writes at v0, v0 + 1, ...: the size stays, the other places stay, and each place inside
the array holds what was written. -/
theorem set_run (v0 : ℕ) (g : ℕ → E) : ∀ (n : ℕ) (V : Array E),
    ((List.range n).foldl (fun V i => V.setIfInBounds (v0 + i) (g i)) V).size = V.size ∧
      (∀ j, j < v0 ∨ v0 + n ≤ j →
        ((List.range n).foldl (fun V i => V.setIfInBounds (v0 + i) (g i)) V).getD j zeroE =
          V.getD j zeroE) ∧
      ∀ i, i < n → v0 + i < V.size →
        ((List.range n).foldl (fun V i => V.setIfInBounds (v0 + i) (g i)) V).getD (v0 + i) zeroE =
          g i
  | 0, _ => ⟨rfl, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1, V => by
    obtain ⟨s, o, w⟩ := set_run v0 g n V
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [Array.size_setIfInBounds, s], fun j hj => ?_, fun i hi hb => ?_⟩
    · rw [getD_set_ne _ (by omega), o j (by omega)]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · rw [getD_set_ne _ (by omega), w i h hb]
      · rw [getD_set_self _ (by rw [s]; exact hb)]

variable (D : StackData) (rs : Array E)

/-- A step keeps the size. -/
theorem vStep_size (V : Array E) (b : SBlk) : (vStep D rs V b).size = V.size := by
  unfold vStep
  cases b.v0 with
  | none => rfl
  | some v0 =>
    dsimp only
    split_ifs
    · exact Array.size_setIfInBounds
    · exact (set_run v0 _ b.ni V).1

/-- A step leaves the places outside the panel's own. -/
theorem vStep_other (V : Array E) (b : SBlk) {j : ℕ}
    (h : ∀ v0, b.v0 = some v0 → j < v0 ∨ v0 + incV b ≤ j) :
    (vStep D rs V b).getD j zeroE = V.getD j zeroE := by
  unfold vStep
  cases h0 : b.v0 with
  | none => rfl
  | some v0 =>
    have hj := h v0 h0
    unfold incV at hj
    rw [h0] at hj
    dsimp only at hj ⊢
    by_cases ht : b.tri = true
    · rw [if_pos ht] at hj ⊢
      exact getD_set_ne _ (by omega) _
    · rw [if_neg ht] at hj ⊢
      exact (set_run v0 _ b.ni V).2.1 j hj

/-- The step of a panel with the selector. -/
theorem vStep_tri (V : Array E) {b : SBlk} (ht : b.tri = true) {v0 : ℕ} (h0 : b.v0 = some v0)
    (hb : v0 < V.size) : (vStep D rs V b).getD v0 zeroE = vTri D rs b v0 := by
  unfold vStep
  rw [h0]
  dsimp only
  rw [if_pos ht]
  exact getD_set_self _ hb _

/-- The step of a panel without the selector. -/
theorem vStep_row (V : Array E) {b : SBlk} (ht : b.tri = false) {v0 : ℕ} (h0 : b.v0 = some v0)
    {i : ℕ} (hi : i < b.ni) (hb : v0 + i < V.size) :
    (vStep D rs V b).getD (v0 + i) zeroE = vRow D rs b v0 i := by
  unfold vStep
  rw [h0]
  dsimp only
  rw [if_neg (by rw [ht]; exact Bool.false_ne_true)]
  exact (set_run v0 _ b.ni V).2.2 i hi hb

/-- **THE LOOP WRITES EACH PLACE ONCE**: where the panels' first weight claims have the running
numbers from n to n', and n' places are there: the places in front of n stay, and at each panel's
places stands what its own step wrote. -/
theorem walk_V : ∀ (l : List SBlk) (n n' : ℕ) (V : Array E), WalkL n l n' → n' ≤ V.size →
    n ≤ n' ∧ (∀ j, j < n → (l.foldl (vStep D rs) V).getD j zeroE = V.getD j zeroE) ∧
      ∀ b ∈ l, ∀ v0, b.v0 = some v0 →
        (b.tri = true → (l.foldl (vStep D rs) V).getD v0 zeroE = vTri D rs b v0) ∧
          (b.tri = false → ∀ i, i < b.ni →
            (l.foldl (vStep D rs) V).getD (v0 + i) zeroE = vRow D rs b v0 i)
  | [], n, n', _, h, _ => by
    have e : n = n' := h
    exact ⟨Nat.le_of_eq e, fun _ _ => rfl, fun b hb => absurd hb List.not_mem_nil⟩
  | b :: l, n, n', V, h, hs => by
    obtain ⟨hb0, hl⟩ : (∀ v0, b.v0 = some v0 → v0 = n) ∧ WalkL (n + incV b) l n' := h
    obtain ⟨r1, r2, r3⟩ := walk_V l (n + incV b) n' (vStep D rs V b) hl
      (by rw [vStep_size]; exact hs)
    rw [List.foldl_cons]
    refine ⟨by omega, fun j hj => ?_, fun c hc v0 h0 => ?_⟩
    · rw [r2 j (by omega)]
      exact vStep_other D rs V b fun v0 h0 => Or.inl (by rw [hb0 v0 h0]; exact hj)
    · rcases List.mem_cons.mp hc with rfl | hcl
      · have e := hb0 v0 h0
        subst e
        have hinc : incV c = if c.tri = true then 1 else c.ni := by
          unfold incV
          rw [h0]
        refine ⟨fun ht => ?_, fun ht i hi => ?_⟩
        · rw [if_pos ht] at hinc
          rw [r2 v0 (by omega)]
          exact vStep_tri D rs V ht h0 (by omega)
        · rw [if_neg (by rw [ht]; exact Bool.false_ne_true)] at hinc
          rw [r2 (v0 + i) (by omega)]
          exact vStep_row D rs V ht h0 hi (by omega)
      · exact r3 c hcl v0 h0

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.set_run
#print axioms OnBytes.Road.K4.C.vStep_size
#print axioms OnBytes.Road.K4.C.vStep_other
#print axioms OnBytes.Road.K4.C.vStep_tri
#print axioms OnBytes.Road.K4.C.vStep_row
#print axioms OnBytes.Road.K4.C.walk_V
