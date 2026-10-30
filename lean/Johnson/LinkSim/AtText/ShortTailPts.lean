-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/ShortTailPts.lean: one half of the premise of the negative test
short_tail_fails follows from a condition on the opened positions alone.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. short_tail_fails (Johnson/LinkSim/AtText/ShortTail.lean) has the premise
PtsFull: the positions at which the first tree is opened give as many distinct points as the mask
code's tail is long. This file proves PtsFull, for all parameters, from a condition on those
positions.
  ptsFull_of_nodup   PtsFull holds wherever the mask code is at most 2 ^ 32 long, and the
                     positions at which the first tree is opened are as many as its tail is long
                     and distinct modulo its length.
  ptG_inj            for a up to 32, distinct positions below 2 ^ a have distinct points.
ptG_inj uses toF_point_inj (OnBytes/Slice/Points.lean).

How it fits. ShortTailAtFull.lean applies ptsFull_of_nodup at the full size.

Limits.
- The other half of that premise, that the last entry of the explicit shift of the tail of the row
  beside the two folded rows (shPsi) is not 0, is not touched here: short_tail_fails stays
  conditional.
- How often the verifier's challenges meet the condition is not said here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.ShortTail
import OnBytes.Slice.Points

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice
open _root_.Desc.K15 (P15)

/-- For a up to 32, different positions below 2 ^ a have different points. -/
theorem ptG_inj (a : ℕ) (ha : a ≤ 32) {x y : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ a)
    (h : ptG a x = ptG a y) : x = y :=
  toF_point_inj a ha hx hy ((algebraMap GF GE).injective h)

/-- PtsFull holds when the mask code is at most 2 ^ 32 long and the first tree's opened positions
are as many as its tail is long and distinct modulo its length. -/
theorem ptsFull_of_nodup (P : P15) (S : Sz) (D : ℕ → Fmt.Drawn) (ha : S.P.Z.a ≤ 32)
    (hl : (q0 P D).length = S.P.Z.r) (hn : ((q0 P D).map (· % 2 ^ S.P.Z.a)).Nodup) :
    PtsFull P S D := by
  unfold PtsFull
  have e : (q0 P D).map (fun y => ptG S.P.Z.a (y % 2 ^ S.P.Z.a)) =
      ((q0 P D).map (· % 2 ^ S.P.Z.a)).map (ptG S.P.Z.a) := by
    rw [List.map_map]
    rfl
  have hlt : ∀ x ∈ (q0 P D).map (· % 2 ^ S.P.Z.a), x < 2 ^ S.P.Z.a := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [e, List.toFinset_card_of_nodup
    (hn.map_on fun x hx y hy h => ptG_inj _ ha (hlt x hx) (hlt y hy) h),
    List.length_map, List.length_map, hl]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.ptG_inj
#print axioms OnBytes.LinkSim.AtText.ptsFull_of_nodup
