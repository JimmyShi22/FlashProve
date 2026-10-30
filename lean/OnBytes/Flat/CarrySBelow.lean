-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/CarrySBelow.lean: the written error counts of a reading of a file's rounds (`Maps.err`,
OnBytes/Flat/CarrySMaps.lean) are below the planner's target, under the two premises of
`Held.cnts_below_held` (OnBytes/Flat/CountsHeld.lean).

`Held.cnts_below_held` speaks of the shape `uL (ckP .two) ds` of written rounds with at most one
tree; a reading's counts stand at the shape `uLT (ckP .two) ds` of a file's rounds. `Err.Below`
reads of a round the number of its verifier messages alone, and a file's round d has those of `toRD
d`. So a bound passes from the one shape to the other. Proofs.

Main names:
  `card_wT`: a file's round has as many verifier messages as `toRD` of it.
  `Held.below_uLT`: `Err.Below` of `Held.cnts` passes from `uL (ckP .two) (ds.map toRD)` to `uLT
    (ckP .two) ds`.
  `Maps.below_held`: if the planner's rounds rs hold the written rounds pair by pair
    (`OnBytes.Slice.Held st r d`) and each typed count is at most the planner's number for its round
    (`Held.CountsL`), then `M.err ε` is below 2^(-st.target).
Limits: the two premises are asked, not shown: at no value here. The target counts a round's proof
of work: a round's written verifier messages include the strings of test bits, so of the target's
bits `work` are work (`held_round`, OnBytes/Slice/HeldRound.lean). `OnBytes.Slice.Held st r d` is
seven clauses (OnBytes/Slice/HeldKinds.lean): the format's field; degree 3; d has r's entry; `logN`
at most 64; drawNZ at most drawE; work + 66 ≤ target where the round draws an element; r holds in
the planner's reckoning. It is asked of every round, also of those that the reading skips. Nothing
on soundness.
-/
import OnBytes.Flat.CarrySFollows

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob _root_.Run _root_.Run.PQ OnBytes.Params OnBytes.Maker OnBytes.Slice
open scoped ENNReal

/-- A file's round has as many verifier messages as the round with at most one tree. -/
theorem card_wT (d : RDT) : Fintype.card (wT d).Chal = Fintype.card (wRound (toRD d)).Chal :=
  Fintype.card_congr (Equiv.refl _)

namespace Held

/-- A bound on the counts passes to the shape of a file's rounds. -/
theorem below_uLT : ∀ (ds : List RDT) (ws : List (Option ℕ)) (s' : Shape) (ε : Err s')
    (c : ℝ≥0∞), Err.Below (cnts (uL (ckP .two) (ds.map toRD)) ws s' ε) c →
    Err.Below (cnts (uLT (ckP .two) ds) ws s' ε) c
  | [], _, _, _, _, _ => trivial
  | d :: ds, some _ :: ws, _ :: s', (_, ε), c, h =>
    ⟨(card_wT d).symm ▸ h.1, below_uLT ds ws s' ε c h.2⟩
  | _ :: ds, some _ :: ws, [], ε, c, h => ⟨by simp, below_uLT ds ws [] ε c h.2⟩
  | _ :: ds, none :: ws, s', ε, c, h => ⟨by simp, below_uLT ds ws s' ε c h.2⟩
  | _ :: ds, [], s', ε, c, h => ⟨by simp, below_uLT ds [] s' ε c h.2⟩

end Held

/-- **The written counts of a reading are below the planner's target.** The target counts the
rounds' proof of work, and `Held` is seven clauses: see the Limits in this file's head. -/
theorem Maps.below_held (st : Setting) {ds : List RDT} {s' : Shape} (M : Maps ds s')
    (rs : List PlanRound) (ε : Err s')
    (H : List.Forall₂ (fun d r => OnBytes.Slice.Held st r d) (ds.map toRD) rs)
    (hc : OnBytes.Flat.Held.CountsL (ds.map toRD) rs M.marks s' ε) :
    Err.Below (M.err ε) ((2 : ℝ≥0∞)⁻¹ ^ st.target) := by
  rw [M.err_eq_cnts ε]
  exact OnBytes.Flat.Held.below_uLT ds _ s' ε _
    (OnBytes.Flat.Held.cnts_below_held st _ rs _ s' ε H hc)

end OnBytes.Flat

#print axioms OnBytes.Flat.Held.below_uLT
#print axioms OnBytes.Flat.Maps.below_held
