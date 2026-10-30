-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/GateOfCount.lean: FROM A COUNT OF FIELD ELEMENTS TO THE MEASURE OVER ONE ROUND's
MESSAGES, AT TYPED CHALLENGES AND AT STRINGS OF HASH BLOCKS: WITHOUT A TEST, A BLOCK OR A STATE.
Lemmas; none of the library's goals. Nothing on completeness, soundness or hiding. An assembly:
`prRho_elem_le` (Johnson/Desc/K8/Honest/CountToRho.lean) at the two kits.

d: a round's data whose list of draws is one field element and nothing else (`OneElem`,
Johnson/Desc/K8/Honest/ChiTyped.lean). Q: an event on the round's drawn value. Q': a predicate on
field elements that holds of x wherever Q holds of a drawn value whose elements are [x]. m: at most
m field elements meet Q'.
  **`gate_of_count`**   the measure (Iop.prRho, uniform on that one round's messages) of the
      messages at which Q holds of what is shown is at most m / p ^ 3, at Run.ck .two
  **`gate_of_count_blocks`**   the entry's positions of at most 64 bits: at most kapSl 128 ^ 3 * m /
      p ^ 3, at Run.ckP .two
By: `elOf_one`, `shows_chi` (ChiTyped.lean) · `card_one_elem` (Johnson/P1K8R/UnitsTest.lean) ·
`blocks_el`, `blocks_bound` (Johnson/P1K8R/UnitsBlocks.lean).
Limits. The uniform law on one round's messages is named, not derived. One round. No number is
evaluated.

-/
import Johnson.P1K8R.UnitsBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Slice
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Iop
open scoped ENNReal

/-- **At typed challenges.** -/
theorem gate_of_count (d : RDT) (h1 : OneElem d.entry d.kind) (Q : Fmt.Drawn → Prop)
    (Q' : Cb.Gl.E → Prop) (hQ : ∀ dr x, Q dr → dr.elems = [Slice.ofE x] → Q' x) (m : ℕ)
    (hm : Prob.cnt Q' ≤ m) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
      ∃ dr, drawnT (_root_.Run.ck .two) [d] ρ = [dr] ∧ Q dr} ≤
      (m : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  have k := prRho_elem_le (_root_.Run.ck .two) d (elOf d.entry d.kind) 1 (elOf_one _ _ h1)
    (fun a => by
      show (_root_.Run.drawnOf .two d.entry d.kind a).elems = _
      rw [shows_chi _ _ h1]
      rfl) Q Q' hQ m hm
  rw [Nat.mul_one] at k
  rw [← card_one_elem d.entry d.kind h1]
  exact k

/-- **At strings of hash blocks.** -/
theorem gate_of_count_blocks (d : RDT) (h1 : OneElem d.entry d.kind) (hlog : d.entry.logN ≤ 64)
    (Q : Fmt.Drawn → Prop) (Q' : Cb.Gl.E → Prop)
    (hQ : ∀ dr x, Q dr → dr.elems = [Slice.ofE x] → Q' x) (m : ℕ) (hm : Prob.cnt Q' ≤ m) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
      ∃ dr, drawnT (_root_.Run.ckP .two) [d] ρ = [dr] ∧ Q dr} ≤
      kapSl 128 ^ 3 * (m : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  have k := prRho_elem_le (_root_.Run.ckP .two) d
    (fun u => elOf d.entry d.kind ((_root_.Run.bsRound .two d.entry d.kind).φ u))
    (_root_.Run.bsRound .two d.entry d.kind).w (blocks_el _ _ h1 hlog)
    (fun a => by
      show (_root_.Run.drawnOf .two d.entry d.kind
        ((_root_.Run.bsRound .two d.entry d.kind).φ a)).elems = _
      rw [shows_chi _ _ h1]
      rfl) Q Q' hQ m hm
  exact k.trans (blocks_bound _ _ h1 hlog _)

end P1K8

#print axioms P1K8.gate_of_count
#print axioms P1K8.gate_of_count_blocks
