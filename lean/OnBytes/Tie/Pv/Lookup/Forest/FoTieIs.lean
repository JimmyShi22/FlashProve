-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTieIs.lean.
The tie of a sub-proof's lookup: a step of the byte-level verifier's run, read into a commutative
ring, is a step of the flat function.

States, for every reading ρ of the byte-level field:
  stepEvs, stepEvs_flat, stepEvs_closed: the six calls of a step, as three rounds of plain data.
  step_take: on these rounds TwV.takeSc gives eps, the challenge, the last claim of the record
    tiePsc and the end values, all read, and hands back what follows. Premise: three scalars sent.
  tie_walk: the weights of the four hiding coefficients of a step: 1, beta, beta^2, beta^3.
  tieRow_value: the value of a step's claim (Psc.rowForm) is the value of the flat function's row
    (TwV.rowU), in every world in which the four slots of the hiding coefficients hold the mask
    entries and the start form has its public part less the incoming form, if the flat function's
    places of the hiding coefficients lie from the sumcheck's first slot on in the walk's order.
  tieCT_value: the form that joins the planes' roots, in every world.
Limits: what stands under a slot after a run is not said here. No statement here has a run as its
premise: that a step's run leads through the calls stepEvs and leaves the record tiePsc is
tieStep_ok (OnBytes/Tie/Pv/Lookup/Forest/FoTieRun.lean); the two sides are joined in tieStep_is
(OnBytes/Tie/Pv/Lookup/Forest/FoTieInv.lean).

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTieRun
import OnBytes.Tie.Pv.Lookup.Forest.FoForm
import OnBytes.Tie.Pv.Psc.FlatTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The six calls of a step of the tie. -/
def stepEvs (mu eps : E) (sent : Array E) (beta : E) (n : ℕ) (v : Array E) : List Ev :=
  [.sum mu, .ans .pscEpsilon eps, .read 3 sent, .ansNZ .pscY beta, .read n v, .empty .pscValues]

theorem stepEvs_flat (mu eps : E) (sent : Array E) (beta : E) (n : ℕ) (v : Array E) :
    flEv ρ (stepEvs mu eps sent beta n v) =
      flH ρ mu eps [(sent.toList, beta)] (some v.toList) := by
  simp [flEv, flGo, stepEvs, flH, flR]

theorem stepEvs_closed (mu eps : E) (sent : Array E) (beta : E) (n : ℕ) (v : Array E) :
    openAfter ρ [] (stepEvs mu eps sent beta n v) = [] := rfl

/-- The flat function's step on the rounds of a step of the tie. -/
theorem step_take (C : Aff) (target mu eps beta : E) (first : ℕ) (sent : Array E) (n : ℕ)
    (v : Array E) (hs : sent.size = 3) (rest : Rounds K) :
    takeSc (flEv ρ (stepEvs mu eps sent beta n v) ++ rest) (ρ.val target) [0] true =
      (⟨ρ.val eps, [ρ.val beta], ρ.val (tiePsc C target mu eps beta first sent).claim,
        v.toList.map ρ.val⟩, rest) := by
  have h := takeSc_eq ρ [(zeroE, 3 + 1)] mu eps target [(sent.toList, beta)] (some v.toList) rest
    ⟨by simp [hs], trivial⟩
  rw [stepEvs_flat]
  simp only [List.map_cons, List.map_nil, ρ.zero] at h
  exact h

/-- The weights of a step's four hiding coefficients. -/
theorem tie_walk (C : Aff) (target mu eps beta : E) (first : ℕ) (sent : Array E) :
    (tiePsc C target mu eps beta first sent).walk.1.map ρ.val =
        [1, ρ.val beta, ρ.val beta ^ 2, ρ.val beta ^ 3] ∧
      ρ.val (tiePsc C target mu eps beta first sent).walk.2 = 1 := by
  have h := hidingWalk_eq ρ [((zeroE, 3 + 1), beta)]
  refine ⟨h.1.trans ?_, h.2⟩
  simp [walkK, List.range_succ]

theorem evalL_append {P : Type} (μ : P → K) (a b : List (P × K)) :
    evalL μ (a ++ b) = evalL μ a + evalL μ b := by
  unfold evalL
  rw [List.map_append, List.sum_append]

/-- The value of a step's claim is the value of the flat function's row. -/
theorem tieRow_value (W : World K) (mask : ℕ → K) (C : Aff) (target mu eps beta S0 : E)
    (first : ℕ) (sent : Array E) (vals : List K) (inc : List (Pl × K)) (L : Led Pl)
    (hh : evalL (muOf mask) (hide L [3] [ρ.val beta]) =
      sumFrom (fun j x => x * mask j) first (walkK [(3 + 1, ρ.val beta)]))
    (hW : ∀ i < 4, W.slot (first + i) = mask (first + i))
    (hC : C.value ρ W = ρ.val target - evalL (muOf mask) inc) :
    ((tiePsc C target mu eps beta first sent).rowForm S0 {}).value ρ W =
      rowRes (muOf mask) (rowU L [3]
        ⟨ρ.val eps, [ρ.val beta], ρ.val (tiePsc C target mu eps beta first sent).claim, vals⟩
        inc (ρ.val S0)) := by
  obtain ⟨hw1, hw2⟩ := tie_walk ρ C target mu eps beta first sent
  rw [Psc.rowForm_value, Aff.value_empty, hw2]
  have hsum : sumFrom (fun j x => ρ.val x * W.slot j) first
      (tiePsc C target mu eps beta first sent).walk.1 =
      mask first + ρ.val beta * mask (first + 1) + ρ.val beta ^ 2 * mask (first + 2) +
        ρ.val beta ^ 3 * mask (first + 3) := by
    generalize (tiePsc C target mu eps beta first sent).walk.1 = l at hw1
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> simp at hw1
    obtain ⟨h1, h2, h3, h4⟩ := hw1
    have w0 := hW 0 (by norm_num)
    rw [Nat.add_zero] at w0
    simp only [sumFrom, h1, h2, h3, h4, w0, hW 1 (by norm_num), hW 2 (by norm_num),
      hW 3 (by norm_num), Nat.add_assoc]
    ring
  have hhide : evalL (muOf mask) (hide L [3] [ρ.val beta]) =
      mask first + ρ.val beta * mask (first + 1) + ρ.val beta ^ 2 * mask (first + 2) +
        ρ.val beta ^ 3 * mask (first + 3) := by
    rw [hh]
    simp [walkK, sumFrom, List.range_succ, Nat.add_assoc]
    ring
  show sumFrom (fun j x => ρ.val x * W.slot j) first
        (tiePsc C target mu eps beta first sent).walk.1 +
      ρ.val eps * 1 * (ρ.val target - C.value ρ W) + ρ.val eps * 0 -
      (ρ.val (tiePsc C target mu eps beta first sent).claim - ρ.val eps * ρ.val S0) =
    evalL (muOf mask) (hide L [3] [ρ.val beta] ++ scale (ρ.val eps) inc) -
      (ρ.val (tiePsc C target mu eps beta first sent).claim - ρ.val eps * ρ.val S0)
  rw [hsum, hC, evalL_append, evalL_scale, hhide]
  ring

/-- The form that joins the planes' roots, in every world. -/
theorem tieCT_value (W : World K) (sG : Array ℕ) (ej : Array E) :
    (tieCT sG ej).value ρ W =
      ((List.range 32).map fun j => W.slot (sG.getD j 0) * ρ.val (ej.getD j zeroE)).sum := by
  unfold tieCT
  have h : ∀ (l : List ℕ) (f : Aff),
      (l.foldl (fun (f : Aff) j => Aff.addMul f (Aff.slot (sG.getD j 0)) (ej.getD j zeroE)) f).value
          ρ W =
        f.value ρ W + (l.map fun j => W.slot (sG.getD j 0) * ρ.val (ej.getD j zeroE)).sum := by
    intro l
    induction l with
    | nil => intro f; simp
    | cons j l ih =>
      intro f
      rw [List.foldl_cons, ih, Aff.value_addMul, Aff.value_slot, List.map_cons, List.sum_cons]
      ring
  rw [h, Aff.value_ofConst, ρ.zero, zero_add]

end
end Fo
