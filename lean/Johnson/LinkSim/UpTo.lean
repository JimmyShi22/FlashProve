-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/UpTo.lean: two functions of coins that agree up to a shift of the coins that can
be undone. A definition, its consequence for distributions, and three tests. General lemmas on
probability: nothing here speaks of a protocol.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  UpToShift add f g   there are maps s, s' on coins such that for all coins c
                          f c = g (add c (s c))   and   s' (add c (s c)) = s c.
The shift s c that is added may depend on the coin c. The second equation says that it can be
recovered from the shifted coin.
  UpToShift.law_eq      if add c d can be cancelled in c (add a d = add b d implies a = b), and
                        the coins form a finite non-empty type, then UpToShift add f g implies that
                        f and g have the same distribution under uniform coins.
  UpToShift.injective   under the same cancellation, c ↦ add c (s c) is injective.
  upTo_of_const         a fixed shift d is the case in which s does not depend on the coin.
  Tests, with one bit of coins and add := xor:
    bare_not_upTo       the constant function true against the constant function false: not up to
                        a shift.
    masked_upTo         b xor coin against coin: up to a shift.
    needs_undo          without the second equation the property would say only that g takes every
                        value of f. For any f whose values g takes, there is a map s with
                        f c = g (add c (s c)).

How it fits. Used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).
Johnson/LinkSim/AtText/Exact.lean uses UpToShift.injective to build the coin bijection that ShiftTo
asks for. UpToShift.law_eq says what the property gives for distributions; under Johnson/LinkSim/ no
file calls it.

Limits. Nothing says when two functions agree in this way: that is a hypothesis of law_eq.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.Shift

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim
open Prob

/-- f c = g (add c (s c)) for all coins c, where the shift s c can be recovered from the shifted
coin by a map s'. -/
def UpToShift {K V : Type} (add : K → K → K) (f g : K → V) : Prop :=
  ∃ s s' : K → K, ∀ c, f c = g (add c (s c)) ∧ s' (add c (s c)) = s c

/-- The shift of the coins c ↦ add c (s c) is injective. -/
theorem UpToShift.injective {K V : Type} {add : K → K → K} {f g : K → V} {s s' : K → K}
    (hc : ∀ a b d, add a d = add b d → a = b)
    (h : ∀ c, f c = g (add c (s c)) ∧ s' (add c (s c)) = s c) :
    Function.Injective fun c => add c (s c) := by
  intro a b hab
  have e : s a = s b := by
    rw [← (h a).2, ← (h b).2]
    exact congrArg s' hab
  refine hc a b (s a) ?_
  have hab' : add a (s a) = add b (s b) := hab
  rw [hab', e]

/-- If add cancels on the right and UpToShift add f g holds, f and g have the same distribution
under uniform coins. -/
theorem UpToShift.law_eq {K V : Type} [Fintype K] [Nonempty K] {add : K → K → K} {f g : K → V}
    (hc : ∀ a b d, add a d = add b d → a = b) (h : UpToShift add f g) :
    (unif K).map f = (unif K).map g := by
  obtain ⟨s, s', hs⟩ := h
  exact map_eq_of_bij (fun c => add c (s c))
    (Finite.injective_iff_bijective.1 (UpToShift.injective hc hs)) f g fun c => (hs c).1

/-- A fixed shift d gives UpToShift. -/
theorem upTo_of_const {K V : Type} (add : K → K → K) (f g : K → V) (d : K)
    (h : ∀ c, f c = g (add c d)) : UpToShift add f g :=
  ⟨fun _ => d, fun _ => d, fun c => ⟨h c, rfl⟩⟩

/-! ## Tests -/

/-- A bare bit against another bit: not up to a shift. -/
theorem bare_not_upTo : ¬ UpToShift xor (fun _ : Bool => true) (fun _ : Bool => false) := by
  rintro ⟨s, _, h⟩
  exact Bool.noConfusion (h true).1

/-- A masked bit against the mask: up to a shift. -/
theorem masked_upTo (b : Bool) : UpToShift xor (fun c : Bool => xor b c) (fun c : Bool => c) :=
  upTo_of_const xor _ _ b fun c => Bool.xor_comm b c

/-- Without the second equation, the property would say only that g takes every value of f: for any
f whose values g takes, the first equation alone holds for some s. -/
theorem needs_undo (f g : Bool → Bool) (h : ∀ c, ∃ c', f c = g c') :
    ∃ s : Bool → Bool, ∀ c, f c = g (xor c (s c)) := by
  choose w hw using h
  refine ⟨fun c => xor c (w c), fun c => ?_⟩
  rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
  exact hw c

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.UpToShift.injective
#print axioms OnBytes.LinkSim.UpToShift.law_eq
#print axioms OnBytes.LinkSim.bare_not_upTo
#print axioms OnBytes.LinkSim.masked_upTo
#print axioms OnBytes.LinkSim.needs_undo
