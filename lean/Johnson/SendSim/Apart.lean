-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Apart.lean: a value a c computed from uniform coins c is uniform and independent of
a second value b c, if for each δ some bijection of the coins adds δ to a c and keeps b c.
Terms: Johnson/SendSim/Defs.lean, "Terms of the model". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves. One general lemma on finite probability; it mentions no protocol.
  apart_of_shifts   Let C be a finite non-empty type of coins, G a finite additive group, a : C → G
                    and b : C → B. Suppose that for each δ in G there is a bijection T δ of C with
                    a (T δ c) = a c + δ and b (T δ c) = b c for all c. Then (a c, b c) over uniform
                    c has the distribution of (g, b c) over uniform (g, c) in G × C.

Limits. The maps T δ are a hypothesis: nothing says when they exist.

How it fits. It rests on map_eq_of_bij (Johnson/LinkSim/Shift.lean). It gives sendFresh
(Johnson/SendSim/CoreProofs.lean).

Notes. The library's map_pair (Prob/LensLaw.lean) concludes the analogue for a getter tst and a
setter set that obey three equations, one of them that setting twice is setting the last value:
tst c is uniform and independent of set z₀ c. Here the maps T δ need not compose, so each may be
chosen on its own.
-/
import Johnson.LinkSim.Shift

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim
open Prob OnBytes.LinkSim

/-- If for each δ in G a bijection T δ of the coins adds δ to a and leaves b unchanged, then over
uniform c the pair (a c, b c) has the distribution of (g, b c) over uniform (g, c) in G × C: a c is
uniform and independent of b c. -/
theorem apart_of_shifts {C G B : Type} [Fintype C] [Nonempty C] [AddGroup G] [Fintype G]
    (a : C → G) (b : C → B) (T : G → C → C) (hT : ∀ δ, Function.Bijective (T δ))
    (ha : ∀ δ c, a (T δ c) = a c + δ) (hb : ∀ δ c, b (T δ c) = b c) :
    (unif C).map (fun c => (a c, b c)) = (unif (G × C)).map fun x => (x.1, b x.2) := by
  classical
  -- φ maps (g, c) to (a c, c') with c' = T (-a c + g) c, so that a c' = g and b c' = b c
  let φ : G × C → G × C := fun x => (a x.2, T (-a x.2 + x.1) x.2)
  have hinj : Function.Injective φ := by
    rintro ⟨g, c⟩ ⟨g', c'⟩ h
    have h1 : a c = a c' := congrArg Prod.fst h
    have h2 : T (-a c + g) c = T (-a c' + g') c' := congrArg Prod.snd h
    have h3 : g = g' := by
      have := congrArg a h2
      rw [ha, ha, add_neg_cancel_left, add_neg_cancel_left] at this
      exact this
    subst h3
    rw [← h1] at h2
    exact Prod.ext rfl ((hT _).1 h2)
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, rfl⟩
  have e1 : (unif (G × C)).map (fun x => (x.1, b x.2)) =
      (unif (G × C)).map fun x => (a x.2, b x.2) :=
    map_eq_of_bij φ hbij _ _ fun x => by
      show (x.1, b x.2) = (a (T (-a x.2 + x.1) x.2), b (T (-a x.2 + x.1) x.2))
      rw [ha, hb, add_neg_cancel_left]
  rw [e1]
  -- the right-hand function does not read g, so g can be dropped
  have e2 : (unif (G × C)).map Prod.snd = unif C := map_snd_unif
  rw [← e2, PMF.map_comp]
  rfl

end OnBytes.SendSim

#print axioms OnBytes.SendSim.apart_of_shifts
