-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/AtDotStart.lean: two of `AtDot`'s four premises are given by the last chain's
own start. A theorem; no definition.
THIS IS THE FORM FOR THE LAST CHAIN (the start takes W's, the own
group's and the mask's numbers by name).




Main name.
  `atDot_of_start`: at the record that the start returns `AtDot` holds, given its other two: Omega
    has the plan's shape in the shared chain's last statement; the pending row's weights are
    well-formed.

Limits. The two premises are stated by no law of these files. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.AtDot
import Johnson.Desc.Third.Law.Mask

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Third.Law

/-- **At the record that the start returns**, AtDot holds, given its other two. -/
theorem atDot_of_start (p : P₁₄) (st₁ : Statement) (book₁ : TreeBook) (roots₁ : Nat)
    (w₁ own₁ : Nat) (mask₁ : Option Nat)
    (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (hs : start₃E p.codes p.S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (homega : ∀ y, o.st.oracles[o.omega]? = some y → y.shape = p.S.omega)
    (hweights : ∀ r, pile₁ = [r] → ∀ g ∈ r.g, g.ok = true) : AtDot p s₀ := by
  have hl := start₃E_lin _ _ _ _ _ _ _ _ _ _ _ hs
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hs
  obtain ⟨hn, _, _, _, _, r, hp, eg⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  obtain ⟨c1, _, e0⟩ := start₃_inv _ _ _ _ hst
  obtain ⟨x, _, hx, _, x1, _⟩ := numbersOk_inv _ _ hn
  subst e0
  refine ⟨?_, ⟨x, hx, x1⟩, ?_, ?_⟩
  · show linOk f.st.codes p.S = true
    rw [c1]
    exact hl
  · intro b y hb hy
    have eb : ({ g := f.g, shared := o } : Border) = b := Option.some.inj hb
    subst eb
    exact homega y hy
  · intro b hb g hg
    have eb : ({ g := f.g, shared := o } : Border) = b := Option.some.inj hb
    subst eb
    have hg' : g ∈ f.g := hg
    rw [eg] at hg'
    exact hweights r hp g hg'

end VerifiableInference.Desc.Third.Law

#print axioms VerifiableInference.Desc.Third.Law.atDot_of_start
