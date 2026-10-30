-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/UpToOn.lean: UpToShiftIn asked only on a part of the coins, and how it passes to a
small type of coins embedded in that part. General: nothing here speaks of a protocol.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  UpToShiftOn add Dm R f g   there are maps s, s' such that for all coins c with Dm c: R (s c),
                          f c = g (add c (s c)), and s' (add c (s c)) = s c.
  UpToShiftOn.comap       Let lay : K₁ → K₂ be injective and additive, with K₁ non-empty and with
                          image inside Dm, and let every element that satisfies R be in the image
                          of lay. If f and g satisfy UpToShiftOn on K₂, then f ∘ lay and g ∘ lay
                          satisfy UpToShift on K₁ (Johnson/LinkSim/UpTo.lean).
  UpToShiftIn.on          UpToShiftIn at all coins implies UpToShiftOn on every part.

Why, beside Johnson/LinkSim/UpToIn.lean. There the property is asked at all elements of the large
type of coins. The step down to the small type uses it only at the elements in the image of lay.
So a premise that is needed for the property need only be proved at these.

How it fits. Used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).
Johnson/LinkSim/AtText/CoinsDown.lean applies UpToShiftOn.comap.

Limits. Nothing says when the property holds.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.UpToIn

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim

/-- UpToShiftIn asked only at the coins that satisfy Dm; every shift satisfies R. -/
def UpToShiftOn {K V : Type} (add : K → K → K) (Dm R : K → Prop) (f g : K → V) : Prop :=
  ∃ s s' : K → K, ∀ c, Dm c → R (s c) ∧ f c = g (add c (s c)) ∧ s' (add c (s c)) = s c

/-- UpToShiftIn at all coins gives UpToShiftOn on any part Dm. -/
theorem UpToShiftIn.on {K V : Type} {add : K → K → K} {R : K → Prop} {f g : K → V}
    (h : UpToShiftIn add R f g) (Dm : K → Prop) : UpToShiftOn add Dm R f g := by
  obtain ⟨s, s', hs⟩ := h
  exact ⟨s, s', fun c _ => hs c⟩

open Classical in
/-- From UpToShiftOn on K₂ to UpToShift on K₁ (non-empty), along an injective additive map lay : K₁
→ K₂ into Dm whose image contains every element that satisfies R. -/
theorem UpToShiftOn.comap {K₁ K₂ V : Type} [Nonempty K₁] {add₁ : K₁ → K₁ → K₁}
    {add₂ : K₂ → K₂ → K₂} {Dm R : K₂ → Prop} {f g : K₂ → V} (lay : K₁ → K₂)
    (hinj : Function.Injective lay) (hadd : ∀ a b, lay (add₁ a b) = add₂ (lay a) (lay b))
    (hD : ∀ k, Dm (lay k)) (hR : ∀ c, R c → ∃ k, lay k = c) (h : UpToShiftOn add₂ Dm R f g) :
    UpToShift add₁ (fun k => f (lay k)) (fun k => g (lay k)) := by
  obtain ⟨s, s', hs⟩ := h
  let back : K₂ → K₁ := fun c => if hc : ∃ k, lay k = c then hc.choose else Classical.arbitrary K₁
  have hback : ∀ k, back (lay k) = k := fun k => by
    have hc : ∃ k', lay k' = lay k := ⟨k, rfl⟩
    show (if hc : ∃ k', lay k' = lay k then hc.choose else _) = k
    rw [dif_pos hc]
    exact hinj hc.choose_spec
  have hlay : ∀ c, R c → lay (back c) = c := fun c hc => by
    obtain ⟨k, rfl⟩ := hR c hc
    rw [hback]
  refine ⟨fun k => back (s (lay k)), fun k => back (s' (lay k)), fun k => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hs (lay k) (hD k)
  have e : lay (add₁ k (back (s (lay k)))) = add₂ (lay k) (s (lay k)) := by
    rw [hadd, hlay _ h1]
  refine ⟨?_, ?_⟩
  · show f (lay k) = g (lay (add₁ k (back (s (lay k)))))
    rw [e]
    exact h2
  · show back (s' (lay (add₁ k (back (s (lay k)))))) = back (s (lay k))
    rw [e, h3]

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.UpToShiftIn.on
#print axioms OnBytes.LinkSim.UpToShiftOn.comap
