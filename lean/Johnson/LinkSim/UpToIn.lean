-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/UpToIn.lean: UpToShift with a constraint on the shift, and how it passes from a
large type of coins to a small type embedded in it. General: nothing here speaks of a protocol.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  UpToShiftIn add R f g   UpToShift add f g (Johnson/LinkSim/UpTo.lean), where in addition
                          every shift s c satisfies R.
  UpToShiftIn.comap       Let K₁ be non-empty, and let lay : K₁ → K₂ be injective and additive,
                          with every element of K₂ that satisfies R in the image of lay. If f and
                          g satisfy UpToShiftIn on K₂, then f ∘ lay and g ∘ lay satisfy UpToShift
                          on K₁.
  UpToShiftIn.forget      UpToShiftIn implies UpToShift.
  comap_needs_fence       a test: without the constraint the step down can fail. On one bit of
                          coins, c and not c agree up to a shift of the bit. Restricted to one
                          point, embedded as false, they do not.

Why. A prover's algorithm may read its coins as values indexed by all natural numbers. That is an
infinite type, with no uniform distribution. The coins actually sampled form a finite type, embedded
in it with zeros at the positions that are not sampled. A shift of the coins found on the large type
serves the finite type only if what it adds is also zero at those positions.

How it fits. Under Johnson/LinkSim/ no file calls its lemmas. The form that is applied is
UpToShiftOn.comap (Johnson/LinkSim/UpToOn.lean), which Johnson/LinkSim/AtText/CoinsDown.lean uses.
comap_needs_fence proves that without the constraint the step down can fail.

Limits. Nothing says when the constraint holds: it is a hypothesis of UpToShiftIn.comap.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.UpTo

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim

/-- As UpToShift, and every shift has the property R. -/
def UpToShiftIn {K V : Type} (add : K → K → K) (R : K → Prop) (f g : K → V) : Prop :=
  ∃ s s' : K → K, ∀ c, R (s c) ∧ f c = g (add c (s c)) ∧ s' (add c (s c)) = s c

/-- UpToShiftIn implies UpToShift. -/
theorem UpToShiftIn.forget {K V : Type} {add : K → K → K} {R : K → Prop} {f g : K → V}
    (h : UpToShiftIn add R f g) : UpToShift add f g := by
  obtain ⟨s, s', hs⟩ := h
  exact ⟨s, s', fun c => (hs c).2⟩

open Classical in
/-- From UpToShiftIn on K₂ to UpToShift on K₁, along an injective additive map lay : K₁ → K₂, K₁
non-empty, whose image contains every element that satisfies R. -/
theorem UpToShiftIn.comap {K₁ K₂ V : Type} [Nonempty K₁] {add₁ : K₁ → K₁ → K₁}
    {add₂ : K₂ → K₂ → K₂} {R : K₂ → Prop} {f g : K₂ → V} (lay : K₁ → K₂)
    (hinj : Function.Injective lay) (hadd : ∀ a b, lay (add₁ a b) = add₂ (lay a) (lay b))
    (hR : ∀ c, R c → ∃ k, lay k = c) (h : UpToShiftIn add₂ R f g) :
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
  obtain ⟨h1, h2, h3⟩ := hs (lay k)
  have e : lay (add₁ k (back (s (lay k)))) = add₂ (lay k) (s (lay k)) := by
    rw [hadd, hlay _ h1]
  refine ⟨?_, ?_⟩
  · show f (lay k) = g (lay (add₁ k (back (s (lay k)))))
    rw [e]
    exact h2
  · show back (s' (lay (add₁ k (back (s (lay k)))))) = back (s (lay k))
    rw [e, h3]

/-- Without the constraint on the shift, the step down to a smaller type of coins can fail. -/
theorem comap_needs_fence :
    UpToShift xor (fun c : Bool => c) (fun c : Bool => !c) ∧
      ¬ UpToShift (fun _ _ : Unit => ()) (fun _ : Unit => false) (fun _ : Unit => !false) := by
  refine ⟨upTo_of_const xor _ _ true fun c => by cases c <;> rfl, ?_⟩
  rintro ⟨_, _, h⟩
  exact Bool.noConfusion (h ()).1

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.UpToShiftIn.forget
#print axioms OnBytes.LinkSim.UpToShiftIn.comap
#print axioms OnBytes.LinkSim.comap_needs_fence
