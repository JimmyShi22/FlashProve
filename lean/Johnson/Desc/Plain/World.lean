-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/World.lean: the plain law SAID AT ONE WORLD w: the form in which several open
items at a border share what is hidden.

Why. Where a border's statement is "ONE w meets every open item", the law of a kind that treats some
of the items cannot be said with "there is a w" inside it: "(∃ w, Out ∧ Rest) → (∃ w, In ∧ Rest)"
does not follow from "(∃ w, Out) → (∃ w, In)". It is said FOR EVERY w, under one "the prover has
lost":
    `K.KeepsW on on' R R' ε` := `Leads` at Q a b := on' b ∧ ∀ w, R' b w → R a w.
No extractor is named: the world in front is the world behind. It is a case of `Leads`: so every
rule for `Leads` bears it as it stands. `KeepsW.beside`: items that only ride beside. `KeepsW.seq`.
`KeepsW.keeps`: its shadow on the statements alone (`Keeps` at "there is a w"). `KeepsW.move`: where
a block fixes a part of the world (a pin is closed): the world in front is f a b w. Limits: those of
Leads.lean.

Nearest kin in the library: none found, by hand and by a search over all statements by shape.


-/
import Johnson.Desc.Plain.Leads

set_option autoImplicit false

namespace Iop
namespace Reduction
variable {A B C W : Type}

/-- The plain law at one world. -/
def KeepsW (K : Reduction A B) (on : A → Prop) (on' : B → Prop) (R : A → W → Prop)
    (R' : B → W → Prop) (ε : Err K.shape) : Prop :=
  K.Leads on (fun a b => on' b ∧ ∀ w, R' b w → R a w) ε

theorem KeepsW.seq {K₁ : Reduction A B} {K₂ : Reduction B C} {on₁ : A → Prop} {on₂ : B → Prop}
    {on₃ : C → Prop} {R₁ : A → W → Prop} {R₂ : B → W → Prop} {R₃ : C → W → Prop}
    {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape} (h₁ : K₁.KeepsW on₁ on₂ R₁ R₂ ε₁)
    (h₂ : K₂.KeepsW on₂ on₃ R₂ R₃ ε₂) : (K₁.seq K₂).KeepsW on₁ on₃ R₁ R₃ (Err.app ε₁ ε₂) :=
  (Leads.seq h₁ h₂ fun _ _ _ h => h.1).conseq (fun _ h => h)
    fun _ _ _ _ _ ⟨_, hb, hc⟩ => ⟨hc.1, fun w h => hb.2 w (hc.2 w h)⟩

/-- **Items that only ride beside**, at the same world, at the block's own errors. -/
theorem KeepsW.beside {K : Reduction A B} {on : A → Prop} {on' : B → Prop} {R : A → W → Prop}
    {R' : B → W → Prop} {ε : Err K.shape} (h : K.KeepsW on on' R R' ε) (Rc : A → W → Prop)
    (Rc' : B → W → Prop)
    (hc : ∀ a τ b w, on a → K.out a τ = some b → on' b → R' b w → Rc' b w → Rc a w) :
    K.KeepsW on on' (fun a w => R a w ∧ Rc a w) (fun b w => R' b w ∧ Rc' b w) ε :=
  Leads.conseq h (fun _ h => h) fun a τ b ha hb hq =>
    ⟨hq.1, fun w hl => ⟨hq.2 w hl.1, hc a τ b w ha hb hq.1 hl.1 hl.2⟩⟩

/-- Its shadow on the statements alone. -/
theorem KeepsW.keeps {K : Reduction A B} {on : A → Prop} {on' : B → Prop} {R : A → W → Prop}
    {R' : B → W → Prop} {ε : Err K.shape} (h : K.KeepsW on on' R R' ε) :
    K.Keeps on on' (fun a => ∃ w, R a w) (fun b => ∃ w, R' b w) ε :=
  Leads.conseq h (fun _ h => h) fun _ _ _ _ _ hq => ⟨hq.1, fun ⟨w, hw⟩ => ⟨w, hq.2 w hw⟩⟩

/-- Where a block fixes a part of the world: from a law "the world in front is f a b w" to the law
at one world for the relation behind that also says "w is fixed so". -/
theorem KeepsW.move {K : Reduction A B} {on : A → Prop} {on' : B → Prop} {R : A → W → Prop}
    {R' : B → W → Prop} {ε : Err K.shape} (f : A → B → W → W)
    (h : K.Leads on (fun a b => on' b ∧ ∀ w, R' b w → R a (f a b w)) ε) (Fix : B → W → Prop)
    (hf : ∀ a τ b w, on a → K.out a τ = some b → Fix b w → f a b w = w) :
    K.KeepsW on on' R (fun b w => R' b w ∧ Fix b w) ε :=
  Leads.conseq h (fun _ h => h) fun a τ b ha hb hq =>
    ⟨hq.1, fun w hw => by
      have := hq.2 w hw.1
      rwa [hf a τ b w ha hb hw.2] at this⟩

end Reduction
end Iop

#print axioms Iop.Reduction.KeepsW.seq
#print axioms Iop.Reduction.KeepsW.beside
#print axioms Iop.Reduction.KeepsW.keeps
#print axioms Iop.Reduction.KeepsW.move
