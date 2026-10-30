-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAdded.lean.
Which claims lie between two states of a sub-proof.

A sub-proof adds its claims up into one equation, claim number c under the c-th power of one drawn
element theta. A claim is a form and a list of runs on long stretches of entries (t2Lin,
OnBytes/Model/Trees.lean); a claim added by SubM.lin has no run.

States:
  Cl, Cl.value: a claim, and its value under a reading, in a world.
  clsValue: the sum over a list of claims of x^i times the claim's value, i counted from a start.
  Added F G l: from F to G the claims of l have been added, in their order: the total has grown by
    their sum under the powers of theta from F's number of claims on; the number of claims has grown
    by their number; theta and the number of slots are kept; there is one coefficient for each slot.
  Added.refl, Added.trans, added_same (a step that turns none of the fields that the total reads),
    added_lin (Fork.lin), added_lins (Fork.lins), added_paid. All but Added.trans ask that F has one
    coefficient for each slot (F.LS.size = F.ns); added_lin and added_lins ask that the step
    returns.
Limit: identities at the one element theta of the state; whether a claim's value hangs on theta is
not seen here. Added speaks of values alone, in every ring, reading and world: it does not tell two
lists of one length apart whose sums are equal there.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Model.TreesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model

/-- A claim: a form, and runs on long stretches of entries. -/
abbrev Cl := Aff × Array Run2

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- The value of a claim. -/
def Cl.value (c : Cl) : K := c.1.value ρ W + (c.2.toList.map (Run2.value ρ W)).sum

/-- The sum of x^i times the value of the claim, i counted from a start. -/
def clsValue (x : K) (s : ℕ) (l : List Cl) : K := sumFrom (fun i c => x ^ i * Cl.value ρ W c) s l

theorem sumFrom_append {α : Type} (g : ℕ → α → K) : ∀ (l₁ l₂ : List α) (s : ℕ),
    sumFrom g s (l₁ ++ l₂) = sumFrom g s l₁ + sumFrom g (s + l₁.length) l₂
  | [], l₂, s => by simp [sumFrom]
  | a :: l₁, l₂, s => by
    show g s a + sumFrom g (s + 1) (l₁ ++ l₂) = g s a + sumFrom g (s + 1) l₁ + _
    rw [sumFrom_append g l₁ l₂ (s + 1), List.length_cons,
      show s + 1 + l₁.length = s + (l₁.length + 1) by omega]
    ring

theorem clsValue_append (x : K) (s : ℕ) (l₁ l₂ : List Cl) :
    clsValue ρ W x s (l₁ ++ l₂) = clsValue ρ W x s l₁ + clsValue ρ W x (s + l₁.length) l₂ :=
  sumFrom_append _ l₁ l₂ s

theorem value_form (f : Aff) : Cl.value ρ W (f, #[]) = f.value ρ W := by
  simp [Cl.value]

theorem clsValue_forms (x : K) : ∀ (l : List Aff) (s : ℕ),
    clsValue ρ W x s (l.map fun f => (f, #[])) = claimsValue ρ W x s l
  | [], _ => rfl
  | f :: l, s => by
    show x ^ s * Cl.value ρ W (f, #[]) + clsValue ρ W x (s + 1) (l.map fun f => (f, #[])) =
      x ^ s * f.value ρ W + claimsValue ρ W x (s + 1) l
    rw [value_form, clsValue_forms x l (s + 1)]

end

/-- From F to G the claims of l have been added, in their order. -/
structure Added (F G : Fork) (l : List Cl) : Prop where
  total : ∀ (K : Type) [CommRing K] (ρ : Reading K) (W : World K),
    G.total ρ W = F.total ρ W + clsValue ρ W (ρ.val F.theta) F.nClaim l
  nClaim : G.nClaim = F.nClaim + l.length
  theta : G.theta = F.theta
  ns : G.ns = F.ns
  sized : G.LS.size = G.ns

theorem Added.refl {F : Fork} (hs : F.LS.size = F.ns) : Added F F [] :=
  ⟨fun K _ ρ W => by simp [clsValue, sumFrom], rfl, rfl, rfl, hs⟩

theorem Added.trans {F G H : Fork} {l₁ l₂ : List Cl} (h1 : Added F G l₁) (h2 : Added G H l₂) :
    Added F H (l₁ ++ l₂) where
  total := fun K _ ρ W => by
    rw [h2.total, h1.total, h1.theta, h1.nClaim, clsValue_append]
    ring
  nClaim := by rw [h2.nClaim, h1.nClaim, List.length_append]; omega
  theta := h2.theta.trans h1.theta
  ns := h2.ns.trans h1.ns
  sized := h2.sized

/-- A step that turns none of the fields that the total and the numbering read. -/
theorem added_same {F G : Fork} (hs : F.LS.size = F.ns) (h1 : G.trees = F.trees) (h2 : G.LS = F.LS)
    (h3 : G.c0 = F.c0) (h4 : G.nClaim = F.nClaim) (h5 : G.theta = F.theta) (h6 : G.ns = F.ns) :
    Added F G [] where
  total := fun K _ ρ W => by
    unfold Fork.total
    rw [h1, h2, h3]
    simp [clsValue, sumFrom]
  nClaim := h4
  theta := h5
  ns := h6
  sized := by rw [h2, h6]; exact hs

theorem added_lin {F G : Fork} {f : Aff} (hs : F.LS.size = F.ns) (h : F.lin f = some G) :
    Added F G [(f, #[])] where
  total := fun K _ ρ W => by
    rw [(Fork.lin_total ρ W F G f hs h).1]
    simp [clsValue, sumFrom, value_form]
  nClaim := (Fork.lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hs h).2.1
  theta := (Fork.lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hs h).2.2.1
  ns := (Fork.lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hs h).2.2.2.1
  sized := (Fork.lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hs h).2.2.2.2.1

theorem added_lins {F G : Fork} {l : List Aff} (hs : F.LS.size = F.ns) (h : F.lins l = some G) :
    Added F G (l.map fun f => (f, #[])) where
  total := fun K _ ρ W => by rw [(Fork.lins_total ρ W l F G hs h).1, clsValue_forms]
  nClaim := by
    rw [(Fork.lins_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ l F G hs h).2.1, List.length_map]
  theta := (Fork.lins_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ l F G hs h).2.2.1
  ns := (Fork.lins_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ l F G hs h).2.2.2.1
  sized := (Fork.lins_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ l F G hs h).2.2.2.2

theorem added_paid {F : Fork} (hs : F.LS.size = F.ns) (i : ℕ) : Added F (F.paid i) [] :=
  added_same hs rfl rfl rfl rfl rfl rfl

end Fo
