-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Kit.lean: lemmas on distributions of functions of uniform
coins. No protocol, no type of Honest/Frame.lean and no part occurs here: the parameters are finite,
non-empty types and functions.

The form "as drawn afresh". Several lemmas speak of an equation
  (unif K).map (fun k => (X k, W k)) = (unif (A × K)).map fun z => (ι z.1, W z.2):
over uniform k the pair (X, W) has the distribution in which the first component is ι of a uniform
a, drawn independently of k. (ι is there so that X may be an option and ι the constructor `some`.)

  1  `map_unif_prod_snd`, `lens_resample`   two uniform coins, the second one sampled first; a
     uniform element with what a lens shows of it drawn anew (Prob/LensLaw.lean)
  2  `afresh_lens`   what a lens shows is as drawn afresh beside whatever does not read it
  3  `afresh_step`   the same for a function α of what the lens shows, beside a W that reads it: if,
     at each fixed value of the rest, (α, v, η) has the distribution in which α is drawn afresh, and
     W depends on what the lens shows through v and η alone
  4  `afresh_map`, `afresh_pair`, `afresh_equiv`   such equations carried along a function; two of
     them as one; the fresh component renamed by a bijection
  5  `kernel_step`   from "as drawn afresh" and a distribution at each fixed value to the joint
     distribution

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Prob.LensLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Kit
open Prob

/-! ## 1 Two coins; a lens -/

section
variable {α β γ : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

/-- Two independent uniform coins: sample the second, then the first. -/
theorem map_unif_prod_snd (f : α × β → γ) :
    (unif (α × β)).map f = (unif β).bind fun b => (unif α).map fun a => f (a, b) := by
  have h : (unif (β × α)).map (Equiv.prodComm β α) = unif (α × β) :=
    map_unif_equiv (Equiv.prodComm β α)
  calc (unif (α × β)).map f = ((unif (β × α)).map (Equiv.prodComm β α)).map f := by rw [h]
    _ = (unif (β × α)).map (f ∘ Equiv.prodComm β α) := PMF.map_comp _ _ _
    _ = (unif β).bind fun b => (unif α).map fun a => (f ∘ Equiv.prodComm β α) (b, a) :=
        map_unif_prod _
    _ = (unif β).bind fun b => (unif α).map fun a => f (a, b) := rfl

end

section
variable {K C A A' B B' V Hh Ω Ω' Φ γ : Type} [Fintype K] [Nonempty K]

section lens
variable [Fintype C] [Nonempty C] {get : K → C} {put : C → K → K}

/-- A uniform element, with what the lens shows of it drawn anew, is uniform: stated for the
distribution of F. -/
theorem lens_resample (hL : Lens.OK get put) (F : K → γ) :
    (unif K).map F = (unif K).bind fun k => (unif C).map fun c => F (put c k) := by
  have h : (unif (C × K)).map (fun p => put p.1 p.2) = unif K := Lens.map_set hL
  calc (unif K).map F = ((unif (C × K)).map fun p => put p.1 p.2).map F := by rw [h]
    _ = (unif (C × K)).map (F ∘ fun p => put p.1 p.2) := PMF.map_comp _ _ _
    _ = (unif K).bind fun k => (unif C).map fun c => (F ∘ fun p => put p.1 p.2) (c, k) :=
        map_unif_prod_snd _
    _ = (unif K).bind fun k => (unif C).map fun c => F (put c k) := rfl

/-! ## 2 What a lens shows, beside what does not read it -/

theorem afresh_lens (hL : Lens.OK get put) (W : K → Ω) (hW : ∀ c k, W (put c k) = W k) :
    (unif K).map (fun k => (get k, W k)) = (unif (C × K)).map fun z => (z.1, W z.2) := by
  rw [lens_resample hL fun k => (get k, W k), map_unif_prod_snd]
  refine congrArg (fun f => (unif K).bind f) (funext fun k => ?_)
  refine congrArg (fun f => (unif C).map f) (funext fun c => ?_)
  show (get (put c k), W (put c k)) = (c, W k)
  rw [hL.tst_set, hW]

/-! ## 3 A function of what the lens shows, beside what reads it -/

/-- **One step.** `vv`: a function of the whole element (what the owner of the lens's part shows).
`η`: a second function of what the lens shows. `hfresh`: at each k, over what the lens shows, (α,
vv, η) has the distribution in which α is drawn afresh. `hfac`: W depends on what the lens shows
through vv and η alone. -/
theorem afresh_step [Fintype A] [Nonempty A] (hL : Lens.OK get put) (α : C → A') (ι : A → A')
    (η : C → Hh) (vv : K → V) (W : K → Ω)
    (hfresh : ∀ k, (unif C).map (fun c => (α c, vv (put c k), η c)) =
      (unif (A × C)).map fun z => (ι z.1, vv (put z.2 k), η z.2))
    (hfac : ∀ k c c', vv (put c k) = vv (put c' k) → η c = η c' → W (put c k) = W (put c' k)) :
    (unif K).map (fun k => (α (get k), W k)) = (unif (A × K)).map fun z => (ι z.1, W z.2) := by
  have s1 : ∀ k, (unif C).map (fun c => (α c, W (put c k))) =
      (unif (A × C)).map fun z => (ι z.1, W (put z.2 k)) := fun k =>
    map_eq_of_factor (f := fun c => (α c, W (put c k)))
      (f' := fun z : A × C => (ι z.1, W (put z.2 k)))
      (g := fun c => (α c, vv (put c k), η c))
      (g' := fun z : A × C => (ι z.1, vv (put z.2 k), η z.2)) (unif C) (unif (A × C))
      (fun c z h => by
        have h1 : α c = ι z.1 := congrArg Prod.fst h
        have h2 : vv (put c k) = vv (put z.2 k) := congrArg (fun t => t.2.1) h
        have h3 : η c = η z.2 := congrArg (fun t => t.2.2) h
        show (α c, W (put c k)) = (ι z.1, W (put z.2 k))
        rw [h1, hfac k c z.2 h2 h3]) (hfresh k)
  have l1 : (unif K).map (fun k => (α (get k), W k)) =
      (unif K).bind fun k => (unif C).map fun c => (α c, W (put c k)) := by
    rw [lens_resample hL fun k => (α (get k), W k)]
    refine congrArg (fun f => (unif K).bind f) (funext fun k => ?_)
    refine congrArg (fun f => (unif C).map f) (funext fun c => ?_)
    show (α (get (put c k)), W (put c k)) = (α c, W (put c k))
    rw [hL.tst_set]
  have r1 : (unif (A × K)).map (fun z => (ι z.1, W z.2)) =
      (unif K).bind fun k => (unif (A × C)).map fun z => (ι z.1, W (put z.2 k)) := by
    have e : ∀ a : A, ((unif K).map fun k => (ι a, W k)) =
        (unif K).bind fun k => (unif C).map fun c => (ι a, W (put c k)) := fun a =>
      lens_resample hL fun k => (ι a, W k)
    calc (unif (A × K)).map (fun z => (ι z.1, W z.2))
        = (unif A).bind fun a => (unif K).map fun k => (ι a, W k) := map_unif_prod _
      _ = (unif A).bind fun a => (unif K).bind fun k => (unif C).map fun c => (ι a, W (put c k)) :=
          congrArg (fun f => (unif A).bind f) (funext e)
      _ = (unif K).bind fun k => (unif A).bind fun a => (unif C).map fun c => (ι a, W (put c k)) :=
          PMF.bind_comm _ _ _
      _ = (unif K).bind fun k => (unif (A × C)).map fun z => (ι z.1, W (put z.2 k)) :=
          congrArg (fun f => (unif K).bind f) (funext fun k =>
            (map_unif_prod fun z : A × C => (ι z.1, W (put z.2 k))).symm)
  rw [l1, r1]
  exact congrArg (fun f => (unif K).bind f) (funext s1)

end lens

/-! ## 4 Such equations, carried on -/

/-- Along a function of both components. -/
theorem afresh_map [Fintype A] [Nonempty A] {X : K → A'} {ι : A → A'} {W : K → Ω}
    (h : (unif K).map (fun k => (X k, W k)) = (unif (A × K)).map fun z => (ι z.1, W z.2))
    (F : A' × Ω → γ) :
    (unif K).map (fun k => F (X k, W k)) = (unif (A × K)).map fun z => F (ι z.1, W z.2) := by
  have e1 : (unif K).map (fun k => F (X k, W k)) = ((unif K).map fun k => (X k, W k)).map F :=
    (PMF.map_comp (fun k => (X k, W k)) (unif K) F).symm
  have e2 : (unif (A × K)).map (fun z => F (ι z.1, W z.2)) =
      ((unif (A × K)).map fun z => (ι z.1, W z.2)).map F :=
    (PMF.map_comp (fun z : A × K => (ι z.1, W z.2)) (unif (A × K)) F).symm
  rw [e1, e2, h]

/-- Two as one: X is as drawn afresh beside (Y, W), and Y beside W: then (X, Y) beside W. -/
theorem afresh_pair [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] {X : K → A'} {Y : K → B'}
    {W : K → Ω} {ι : A → A'} {κ : B → B'}
    (h1 : (unif K).map (fun k => (X k, (Y k, W k))) =
      (unif (A × K)).map fun z => (ι z.1, (Y z.2, W z.2)))
    (h2 : (unif K).map (fun k => (Y k, W k)) = (unif (B × K)).map fun z => (κ z.1, W z.2)) :
    (unif K).map (fun k => ((X k, Y k), W k)) =
      (unif ((A × B) × K)).map fun z => ((ι z.1.1, κ z.1.2), W z.2) := by
  have a1 : (unif K).map (fun k => ((X k, Y k), W k)) =
      (unif (A × K)).map fun z => ((ι z.1, Y z.2), W z.2) :=
    afresh_map (W := fun k => (Y k, W k)) h1 fun t => ((t.1, t.2.1), t.2.2)
  have a2 : ∀ a : A, ((unif K).map fun k => ((ι a, Y k), W k)) =
      (unif (B × K)).map fun z => ((ι a, κ z.1), W z.2) := fun a =>
    afresh_map h2 fun t => ((ι a, t.1), t.2)
  have a3 : (unif ((A × B) × K)).map (fun z => ((ι z.1.1, κ z.1.2), W z.2)) =
      (unif (A × (B × K))).map fun z => ((ι z.1, κ z.2.1), W z.2.2) := by
    have h : (unif ((A × B) × K)).map (Equiv.prodAssoc A B K) = unif (A × (B × K)) :=
      map_unif_equiv (Equiv.prodAssoc A B K)
    rw [← h, PMF.map_comp]
    rfl
  rw [a1, a3, map_unif_prod, map_unif_prod]
  exact congrArg (fun f => (unif A).bind f) (funext a2)

/-- The fresh component renamed by a bijection. -/
theorem afresh_equiv [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] (e : B ≃ A) {X : K → A'}
    {ι : A → A'} {W : K → Ω}
    (h : (unif K).map (fun k => (X k, W k)) = (unif (A × K)).map fun z => (ι z.1, W z.2)) :
    (unif K).map (fun k => (X k, W k)) = (unif (B × K)).map fun z => (ι (e z.1), W z.2) := by
  have h' : (unif (B × K)).map (Equiv.prodCongr e (Equiv.refl K)) = unif (A × K) :=
    map_unif_equiv (Equiv.prodCongr e (Equiv.refl K))
  rw [h, ← h', PMF.map_comp]
  rfl

/-! ## 5 From "as drawn afresh" to the joint distribution -/

/-- **The kernel's step.** `a`: what is as drawn afresh. `b`: what it is beside. `g`: what is shown,
from the two. `h`: what of b a kernel T reads. `hker`: at each b that a k reaches, over a fresh a,
what is shown has the distribution T (h b). -/
theorem kernel_step [Fintype A] [Nonempty A] (a : K → A') (ι : A → A') (b : K → B)
    (hind : (unif K).map (fun k => (a k, b k)) = (unif (A × K)).map fun z => (ι z.1, b z.2))
    (g : A' → B → V) (h : B → Φ) (T : Φ → PMF V)
    (hker : ∀ k, (unif A).map (fun x => g (ι x) (b k)) = T (h (b k))) :
    (unif K).map (fun k => (h (b k), g (a k) (b k))) =
      ((unif K).map fun k => h (b k)).bind fun φ => (T φ).map fun v => (φ, v) := by
  have e1 : (unif K).map (fun k => (h (b k), g (a k) (b k))) =
      (unif (A × K)).map fun z => (h (b z.2), g (ι z.1) (b z.2)) :=
    afresh_map hind fun t => (h t.2, g t.1 t.2)
  have e2 : ∀ k, ((unif A).map fun x => (h (b k), g (ι x) (b k))) =
      (T (h (b k))).map fun v => (h (b k), v) := fun k => by
    rw [← hker k, PMF.map_comp]
    rfl
  rw [e1, map_unif_prod_snd, PMF.bind_map]
  exact congrArg (fun f => (unif K).bind f) (funext e2)

end

end ProofFile.Honest.Kit

#print axioms ProofFile.Honest.Kit.map_unif_prod_snd
#print axioms ProofFile.Honest.Kit.lens_resample
#print axioms ProofFile.Honest.Kit.afresh_lens
#print axioms ProofFile.Honest.Kit.afresh_step
#print axioms ProofFile.Honest.Kit.afresh_map
#print axioms ProofFile.Honest.Kit.afresh_pair
#print axioms ProofFile.Honest.Kit.afresh_equiv
#print axioms ProofFile.Honest.Kit.kernel_step
