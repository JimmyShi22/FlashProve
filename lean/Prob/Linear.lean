-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/Linear.lean: peeling of uniform randomness; adaptive queries to random tables.

# What this file is for

This file proves two elementary lemmas, peeling and adaptive queries (the second in the form of
`Reader.law_eq` below), and two simpler facts on uniform random variables, on Mathlib's type `PMF`
of probability mass functions, for arbitrary finite index sets, alphabets and groups (commutative
groups in Part 4). No error-correcting code, protocol or hash function occurs in it.

 * Part 1: maps that push the uniform distribution to the uniform distribution; independent
   coordinates, independent parts, one part after the other.
 * Part 2, uniform in, uniform out: a surjective additive map pushes uniform to uniform, also after
   a shift, and only a surjective one does (`map_unif_add_addMonoidHom_iff`).
 * Part 3, one-time pad: a value plus an independent uniform pad is uniform and independent of the
   value.
 * Part 4, peeling: if value k is a shift that reads only earlier randomness (for a well-founded
   "earlier"), plus a surjective additive image of its own randomness, then all the values together
   are uniform (`peel`).
 * Parts 5 and 6, adaptive queries: a table holds one symbol at each of its places. Two random
   tables with the same law on every good set of places give the same law of outputs to an
   algorithm whose set of places read is always good, even if it chooses each place by what it has
   seen and flips its own coins (`Reader.law_eq`; which sets are good is a parameter).
 * Part 7: the uniform table is uniform on every set of places (`map_unif_res`); several rows side
   by side (`map_unif_rows`); a table next to a second one (for instance symbols and salts;
   `map_unif_pair`).

# How a probability is written

`unif α` is the uniform distribution on a finite non-empty type (Prob/Basic.lean; it unfolds to
Mathlib's `PMF.uniformOfFintype α`).
"X has the law q" is an equation between two PMFs: (unif Ω).map X = q. "Draw h from p, then ..." is
`PMF.bind`.
All statements are exact: there is no error term in this file. The conversion between such equations
and numbers of elements is `map_unif_eq_unif_iff` of Prob/Count.lean.

# Credit

The public Lean library VCV-io (https://github.com/Verified-zkEVM/VCV-io) also represents an
algorithm with oracle access as a tree of queries.
"Reader" of Part 6 is a tree of that kind, for an algorithm that reads the places of a table and
flips coins of its own.
VCV-io is not a dependency: no file of this library imports it.
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Module.LinearMap.Defs
import Prob.Count
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Prob

open scoped ENNReal

/-! ## Part 1. Uniform distributions and maps -/

section Basics

variable {α β : Type}

/-- An injective map sends the mass of a point to the image of the point. -/
theorem map_apply_of_injective {f : α → β} (hf : Function.Injective f) (p : PMF α) (a : α) :
    p.map f (f a) = p a := by
  rw [PMF.map_apply, tsum_eq_single a]
  · rw [if_pos rfl]
  · intro a' ha'
    rw [if_neg fun h => ha' (hf h.symm)]

/-- One map, written as two maps one after the other. -/
theorem map_eq_map_map {γ : Type} (p : PMF α) {f : α → β} {g : β → γ}
    {h : α → γ} (e : ∀ a, h a = g (f a)) : p.map h = (p.map f).map g := by
  rw [PMF.map_comp]
  exact congrArg (fun u => p.map u) (funext e)

/-- A distribution on a finite type that gives all points the same mass is the uniform one. -/
theorem eq_unif_of_const [Fintype β] [Nonempty β] (q : PMF β) (h : ∀ b b', q b = q b') :
    q = unif β := by
  refine PMF.ext fun b => ?_
  have h1 : ∑' b', q b' = 1 := q.tsum_coe
  rw [tsum_fintype, Finset.sum_congr rfl fun b' _ => h b' b, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at h1
  rw [PMF.uniformOfFintype_apply]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)

variable [Fintype α] [Nonempty α]

/-- A bijection pushes uniform to uniform. -/
theorem map_unif_of_bijective [Fintype β] [Nonempty β] {f : α → β} (hf : Function.Bijective f) :
    (unif α).map f = unif β :=
  map_unif_equiv (Equiv.ofBijective f hf)

/-- A map that pushes uniform to uniform is surjective. -/
theorem surjective_of_map_unif [Fintype β] [Nonempty β] {f : α → β} (h : (unif α).map f = unif β) :
    Function.Surjective f := by
  intro b
  have hb : b ∈ ((unif α).map f).support := by
    rw [h]
    exact PMF.mem_support_uniformOfFintype b
  obtain ⟨a, -, ha⟩ := (PMF.mem_support_map_iff _ _ _).1 hb
  exact ⟨a, ha⟩

/-- Independent coordinates. If g i pushes uniform to uniform for every i, then so does the map that
applies g i to coordinate i of a family. -/
theorem map_unif_pi {ι : Type} [Fintype ι] [DecidableEq ι] {Ω Y : ι → Type} [∀ i, Fintype (Ω i)]
    [∀ i, Nonempty (Ω i)] [∀ i, Fintype (Y i)] [∀ i, Nonempty (Y i)] (g : ∀ i, Ω i → Y i)
    (hg : ∀ i, (unif (Ω i)).map (g i) = unif (Y i)) :
    (unif (∀ i, Ω i)).map (fun ω i => g i (ω i)) = unif (∀ i, Y i) := by
  rw [map_unif_eq_unif_iff]
  intro y
  have h1 : cnt (fun ω : ∀ i, Ω i => (fun i => g i (ω i)) = y) =
      ∏ i, cnt (fun x => g i x = y i) := by
    rw [← cnt_forall_pi]
    exact cnt_congr fun ω => funext_iff
  rw [h1, Fintype.card_pi, Fintype.card_pi, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (map_unif_eq_unif_iff (g i)).1 (hg i) (y i)

/-- Independent parts. If g₁ and g₂ push uniform to uniform, then so does the map that applies them
to the two parts of a pair. -/
theorem map_unif_prodMap {Ω₁ Ω₂ Y₁ Y₂ : Type} [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
    [Fintype Y₁] [Nonempty Y₁] [Fintype Y₂] [Nonempty Y₂] (g₁ : Ω₁ → Y₁) (g₂ : Ω₂ → Y₂)
    (h₁ : (unif Ω₁).map g₁ = unif Y₁) (h₂ : (unif Ω₂).map g₂ = unif Y₂) :
    (unif (Ω₁ × Ω₂)).map (fun ω => (g₁ ω.1, g₂ ω.2)) = unif (Y₁ × Y₂) := by
  rw [map_unif_eq_unif_iff]
  rintro ⟨y₁, y₂⟩
  have h : cnt (fun ω : Ω₁ × Ω₂ => (g₁ ω.1, g₂ ω.2) = (y₁, y₂)) =
      cnt (fun x => g₁ x = y₁) * cnt (fun x => g₂ x = y₂) := by
    rw [← cnt_and_prod]
    exact cnt_congr fun ω => Prod.mk_inj
  rw [h, Fintype.card_prod, Fintype.card_prod, ← (map_unif_eq_unif_iff g₁).1 h₁ y₁,
    ← (map_unif_eq_unif_iff g₂).1 h₂ y₂]
  ring

/-- One part after the other. If g₁ pushes uniform to uniform, and g₂ a does so for every value a of
the first part, then the pair (g₁ of the first part, g₂ of both parts) is uniform. -/
theorem map_unif_chain {Ω₁ Ω₂ Y₁ Y₂ : Type} [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
    [Fintype Y₁] [Nonempty Y₁] [Fintype Y₂] [Nonempty Y₂] (g₁ : Ω₁ → Y₁) (g₂ : Ω₁ → Ω₂ → Y₂)
    (h₁ : (unif Ω₁).map g₁ = unif Y₁) (h₂ : ∀ a, (unif Ω₂).map (g₂ a) = unif Y₂) :
    (unif (Ω₁ × Ω₂)).map (fun ω => (g₁ ω.1, g₂ ω.1 ω.2)) = unif (Y₁ × Y₂) := by
  rw [unif_prod, unif_prod]
  unfold prod
  rw [PMF.map_bind, ← h₁, PMF.bind_map]
  refine congrArg (unif Ω₁).bind (funext fun a => ?_)
  show ((unif Ω₂).map fun b => (a, b)).map (fun ω : Ω₁ × Ω₂ => (g₁ ω.1, g₂ ω.1 ω.2)) =
    (unif Y₂).map fun b => (g₁ a, b)
  rw [← h₂ a, PMF.map_comp, PMF.map_comp]
  rfl

/-- For every h, hence on average. If T h pushes uniform to uniform for every value h of a
parameter, then it does so for a parameter drawn from any distribution p. -/
theorem bind_map_unif {H Y : Type} [Fintype Y] [Nonempty Y] (p : PMF H) (T : H → α → Y)
    (hT : ∀ h, (unif α).map (T h) = unif Y) : (p.bind fun h => (unif α).map (T h)) = unif Y := by
  simp only [hT]
  exact PMF.bind_const _ _

/-- For every h, hence independent of h. If T h pushes uniform to uniform for every value h of a
parameter, then for a parameter drawn from any distribution p the pair (h, T h ω) has the law of h
next to an independent uniform value. -/
theorem bind_map_unif_joint {H Y : Type} [Fintype Y] [Nonempty Y] (p : PMF H) (T : H → α → Y)
    (hT : ∀ h, (unif α).map (T h) = unif Y) :
    (p.bind fun h => (unif α).map fun ω => (h, T h ω)) = prod p (unif Y) := by
  refine congrArg p.bind (funext fun h => ?_)
  rw [← hT h, PMF.map_comp]
  rfl

end Basics

/-! ## Part 2. Uniform in, uniform out: additive maps -/

section Additive

variable {V W : Type} [AddGroup V] [Fintype V] [AddGroup W] [Fintype W]

/-- Uniform in, uniform out. A surjective additive map between finite groups pushes the uniform
distribution to the uniform distribution: all its fibres are translates of each other. -/
theorem map_unif_addMonoidHom (φ : V →+ W) (hφ : Function.Surjective φ) :
    (unif V).map φ = unif W := by
  refine eq_unif_of_const _ fun w w' => ?_
  obtain ⟨x0, hx0⟩ := hφ (-w + w')
  have hinv : ((unif V).map φ).map (Equiv.addRight (-w + w')) = (unif V).map φ :=
    calc ((unif V).map φ).map (Equiv.addRight (-w + w')) = (unif V).map (Equiv.addRight (-w + w') ∘ φ) :=
          PMF.map_comp _ _ _
      _ = (unif V).map (φ ∘ Equiv.addRight x0) := by
          refine congrArg (fun g => (unif V).map g) (funext fun x => ?_)
          simp only [Function.comp_apply, Equiv.coe_addRight, map_add, hx0]
      _ = ((unif V).map (Equiv.addRight x0)).map φ := (PMF.map_comp _ _ _).symm
      _ = (unif V).map φ := by rw [map_unif_equiv (Equiv.addRight x0)]
  have hw : Equiv.addRight (-w + w') w = w' := by simp
  calc (unif V).map φ w = (((unif V).map φ).map (Equiv.addRight (-w + w'))) (Equiv.addRight (-w + w') w) :=
        (map_apply_of_injective (Equiv.injective _) _ _).symm
    _ = (unif V).map φ w' := by rw [hinv, hw]

/-- Uniform in, uniform out, with a shift. A fixed element plus a surjective additive image of a
uniform element is uniform. -/
theorem map_unif_add_addMonoidHom (φ : V →+ W) (hφ : Function.Surjective φ) (s : W) :
    (unif V).map (fun x => s + φ x) = unif W :=
  calc
    (unif V).map (fun x => s + φ x) = ((unif V).map φ).map (Equiv.addLeft s) :=
      (PMF.map_comp _ _ _).symm
    _ = unif W := by rw [map_unif_addMonoidHom φ hφ, map_unif_equiv (Equiv.addLeft s)]

/-- A shifted additive image of a uniform element is uniform if and only if the additive map is
surjective. -/
theorem map_unif_add_addMonoidHom_iff (φ : V →+ W) (s : W) :
    (unif V).map (fun x => s + φ x) = unif W ↔ Function.Surjective φ := by
  refine ⟨fun h w => ?_, fun h => map_unif_add_addMonoidHom φ h s⟩
  obtain ⟨x, hx⟩ := surjective_of_map_unif h (s + w)
  exact ⟨x, add_left_cancel hx⟩

/-- Uniform in, uniform out, for a surjective linear map and a shift. -/
theorem map_unif_add_linearMap {K V' W' : Type} [Semiring K] [AddCommGroup V'] [Module K V']
    [Fintype V'] [AddCommGroup W'] [Module K W'] [Fintype W'] (φ : V' →ₗ[K] W')
    (hφ : Function.Surjective φ) (s : W') :
    (unif V').map (fun x => s + φ x) = unif W' :=
  map_unif_add_addMonoidHom φ.toAddMonoidHom hφ s

end Additive

/-! ## Part 3. The one-time pad -/

section Pad

variable {G : Type} [AddGroup G] [Fintype G]

/-- One-time pad. A fixed value plus a uniform pad is uniform. -/
theorem one_time_pad (m : G) : (unif G).map (fun r => m + r) = unif G :=
  map_unif_equiv (Equiv.addLeft m)

/-- One-time pad, with the pad on the left. -/
theorem one_time_pad_left (m : G) : (unif G).map (fun r => r + m) = unif G :=
  map_unif_equiv (Equiv.addRight m)

/-- The padded value tells nothing about the value. Draw x from any distribution, and let m x be the
value to be hidden. Then x next to m x + pad has the law of x next to an independent uniform
element. -/
theorem one_time_pad_joint {H : Type} (p : PMF H) (m : H → G) :
    (p.bind fun x => (unif G).map fun r => (x, m x + r)) = prod p (unif G) :=
  bind_map_unif_joint p (fun x r => m x + r) fun x => one_time_pad (m x)

end Pad

/-! ## Part 4. Peeling: triangular systems -/

section Peel

variable {ι κ : Type} {R : ι → Type}

/-- The function g of a family r reads only the coordinates r j with `rel j i`: the coordinates
before i. -/
def ReadsBelow (rel : ι → ι → Prop) (i : ι) {Y : Type} (g : (∀ j, R j) → Y) : Prop :=
  ∀ r r' : ∀ j, R j, (∀ j, rel j i → r j = r' j) → g r = g r'

/-- A function that ignores its argument reads nothing. -/
theorem readsBelow_const (rel : ι → ι → Prop) (i : ι) {Y : Type} (y : Y) :
    ReadsBelow (R := R) rel i fun _ => y := fun _ _ _ => rfl

/-- Reading a coordinate before i is allowed. -/
theorem readsBelow_apply (rel : ι → ι → Prop) {i j : ι} (h : rel j i) :
    ReadsBelow (R := R) rel i fun r => r j :=
  fun _ _ hr => hr j h

/-- A function of a function that reads below i reads below i. -/
theorem ReadsBelow.comp {rel : ι → ι → Prop} {i : ι} {Y Z : Type} {g : (∀ j, R j) → Y}
    (hg : ReadsBelow rel i g) (u : Y → Z) :
    ReadsBelow rel i fun r => u (g r) :=
  fun r r' hr => congrArg u (hg r r' hr)

/-- If every coordinate that is before i for `rel` is before i for `rel'`, then a function that
reads below i for `rel` does so for `rel'`. -/
theorem ReadsBelow.mono {rel rel' : ι → ι → Prop} {i : ι} {Y : Type} {g : (∀ j, R j) → Y}
    (hg : ReadsBelow rel i g) (h : ∀ j, rel j i → rel' j i) : ReadsBelow rel' i g :=
  fun r r' hr => hg r r' fun j hj => hr j (h j hj)

variable [∀ i, AddCommGroup (R i)]

/-- A triangular shift is injective. Add to each coordinate i a shift t i that reads only
coordinates before i, for a well-founded "before". Then the family can be recovered from the shifted
family, one coordinate after the other. -/
theorem shear_injective (rel : ι → ι → Prop) (wf : WellFounded rel)
    (t : ∀ i, (∀ j, R j) → R i) (ht : ∀ i, ReadsBelow rel i (t i)) :
    Function.Injective fun (r : ∀ j, R j) i => t i r + r i := by
  intro r r' h
  funext i
  induction i using wf.induction with
  | _ i ih =>
    have hi : t i r + r i = t i r' + r' i := congrFun h i
    rw [ht i r r' ih] at hi
    exact add_left_cancel hi

variable [Fintype κ] [DecidableEq ι]

/-- For an injective e: the family that holds w k at the coordinate e k, and zero at the coordinates
that are not of the form e k. (In general a coordinate holds the sum of the w k with e k equal to
it.) -/
def place (e : κ → ι) (w : ∀ k, R (e k)) : ∀ j, R j := ∑ k, Pi.single (e k) (w k)

/-- For an injective e, `place` holds w k at the coordinate e k. -/
theorem place_apply {e : κ → ι} (he : Function.Injective e) (w : ∀ k, R (e k)) (k : κ) :
    place e w (e k) = w k := by
  unfold place
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · exact Pi.single_eq_same _ _
  · intro k' _ hk'
    exact Pi.single_eq_of_ne (fun h => hk' (he h).symm) _
  · intro h
    exact absurd (Finset.mem_univ k) h

variable [Fintype ι] [DecidableEq κ] [∀ i, Fintype (R i)] {V : κ → Type}
  [∀ k, AddCommGroup (V k)] [∀ k, Fintype (V k)]

/-- Peeling. The randomness is a family r of independent uniform elements r j of finite commutative
groups R j. The coordinates are ordered by a well-founded relation "before". There is one value for
each k in κ; it has its own coordinate e k (e is injective), and it is

    v k = s k r + L k (r (e k)),

where L k is additive and surjective onto V k, and the shift s k is any function that reads only
coordinates before e k.
Then the values (v k) are jointly uniform: each is uniform, and they are independent.

A parameter h in a set H (as in `peel_fin`) is a parameter of the functions s k here (the statement
holds for every s), and coordinates that are not of the form e k are randomness that shifts may read
but that masks no value of its own. `bind_map_unif` and `bind_map_unif_joint` pass from "for every
h" to an h that is drawn at random. -/
theorem peel (rel : ι → ι → Prop) (wf : WellFounded rel) (e : κ → ι) (he : Function.Injective e)
    (L : ∀ k, R (e k) →+ V k) (hL : ∀ k, Function.Surjective (L k)) (s : ∀ k, (∀ j, R j) → V k)
    (hs : ∀ k, ReadsBelow rel (e k) (s k)) :
    (unif (∀ j, R j)).map (fun r k => s k r + L k (r (e k))) = unif (∀ k, V k) := by
  -- a right inverse of each L k, as a plain function
  let σ : ∀ k, V k → R (e k) := fun k => Function.surjInv (hL k)
  have hσ : ∀ k v, L k (σ k v) = v := fun k => Function.surjInv_eq (hL k)
  -- the triangular shift on the randomness that produces the shifts s k after L k
  let t : ∀ i, (∀ j, R j) → R i := fun i r => place e (fun k => σ k (s k r)) i
  have ht : ∀ i, ReadsBelow rel i (t i) := by
    intro i r r' hr
    show place e (fun k => σ k (s k r)) i = place e (fun k => σ k (s k r')) i
    unfold place
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : e k = i
    · subst hk
      show Pi.single (e k) (σ k (s k r)) (e k) = Pi.single (e k) (σ k (s k r')) (e k)
      rw [hs k r r' hr]
    · rw [Pi.single_eq_of_ne (Ne.symm hk), Pi.single_eq_of_ne (Ne.symm hk)]
  have hΦ : Function.Bijective fun (r : ∀ j, R j) i => t i r + r i :=
    Finite.injective_iff_bijective.1 (shear_injective rel wf t ht)
  -- the additive map that applies L k to the coordinate e k
  let Λ : (∀ j, R j) →+ ∀ k, V k :=
    { toFun := fun r k => L k (r (e k))
      map_zero' := funext fun k => (L k).map_zero
      map_add' := fun a b => funext fun k => (L k).map_add (a (e k)) (b (e k)) }
  have hΛ : Function.Surjective Λ := by
    intro v
    refine ⟨place e fun k => σ k (v k), funext fun k => ?_⟩
    show L k (place e (fun k => σ k (v k)) (e k)) = v k
    rw [place_apply he, hσ]
  have hcomp : (fun (r : ∀ j, R j) k => s k r + L k (r (e k))) =
      Λ ∘ fun (r : ∀ j, R j) i => t i r + r i := by
    funext r k
    show s k r + L k (r (e k)) = L k (place e (fun k => σ k (s k r)) (e k) + r (e k))
    rw [map_add, place_apply he, hσ]
  rw [hcomp, ← PMF.map_comp, map_unif_of_bijective hΦ, map_unif_addMonoidHom Λ hΛ]

omit [Fintype κ] [DecidableEq κ] in
/-- Peeling, one value for each coordinate: `peel` with e the identity, under its hypotheses: v i =
s i r + L i (r i), where L i is additive and surjective onto V i (`hL`), "before" is well-founded
(`wf`), and s i reads only coordinates before i (`hs`); then the values (v i) are jointly uniform.
-/
theorem peel_self {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Fintype (V i)] (rel : ι → ι → Prop)
    (wf : WellFounded rel) (L : ∀ i, R i →+ V i) (hL : ∀ i, Function.Surjective (L i))
    (s : ∀ i, (∀ j, R j) → V i) (hs : ∀ i, ReadsBelow rel i (s i)) :
    (unif (∀ j, R j)).map (fun r i => s i r + L i (r i)) = unif (∀ i, V i) :=
  peel rel wf id Function.injective_id L hL s hs

/-- Peeling by levels. As `peel`, with the order given by levels: each coordinate has a level, a
natural number, and a shift reads only coordinates of lower levels than that of its value's own
coordinate. Coordinates of the same level do not read each other. -/
theorem peel_level (lv : ι → ℕ) (e : κ → ι) (he : Function.Injective e) (L : ∀ k, R (e k) →+ V k)
    (hL : ∀ k, Function.Surjective (L k)) (s : ∀ k, (∀ j, R j) → V k)
    (hs : ∀ k, ReadsBelow (fun j i => lv j < lv i) (e k) (s k)) :
    (unif (∀ j, R j)).map (fun r k => s k r + L k (r (e k))) = unif (∀ k, V k) :=
  peel (fun j i => lv j < lv i) (InvImage.wf lv Nat.lt_wfRel.wf) e he L hL s hs

end Peel

/-- Peeling for indices i < m, with a parameter h. Let H be a set and, for i < m, let L i : R i → V
i be additive and surjective and s i any function of h in H and of r 0, ..., r (i - 1). For h in H
and independent uniform r i put v i = s i (h, r 0, ..., r (i - 1)) + L i (r i). Then (v 0, ..., v (m
- 1)) is uniform, for every h. -/
theorem peel_fin {m : ℕ} {H : Type} {R V : Fin m → Type} [∀ i, AddCommGroup (R i)]
    [∀ i, Fintype (R i)] [∀ i, AddCommGroup (V i)] [∀ i, Fintype (V i)] (L : ∀ i, R i →+ V i)
    (hL : ∀ i, Function.Surjective (L i)) (s : ∀ i, H → (∀ j, R j) → V i)
    (hs : ∀ i h, ReadsBelow (· < ·) i (s i h)) (h : H) :
    (unif (∀ j, R j)).map (fun r i => s i h r + L i (r i)) = unif (∀ i, V i) :=
  peel_self (· < ·) wellFounded_lt L hL (fun i => s i h) fun i => hs i h

/-- Masked scalars are jointly uniform. The pads are independent uniform elements π j of a finite
commutative group G. The scalar number k is sent as val k π + π (e k): it is masked by its own
pad, and its value reads only pads before that one, for a well-founded "before" (for instance
because it depends on scalars that were sent masked before). Then the sent scalars are jointly
uniform. Pads that mask nothing may be read by values as well. -/
theorem masked_scalars_unif {ι κ G : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup G] [Fintype G] (rel : ι → ι → Prop) (wf : WellFounded rel) (e : κ → ι)
    (he : Function.Injective e) (val : κ → (ι → G) → G) (hval : ∀ k, ReadsBelow rel (e k) (val k)) :
    (unif (ι → G)).map (fun π k => val k π + π (e k)) = unif (κ → G) :=
  peel (R := fun _ => G) (V := fun _ => G) rel wf e he (fun _ => AddMonoidHom.id G)
    (fun _ => Function.surjective_id) val hval

/-! ## Part 5. Random tables and their laws on finite sets of places -/

section Tables

variable {P : Type} {X : P → Type}

/-- A table is a function f that holds a symbol f p of the alphabet X p at every place p.
`Agree S v f`: the table f holds at the places of S what the table v holds there. -/
def Agree (S : Finset P) (v f : ∀ p, X p) : Prop := ∀ p ∈ S, f p = v p

/-- The part of a table on the places of S. -/
def res (S : Finset P) (f : ∀ p, X p) : ∀ j : S, X j := fun j => f j

/-- Two tables have the same part on S if and only if they agree on S. -/
theorem res_eq_iff {S : Finset P} {v f : ∀ p, X p} : res S v = res S f ↔ Agree S v f :=
  ⟨fun h p hp => (congrFun h ⟨p, hp⟩).symm, fun h => funext fun j => (h j j.2).symm⟩

/-- Every assignment of symbols to the places of S is the part of a table, if there is a table at
all. -/
theorem exists_res_eq (S : Finset P) (f₀ : ∀ p, X p) (w : ∀ j : S, X j) : ∃ v, res S v = w := by
  classical
  refine ⟨fun p => if h : p ∈ S then w ⟨p, h⟩ else f₀ p, funext fun j => ?_⟩
  show (if h : (j : P) ∈ S then w ⟨j, h⟩ else f₀ j) = w j
  rw [dif_pos j.2]

open Classical in
/-- The indicator of `Agree S v f`, as a number. -/
def chi (S : Finset P) (v f : ∀ p, X p) : ℝ≥0∞ := if Agree S v f then 1 else 0

theorem chi_of_agree {S : Finset P} {v f : ∀ p, X p} (h : Agree S v f) : chi S v f = 1 := if_pos h

theorem chi_of_not_agree {S : Finset P} {v f : ∀ p, X p} (h : ¬ Agree S v f) : chi S v f = 0 :=
  if_neg h

/-- The probability of a cylinder: the probability that the random table O holds at the places of S
what v holds there. -/
def cyl (O : PMF (∀ p, X p)) (S : Finset P) (v : ∀ p, X p) : ℝ≥0∞ :=
  ∑' f, O f * chi S v f

/-- `cyl` is the probability of the event `Agree S v`. -/
theorem cyl_eq_pr (O : PMF (∀ p, X p)) (S : Finset P) (v : ∀ p, X p) :
    cyl O S v = pr O {f | Agree S v f} := by
  rw [pr_eq_tsum_indicator]
  refine tsum_congr fun f => ?_
  by_cases h : Agree S v f
  · rw [chi_of_agree h, mul_one, Set.indicator_of_mem (show f ∈ {f | Agree S v f} from h)]
  · rw [chi_of_not_agree h, mul_zero, Set.indicator_of_notMem (show f ∉ {f | Agree S v f} from h)]

/-- `cyl` is the mass of the part of v under the law of the part of the table on S. -/
theorem cyl_eq_map_res (O : PMF (∀ p, X p)) (S : Finset P) (v : ∀ p, X p) :
    cyl O S v = O.map (res S) (res S v) := by
  rw [PMF.map_apply]
  refine tsum_congr fun f => ?_
  by_cases h : Agree S v f
  · rw [chi_of_agree h, mul_one, if_pos (res_eq_iff.2 h)]
  · rw [chi_of_not_agree h, mul_zero, if_neg fun h' => h (res_eq_iff.1 h')]

/-- Two random tables have the same law on S if and only if all cylinders over S have the same
probability. -/
theorem map_res_eq_iff (O O' : PMF (∀ p, X p)) (S : Finset P) :
    O.map (res S) = O'.map (res S) ↔ ∀ v, cyl O S v = cyl O' S v := by
  constructor
  · intro h v
    rw [cyl_eq_map_res, cyl_eq_map_res, h]
  · intro h
    obtain ⟨f₀, -⟩ := O.support_nonempty
    refine PMF.ext fun w => ?_
    obtain ⟨v, rfl⟩ := exists_res_eq S f₀ w
    rw [← cyl_eq_map_res, ← cyl_eq_map_res, h]

section Finite

variable [DecidableEq P] [∀ p, Fintype (X p)]

/-- The number of assignments of symbols to the places of S. -/
theorem card_res (S : Finset P) :
    (Fintype.card (∀ j : S, X j) : ℝ≥0∞) = ∏ p ∈ S, (Fintype.card (X p) : ℝ≥0∞) := by
  rw [Fintype.card_pi, Nat.cast_prod]
  exact Finset.prod_coe_sort S fun p => (Fintype.card (X p) : ℝ≥0∞)

/-- A random table is uniform on S if and only if every cylinder over S has the probability
1 / ∏ |X p|, the product over the places of S. -/
theorem map_res_eq_unif_iff [∀ p, Nonempty (X p)] (O : PMF (∀ p, X p)) (S : Finset P) :
    O.map (res S) = unif (∀ j : S, X j) ↔
    ∀ v, cyl O S v = (∏ p ∈ S, (Fintype.card (X p) : ℝ≥0∞))⁻¹ := by
  constructor
  · intro h v
    rw [cyl_eq_map_res, h, PMF.uniformOfFintype_apply, card_res]
  · intro h
    obtain ⟨f₀, -⟩ := O.support_nonempty
    refine PMF.ext fun w => ?_
    obtain ⟨v, rfl⟩ := exists_res_eq S f₀ w
    rw [← cyl_eq_map_res, h, PMF.uniformOfFintype_apply, card_res]

end Finite

variable [DecidableEq P]

/-- To agree with v on S and to hold x at a further place p is to agree on S and p with v changed to
x at p. -/
theorem agree_insert {S : Finset P} {p : P} (hp : p ∉ S) {v f : ∀ p, X p} {x : X p} :
    Agree (insert p S) (Function.update v p x) f ↔ Agree S v f ∧ f p = x := by
  constructor
  · intro h
    refine ⟨fun q hq => ?_, ?_⟩
    · have h1 := h q (Finset.mem_insert_of_mem hq)
      rwa [Function.update_of_ne (ne_of_mem_of_not_mem hq hp)] at h1
    · have h1 := h p (Finset.mem_insert_self p S)
      rwa [Function.update_self] at h1
  · rintro ⟨h, hx⟩ q hq
    by_cases hqp : q = p
    · subst hqp
      rw [Function.update_self]
      exact hx
    · rw [Function.update_of_ne hqp]
      exact h q ((Finset.mem_insert.1 hq).resolve_left hqp)

/-- The event `Agree S v` splits by the symbol x at a further place p. -/
theorem chi_split {S : Finset P} {p : P} (hp : p ∉ S) (v f : ∀ p, X p) :
    chi S v f = ∑' x : X p, chi (insert p S) (Function.update v p x) f := by
  rw [tsum_eq_single (f p)]
  · by_cases h : Agree S v f
    · rw [chi_of_agree h, chi_of_agree ((agree_insert hp).2 ⟨h, rfl⟩)]
    · rw [chi_of_not_agree h, chi_of_not_agree fun h' => h ((agree_insert hp).1 h').1]
  · intro x hx
    exact chi_of_not_agree fun h' => hx ((agree_insert hp).1 h').2.symm

/-- The average over the random table O of the quantity g times the indicator of the event
`Agree S v` (not a conditional average). -/
def wt (O : PMF (∀ p, X p)) (S : Finset P) (v : ∀ p, X p) (g : (∀ p, X p) → ℝ≥0∞) :
    ℝ≥0∞ :=
  ∑' f, O f * chi S v f * g f

omit [DecidableEq P] in
theorem wt_const (O : PMF (∀ p, X p)) (S : Finset P) (v : ∀ p, X p) (c : ℝ≥0∞) :
    wt O S v (fun _ => c) = cyl O S v * c := by
  unfold wt cyl
  rw [ENNReal.tsum_mul_right]

omit [DecidableEq P] in
theorem wt_congr (O : PMF (∀ p, X p)) {S : Finset P} {v : ∀ p, X p} {g g' : (∀ p, X p) → ℝ≥0∞}
    (h : ∀ f, Agree S v f → g f = g' f) : wt O S v g = wt O S v g' := by
  refine tsum_congr fun f => ?_
  by_cases hf : Agree S v f
  · rw [h f hf]
  · rw [chi_of_not_agree hf, mul_zero, zero_mul, zero_mul]

omit [DecidableEq P] in
theorem wt_tsum (O : PMF (∀ p, X p)) (S : Finset P) (v : ∀ p, X p) {β : Type}
    (d : β → ℝ≥0∞) (g : β → (∀ p, X p) → ℝ≥0∞) :
    wt O S v (fun f => ∑' y, d y * g y f) = ∑' y, d y * wt O S v (g y) := by
  unfold wt
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => tsum_congr fun f => ?_
  ring

theorem wt_split (O : PMF (∀ p, X p)) {S : Finset P} {p : P} (hp : p ∉ S)
    (v : ∀ p, X p) (g : (∀ p, X p) → ℝ≥0∞) :
    wt O S v g = ∑' x : X p, wt O (insert p S) (Function.update v p x) g := by
  unfold wt
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun f => ?_
  rw [chi_split hp v f, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]

omit [DecidableEq P] in
theorem wt_empty (O : PMF (∀ p, X p)) (v : ∀ p, X p) (g : (∀ p, X p) → ℝ≥0∞) :
    wt O ∅ v g = ∑' f, O f * g f := by
  refine tsum_congr fun f => ?_
  rw [chi_of_agree (fun p hp => absurd hp (Finset.notMem_empty p)), mul_one]

end Tables

/-! ## Part 6. Adaptive queries -/

/-- An algorithm that reads a table, as a decision tree. It ends with an output, or reads the place
p and goes on by the symbol that it finds there, or draws y from a distribution d of its own choice
and goes on by y. So each place that it reads may depend on all the symbols that it has seen and on
all its coins. Every run ends, since a tree has no infinite branch; there is no bound on the number
of steps, and the functions k are arbitrary, computable or not. -/
inductive Reader (P : Type) (X : P → Type) (α : Type) : Type 1
  | done (a : α) : Reader P X α
  | read (p : P) (k : X p → Reader P X α) : Reader P X α
  | draw (β : Type) (d : PMF β) (k : β → Reader P X α) : Reader P X α

namespace Reader

variable {P : Type} {X : P → Type} {α : Type}

/-- The law of the output of the algorithm on the table f. -/
def run : Reader P X α → (∀ p, X p) → PMF α
  | done a, _ => PMF.pure a
  | read p k, f => (k (f p)).run f
  | draw _ d k, f => d.bind fun y => (k y).run f

@[simp] theorem run_done (a : α) (f : ∀ p, X p) : (done a : Reader P X α).run f = PMF.pure a := rfl

@[simp] theorem run_read (p : P) (k : X p → Reader P X α) (f : ∀ p, X p) :
    (read p k).run f = (k (f p)).run f := rfl

@[simp] theorem run_draw (β : Type) (d : PMF β) (k : β → Reader P X α) (f : ∀ p, X p) :
    (draw β d k).run f = d.bind fun y => (k y).run f := rfl

variable [DecidableEq P]

/-- "c.Within good S": if the places of S have been read before, then whatever answers the algorithm
c receives and however its coins fall, the set of all places read when it ends is good. "Whatever
answers" is meant literally: also coins of probability zero, and also an answer at a repeated place
that differs from the first answer there, which no table gives. An algorithm that notes its answers
and reads no place twice is not affected by the last point. -/
def Within (good : Finset P → Prop) : Reader P X α → Finset P → Prop
  | done _, S => good S
  | read p k, S => ∀ x, (k x).Within good (insert p S)
  | draw _ _ k, S => ∀ y, (k y).Within good S

theorem within_done {good : Finset P → Prop} {a : α} {S : Finset P} :
    (done a : Reader P X α).Within good S ↔ good S := Iff.rfl

theorem within_read {good : Finset P → Prop} {p : P} {k : X p → Reader P X α} {S : Finset P} :
    (read p k).Within good S ↔ ∀ x, (k x).Within good (insert p S) := Iff.rfl

theorem within_draw {good : Finset P → Prop} {β : Type} {d : PMF β}
    {k : β → Reader P X α} {S : Finset P} :
    (draw β d k).Within good S ↔ ∀ y, (k y).Within good S := Iff.rfl

/-- Without a condition on the sets, every algorithm is within. -/
theorem within_true (c : Reader P X α) (S : Finset P) : c.Within (fun _ => True) S := by
  induction c generalizing S with
  | done a => trivial
  | read p k ih => exact fun x => ih x _
  | draw β d k ih => exact fun y => ih y _

/-- A weaker condition on the sets. -/
theorem Within.mono {good good' : Finset P → Prop} (h : ∀ S, good S → good' S) {c : Reader P X α}
    {S : Finset P} (hc : c.Within good S) : c.Within good' S := by
  induction c generalizing S with
  | done a => exact h S hc
  | read p k ih => exact fun x => ih x (hc x)
  | draw β d k ih => exact fun y => ih y (hc y)

/-! ### One algorithm after another -/

/-- First c, then g on the output of c. -/
def bind {β : Type} : Reader P X α → (α → Reader P X β) → Reader P X β
  | done a, g => g a
  | read p k, g => read p fun x => (k x).bind g
  | draw γ d k, g => draw γ d fun y => (k y).bind g

omit [DecidableEq P] in
/-- The law of the output of "first c, then g", on a fixed table. -/
theorem run_bind {β : Type} (c : Reader P X α) (g : α → Reader P X β) (f : ∀ p, X p) :
    (c.bind g).run f = (c.run f).bind fun a => (g a).run f := by
  induction c with
  | done a => simp only [bind, run_done, PMF.pure_bind]
  | read p k ih => exact ih (f p)
  | draw γ d k ih => simp only [bind, run_draw, ih, PMF.bind_bind]

/-- "First c, then g" stays within the good sets if c ends only at sets from which every g a stays
within them. -/
theorem within_bind {β : Type} {good : Finset P → Prop} (c : Reader P X α) (g : α → Reader P X β)
    (S : Finset P) (h : c.Within (fun T => ∀ a, (g a).Within good T) S) :
    (c.bind g).Within good S := by
  induction c generalizing S with
  | done a => exact h a
  | read p k ih => exact fun x => ih x _ (h x)
  | draw γ d k ih => exact fun y => ih y _ (h y)

/-- If c, started after the places of S, ends with at most b places read, then c, started after the
places of S and T, ends with at most b + |T| places read. -/
theorem Within.union_card {b : ℕ} {c : Reader P X α} {S : Finset P}
    (hc : c.Within (fun S => S.card ≤ b) S) (T : Finset P) :
    c.Within (fun S => S.card ≤ b + T.card) (S ∪ T) := by
  induction c generalizing S with
  | done a => exact (Finset.card_union_le S T).trans (Nat.add_le_add_right hc _)
  | read p k ih =>
    intro x
    have h1 := ih x (hc x)
    rwa [Finset.insert_union] at h1
  | draw γ d k ih => exact fun y => ih y (hc y)

/-! ### The proof of "Reader.law_eq" -/

omit [DecidableEq P] in
/-- One step of a run, on the event that the table agrees with v on S: a place of S. -/
theorem wt_read_old (O : PMF (∀ p, X p)) {S : Finset P} (v : ∀ p, X p) {p : P} (hp : p ∈ S)
    (k : X p → Reader P X α) (a : α) :
    wt O S v (fun f => (read p k).run f a) = wt O S v fun f => (k (v p)).run f a :=
  wt_congr O fun f hf => by rw [run_read, hf p hp]

/-- One step of a run: a new place. The event splits by the symbol x that the place holds. -/
theorem wt_read_new (O : PMF (∀ p, X p)) {S : Finset P} (v : ∀ p, X p) {p : P} (hp : p ∉ S)
    (k : X p → Reader P X α) (a : α) :
    wt O S v (fun f => (read p k).run f a) =
      ∑' x, wt O (insert p S) (Function.update v p x) fun f => (k x).run f a := by
  rw [wt_split O hp]
  refine tsum_congr fun x => wt_congr O fun f hf => ?_
  rw [run_read, ((agree_insert hp).1 hf).2]

omit [DecidableEq P] in
/-- One step of a run: a draw. -/
theorem wt_draw (O : PMF (∀ p, X p)) (S : Finset P) (v : ∀ p, X p) (β : Type) (d : PMF β)
    (k : β → Reader P X α) (a : α) :
    wt O S v (fun f => (draw β d k).run f a) = ∑' y, d y * wt O S v fun f => (k y).run f a :=
  wt_tsum O S v d fun y f => (k y).run f a

/-- Adaptive queries, in the middle of a run. Let all cylinders over good sets have the same
probability under O and under O'. Let the places of S have been read, with the answers v, and let c
stay within the good sets from there on. Then the event "the table holds v on S, and c ends with a"
has the same probability for both tables. -/
theorem wt_eq {good : Finset P → Prop} {O O' : PMF (∀ p, X p)}
    (h : ∀ S, good S → ∀ v, cyl O S v = cyl O' S v) (c : Reader P X α) (a : α) (S : Finset P)
    (v : ∀ p, X p) (hc : c.Within good S) :
    wt O S v (fun f => c.run f a) = wt O' S v fun f => c.run f a := by
  induction c generalizing S v with
  | done b =>
    simp only [run_done]
    rw [wt_const, wt_const, h S hc v]
  | read p k ih =>
    by_cases hp : p ∈ S
    · rw [wt_read_old O v hp, wt_read_old O' v hp]
      have h1 := hc (v p)
      rw [Finset.insert_eq_of_mem hp] at h1
      exact ih (v p) S v h1
    · rw [wt_read_new O v hp, wt_read_new O' v hp]
      exact tsum_congr fun x => ih x _ _ (hc x)
  | draw β d k ih =>
    rw [wt_draw, wt_draw]
    exact tsum_congr fun y => by rw [ih y S v (hc y)]

/-- Adaptive queries, for a family of good sets of places. If two random tables have the same law on
every good set of places, then an algorithm whose set of places read is always good has the same law
of outputs on both.

The family of good sets can carry more than a number of places: a budget for each row of a table
with places (row, position);
or, if the table to be read is chosen only during the run, places (choice, position) and the sets
that use one choice only. -/
theorem law_eq {good : Finset P → Prop} {O O' : PMF (∀ p, X p)}
    (h : ∀ S, good S → O.map (res S) = O'.map (res S)) (c : Reader P X α) (hc : c.Within good ∅) :
    O.bind c.run = O'.bind c.run := by
  refine PMF.ext fun a => ?_
  obtain ⟨v, -⟩ := O.support_nonempty
  calc (O.bind c.run) a = wt O ∅ v (fun f => c.run f a) := (wt_empty O v fun f => c.run f a).symm
    _ = wt O' ∅ v (fun f => c.run f a) :=
      wt_eq (fun S hS => (map_res_eq_iff O O' S).1 (h S hS)) c a ∅ v hc
    _ = (O'.bind c.run) a := wt_empty O' v fun f => c.run f a

variable [∀ p, Fintype (X p)] [∀ p, Nonempty (X p)]


end Reader

/-! ## Part 7. Uniform tables; rows and tables side by side -/

section Uniform

variable {P : Type} [DecidableEq P] {X : P → Type} [∀ p, Fintype (X p)] [∀ p, Nonempty (X p)]

/-- The uniform table is uniform on every set of places. -/
theorem map_unif_res [Fintype P] (S : Finset P) :
    (unif (∀ p, X p)).map (res S) = unif (∀ j : S, X j) :=
  calc (unif (∀ p, X p)).map (res S)
      = ((unif (∀ p, X p)).map (Equiv.piEquivPiSubtypeProd (fun p => p ∈ S) X)).map Prod.fst :=
        map_eq_map_map _ fun _ => rfl
    _ = unif (∀ j : S, X j) := by rw [map_unif_equiv, map_fst_unif]

/-- Rows side by side. Row r of a table is computed from its own seed, the seeds independent and
uniform, and each row is uniform on the set S of places. Then the table whose place p holds the
column of all rows' symbols at p is uniform on S: rows and places are independent. -/
theorem map_unif_rows {Rw : Type} [Fintype Rw] [DecidableEq Rw] {Ω : Rw → Type} [∀ r, Fintype (Ω r)]
    [∀ r, Nonempty (Ω r)] {Y : Rw → P → Type} [∀ r p, Fintype (Y r p)] [∀ r p, Nonempty (Y r p)]
    (w : ∀ r, Ω r → ∀ p, Y r p) (S : Finset P)
    (h : ∀ r, (unif (Ω r)).map (fun ω => fun j : S => w r ω j) = unif (∀ j : S, Y r j)) :
    (unif (∀ r, Ω r)).map (fun ω => fun j : S => fun r => w r (ω r) j) =
      unif (∀ j : S, ∀ r, Y r j) :=
  calc (unif (∀ r, Ω r)).map (fun ω => fun j : S => fun r => w r (ω r) j)
      = ((unif (∀ r, Ω r)).map fun ω r => fun j : S => w r (ω r) j).map
          (Equiv.piComm fun (r : Rw) (j : S) => Y r j) := map_eq_map_map _ fun _ => rfl
    _ = unif (∀ j : S, ∀ r, Y r j) := by
        rw [map_unif_pi (fun r ω => fun j : S => w r ω j) h, map_unif_equiv]

/-- Two tables side by side, computed from independent uniform seeds (for instance symbols and
salts). If both are uniform on the set S of places, then so is the table whose place p holds the
pair of the two symbols at p. -/
theorem map_unif_pair {Ω₁ Ω₂ : Type} [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
    {X₂ : P → Type} [∀ p, Fintype (X₂ p)] [∀ p, Nonempty (X₂ p)] (w₁ : Ω₁ → ∀ p, X p)
    (w₂ : Ω₂ → ∀ p, X₂ p) (S : Finset P)
    (h₁ : (unif Ω₁).map (fun ω => fun j : S => w₁ ω j) = unif (∀ j : S, X j))
    (h₂ : (unif Ω₂).map (fun ω => fun j : S => w₂ ω j) = unif (∀ j : S, X₂ j)) :
    (unif (Ω₁ × Ω₂)).map (fun ω => fun j : S => (w₁ ω.1 j, w₂ ω.2 j)) =
      unif (∀ j : S, X j × X₂ j) := by
  have hzip : Function.Bijective fun (z : (∀ j : S, X j) × (∀ j : S, X₂ j)) (j : S) =>
      (z.1 j, z.2 j) :=
    ⟨fun z z' hz => Prod.ext (funext fun j => congrArg Prod.fst (congrFun hz j))
        (funext fun j => congrArg Prod.snd (congrFun hz j)),
      fun u => ⟨(fun j => (u j).1, fun j => (u j).2), rfl⟩⟩
  calc
    (unif (Ω₁ × Ω₂)).map (fun ω => fun j : S => (w₁ ω.1 j, w₂ ω.2 j)) =
        ((unif (Ω₁ × Ω₂)).map fun ω => ((fun j : S => w₁ ω.1 j), (fun j : S => w₂ ω.2 j))).map
          (fun (z : (∀ j : S, X j) × (∀ j : S, X₂ j)) (j : S) => (z.1 j, z.2 j)) :=
      map_eq_map_map _ fun _ => rfl
    _ = unif (∀ j : S, X j × X₂ j) := by
        rw [map_unif_prodMap (fun ω => fun j : S => w₁ ω j) (fun ω => fun j : S => w₂ ω j) h₁ h₂,
          map_unif_of_bijective hzip]

end Uniform

end Prob
