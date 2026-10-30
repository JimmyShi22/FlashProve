--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/FreshWide.lean: random entries under codes with random tails, with several out-of-domain
answers, each with a pad of its own: the joint distribution of three things that are made of them:
the symbols that are read, the answers, and a linear image of the entries. It widens the statement
`fresh_core` of Code/FreshCore.lean (one pad, one answer, the entries themselves), which it does not
import: `fresh_wide_core` has that statement's text and is one call of `fresh_wide_one`: where both
files stand in one library, `Code` has two theorems of one statement, `fresh_core` and
`fresh_wide_core`. Statements of linear algebra and counting over a finite field; no protocol occurs
in them.

THE COINS, uniform and independent: t: the tails of all rows that are read. p: one pad for each
answer. k: entries. Everything else is fixed, arbitrary, and bound outside the distribution: all
coefficients, the constants c0, a0 and c, the positions, the factors beta, the function f. THE THREE
COMPONENTS, each an affine function of the coins:
  the symbols   c0 + (what the tails add + what the pads add + what the entries add)
  the answers   for each a: a0 a + (beta a times the pad p a + a linear form of the entries): A PAD
                STANDS IN ITS OWN ANSWER ALONE
  the image     c + M k, M linear
If the tails' shares take all patterns on what is read, every beta a is not 0, and M is onto, the
map from the coins to the triple is affine and ONTO: solve k from the image, then each p a from its
answer, then t from the symbols. An affine map that is onto has fibres of one size, so it carries
the uniform distribution to the uniform distribution (`map_uniform_of_surjective`,
Code/QueryUniform.lean).

  WideLaw g       the conclusion, as a proposition about a map g from coins to values: whatever is
                  made of g, over uniform coins, has the distribution of the same made of a uniform
                  value. wideLaw_iff, WideLaw.congr, WideLaw.comp_equiv, WideLaw.comp_law,
                  WideLaw.of_coins, wideLaw_of_onto: tools
  triHom, triHom_onto, tri_law   THE BARE FORM: additive maps of finite commutative groups,
                  triangular:
                  the symbols hang on all three coins, the answers on pads and entries, the image on
                  the entries alone; the three maps on the diagonal are onto
  prodMap_onto    a product of maps that are onto is onto: for rows under different codes
  padHom, padHom_onto   the answers' diagonal: each pad times its factor
  fresh_wide      **the statement in coordinates**, under one abstract code phi and set S.
                  Arguments in the order of `fresh_core`, with M and hM in front of c:
                  phi S hS bp c0 bk ak M hM c a0 beta hbeta
  fresh_wide_map  the same as an equation of distributions, with f written out
  fresh_wide_one  one pad and one answer, as plain elements: the coins and the triple have the
                  types of `fresh_core`, but for the image
  fresh_wide_core, fresh_wide_one_equiv   `fresh_core`'s own text; one pad, and the image by a
                  bijection
  fresh_wide_table   several rows under one code: a position holds a column
  fresh_wide_equiv   the image by a bijection E of the entries that need not be linear
  blockEquiv, blockEquiv_on, blockEquiv_off   a bijection of the entries at some places, carried to
                  all entries: elsewhere it leaves them as they are. Such bijections at several sets
                  of places are composed (Equiv.trans); the composite is each of them at its own
                  places WHERE THE SETS OF PLACES ARE DISJOINT (blockEquiv_two)

How it is meant to be read. With A a single answer and M the identity: `fresh_core`. Entries that
are left out of the image (M forgets them) stay among the coins. For rows under different codes, or
messages with different sets of positions: the bare form, with products.

What is assumed. The tails' shares take all patterns on S: Surjective (restr phi S); for a set of at
most b positions that is OntoUpTo phi b. S counts DISTINCT positions, over all lists at which a row
is read. Every beta a is not 0. M is onto: THE ROWS OF M ARE LINEARLY INDEPENDENT FORMS OF THE
ENTRIES: never more values in the image than entries; fewer are allowed. One entry that stands in
two values, and nothing else in them, gives no such M (said here without a theorem). Where a second
value has a further entry in it, that entry has to be among the coins k; if it lies in another
message, that message's tails, pads, positions and answers come among the coins and the components
too (the bare form, with products); and the form itself: no tail in an answer or in the image, no
pad in the image or in another's answer. What is not claimed. That any code, row, answer or scalar
of a protocol has this form. That an honest prover samples t, p and k uniformly. How many positions
of a row a run reads. Anything where what is fixed here is sampled, or is a function of what was
sent. Nothing on what else hangs on these values. That the map is one to one. That the premises are
needed: they are sufficient; where entries are left out of the image the law can hold without the
first two (said here without a theorem). Which entries a run spends, that each is spent once, that
the
spenders' places are disjoint. The joint distribution over several owners' coins, from statements on
each owner's. What holds where a factor that a run samples is 0. Nothing on a run, a verifier or a
view. A pad of several entries is not of the form in coordinates; the bare form serves it. No
property of a protocol is claimed.

-/
import Code.QueryUniform
import Prob.LawKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Code
open Function (Surjective)

/-! ## The conclusion, as a proposition -/

section Law

variable {C Y Y' : Type} [Fintype C] [Nonempty C] [Fintype Y] [Nonempty Y] [Fintype Y']
  [Nonempty Y']

/-- Whatever is made of g, over uniform coins, has the distribution of the same made of a uniform
value. -/
def WideLaw (g : C → Y) : Prop :=
  ∀ (γ : Type) (f : Y → γ), (Prob.unif C).map (fun x => f (g x)) = (Prob.unif Y).map f

/-- It says that g carries the uniform distribution to the uniform distribution. -/
theorem wideLaw_iff (g : C → Y) : WideLaw g ↔ (Prob.unif C).map g = Prob.unif Y := by
  constructor
  · intro h
    have := h Y id
    rw [PMF.map_id] at this
    exact this
  · intro h γ f
    have e : (Prob.unif C).map (fun x => f (g x)) = ((Prob.unif C).map g).map f := by
      rw [PMF.map_comp]
      rfl
    rw [e, h]

/-- It goes along an equation of maps. -/
theorem WideLaw.congr {g g' : C → Y} (h : WideLaw g) (e : ∀ x, g x = g' x) : WideLaw g' := by
  have : g = g' := funext e
  rw [← this]
  exact h

/-- It goes on behind a map that has the law. -/
theorem WideLaw.comp_law {g : C → Y} (h : WideLaw g) {u : Y → Y'} (hu : WideLaw u) :
    WideLaw fun x => u (g x) := by
  intro γ f
  rw [h γ fun y => f (u y)]
  exact hu γ f

/-- A bijection has the law. -/
theorem wideLaw_equiv (e : Y ≃ Y') : WideLaw e :=
  (wideLaw_iff _).2 (Prob.map_unif_equiv e)

/-- It goes on behind a bijection of the values. -/
theorem WideLaw.comp_equiv {g : C → Y} (h : WideLaw g) (e : Y ≃ Y') : WideLaw fun x => e (g x) :=
  h.comp_law (wideLaw_equiv e)

/-- It goes on in front of a bijection of the coins. -/
theorem WideLaw.of_coins {C' : Type} [Fintype C'] [Nonempty C'] {g : C → Y} (h : WideLaw g)
    (e : C' ≃ C) : WideLaw fun x => g (e x) :=
  (wideLaw_equiv e).comp_law h

end Law

/-! ## The bare form -/

section Tri

variable {T P Q Y R Z : Type} [AddCommGroup T] [AddCommGroup P] [AddCommGroup Q] [AddCommGroup Y]
  [AddCommGroup R] [AddCommGroup Z]

/-- The linear part: triangular: the symbols hang on all three coins, the answers on pads and
entries, the image on the entries alone. -/
def triHom (Φ : T →+ Y) (B₁ : P →+ Y) (B₂ : Q →+ Y) (D : P →+ R) (B₃ : Q →+ R) (M : Q →+ Z) :
    T × P × Q →+ Y × R × Z :=
  AddMonoidHom.mk' (fun x => (Φ x.1 + B₁ x.2.1 + B₂ x.2.2, D x.2.1 + B₃ x.2.2, M x.2.2))
    (by
      intro a b
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show Φ (a.1 + b.1) + B₁ (a.2.1 + b.2.1) + B₂ (a.2.2 + b.2.2) =
          (Φ a.1 + B₁ a.2.1 + B₂ a.2.2) + (Φ b.1 + B₁ b.2.1 + B₂ b.2.2)
        rw [map_add, map_add, map_add]
        abel
      · show D (a.2.1 + b.2.1) + B₃ (a.2.2 + b.2.2) =
          (D a.2.1 + B₃ a.2.2) + (D b.2.1 + B₃ b.2.2)
        rw [map_add, map_add]
        abel
      · exact map_add M a.2.2 b.2.2)

/-- It is onto, if the three maps on the diagonal are. -/
theorem triHom_onto (Φ : T →+ Y) (B₁ : P →+ Y) (B₂ : Q →+ Y) (D : P →+ R) (B₃ : Q →+ R)
    (M : Q →+ Z) (hΦ : Surjective Φ) (hD : Surjective D) (hM : Surjective M) :
    Surjective (triHom Φ B₁ B₂ D B₃ M) := by
  rintro ⟨y, r, z⟩
  obtain ⟨k, hk⟩ := hM z
  obtain ⟨p, hp⟩ := hD (r - B₃ k)
  obtain ⟨t, ht⟩ := hΦ (y - B₁ p - B₂ k)
  refine ⟨(t, p, k), Prod.ext ?_ (Prod.ext ?_ hk)⟩
  · show Φ t + B₁ p + B₂ k = y
    rw [ht]
    abel
  · show D p + B₃ k = r
    rw [hp]
    abel

/-- **The bare form**: over uniform (t, p, k), the triple c + (Φ t + B₁ p + B₂ k, D p + B₃ k, M k)
has the law, if Φ, D and M are onto. -/
theorem tri_law [Fintype T] [Fintype P] [Fintype Q] [Fintype Y] [Fintype R] [Fintype Z]
    (Φ : T →+ Y) (B₁ : P →+ Y) (B₂ : Q →+ Y) (D : P →+ R) (B₃ : Q →+ R) (M : Q →+ Z)
    (hΦ : Surjective Φ) (hD : Surjective D) (hM : Surjective M) (c : Y × R × Z) :
    WideLaw fun x => c + triHom Φ B₁ B₂ D B₃ M x :=
  (wideLaw_iff _).2
    (map_uniform_of_surjective (triHom Φ B₁ B₂ D B₃ M) (triHom_onto Φ B₁ B₂ D B₃ M hΦ hD hM) c)

/-- An additive map that is onto, followed by a translation, has the law. -/
theorem wideLaw_of_onto {G H : Type} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (h : G →+ H) (ho : Surjective h) (c : H) : WideLaw fun x => c + h x :=
  (wideLaw_iff _).2 (map_uniform_of_surjective h ho c)

/-- A product of maps that are onto is onto. -/
theorem prodMap_onto {T' Y' : Type} [AddCommGroup T'] [AddCommGroup Y'] (Φ : T →+ Y)
    (Φ' : T' →+ Y') (h : Surjective Φ) (h' : Surjective Φ') : Surjective (Φ.prodMap Φ') :=
  fun y => by
    obtain ⟨t, ht⟩ := h y.1
    obtain ⟨t', ht'⟩ := h' y.2
    exact ⟨(t, t'), Prod.ext ht ht'⟩

end Tri

/-! ## In coordinates -/

section Coord

variable {K : Type} [Field K] {A J I : Type}

/-- Each pad times its factor. -/
def padHom (β : A → K) : (A → K) →+ (A → K) :=
  AddMonoidHom.mk' (fun p a => β a * p a) (by
    intro p q
    funext a
    exact mul_add (β a) (p a) (q a))

/-- It is onto, if no factor is 0. -/
theorem padHom_onto (β : A → K) (hβ : ∀ a, β a ≠ 0) : Surjective (padHom β) := fun y =>
  ⟨fun a => y a / β a, funext fun a => mul_div_cancel₀ (y a) (hβ a)⟩

variable [Fintype A] [Fintype J]

/-- A family of coefficients, as an additive map: x goes to the sums of x i times b i. -/
def sumHom {N O : Type} [Fintype N] (b : N → O → K) : (N → K) →+ (O → K) :=
  AddMonoidHom.mk' (fun x o => ∑ i, x i * b i o) (by
    intro x y
    funext o
    show ∑ i, (x i + y i) * b i o = ∑ i, x i * b i o + ∑ i, y i * b i o
    simp only [add_mul, Finset.sum_add_distrib])

variable {V : Type} [AddCommGroup V] [Module K V] {ι : Type}

/-- **Over uniform (tails, pads, entries): (the symbols on S, the answers, c + M of the entries) has
the law.** Arguments in the order of `fresh_core`, with M and hM in front of c. -/
theorem fresh_wide [Fintype K] [Fintype V] [Fintype I] [DecidableEq ι] [DecidableEq A]
    [DecidableEq J] [DecidableEq I] (φ : V →ₗ[K] (ι → K)) (S : Finset ι)
    (hS : Surjective (restr φ S)) (bp : A → S → K) (c0 : S → K) (bk : J → S → K) (ak : A → J → K)
    (M : (J → K) →ₗ[K] (I → K)) (hM : Surjective M) (c : I → K) (a0 β : A → K)
    (hβ : ∀ a, β a ≠ 0) :
    WideLaw fun x : V × (A → K) × (J → K) =>
      ((fun j => c0 j + (φ x.1 j.1 + ∑ a, x.2.1 a * bp a j + ∑ i, x.2.2 i * bk i j),
        fun a => a0 a + (β a * x.2.1 a + ∑ i, ak a i * x.2.2 i),
        fun i => c i + M x.2.2 i) : (S → K) × (A → K) × (I → K)) := by
  have h := tri_law (restr φ S).toAddMonoidHom (sumHom bp) (sumHom bk) (padHom β)
    (sumHom fun (i : J) (a : A) => ak a i) M.toAddMonoidHom hS (padHom_onto β hβ) hM (c0, a0, c)
  refine h.congr fun x => Prod.ext rfl (Prod.ext ?_ rfl)
  funext a
  show a0 a + (β a * x.2.1 a + ∑ i, x.2.2 i * ak a i) =
    a0 a + (β a * x.2.1 a + ∑ i, ak a i * x.2.2 i)
  simp only [mul_comm]

/-- The same, as an equation of distributions. -/
theorem fresh_wide_map [Fintype K] [Fintype V] [Fintype I] [DecidableEq ι] [DecidableEq A]
    [DecidableEq J] [DecidableEq I] {γ : Type} (φ : V →ₗ[K] (ι → K)) (S : Finset ι)
    (hS : Surjective (restr φ S)) (bp : A → S → K) (c0 : S → K) (bk : J → S → K) (ak : A → J → K)
    (M : (J → K) →ₗ[K] (I → K)) (hM : Surjective M) (c : I → K) (a0 β : A → K)
    (hβ : ∀ a, β a ≠ 0) (f : (S → K) × (A → K) × (I → K) → γ) :
    (Prob.unif (V × (A → K) × (J → K))).map (fun x => f
        (fun j => c0 j + (φ x.1 j.1 + ∑ a, x.2.1 a * bp a j + ∑ i, x.2.2 i * bk i j),
          fun a => a0 a + (β a * x.2.1 a + ∑ i, ak a i * x.2.2 i), fun i => c i + M x.2.2 i)) =
      (Prob.unif ((S → K) × (A → K) × (I → K))).map f :=
  fresh_wide φ S hS bp c0 bk ak M hM c a0 β hβ γ f

/-- One pad and one answer, as plain elements. -/
theorem fresh_wide_one [Fintype K] [Fintype V] [Fintype I] [DecidableEq ι] [DecidableEq J]
    [DecidableEq I] (φ : V →ₗ[K] (ι → K)) (S : Finset ι) (hS : Surjective (restr φ S))
    (bp c0 : S → K) (bk : J → S → K) (ak : J → K) (M : (J → K) →ₗ[K] (I → K)) (hM : Surjective M)
    (c : I → K) (a0 β : K) (hβ : β ≠ 0) :
    WideLaw fun x : V × K × (J → K) =>
      ((fun j => c0 j + (φ x.1 j.1 + x.2.1 * bp j + ∑ i, x.2.2 i * bk i j),
        a0 + (β * x.2.1 + ∑ i, ak i * x.2.2 i), fun i => c i + M x.2.2 i) :
        (S → K) × K × (I → K)) := by
  have h := tri_law (restr φ S).toAddMonoidHom
    (AddMonoidHom.mk' (fun (p : K) (j : S) => p * bp j) (by
      intro p q
      funext j
      exact add_mul p q (bp j)))
    (sumHom bk) (AddMonoidHom.mulLeft β)
    (AddMonoidHom.mk' (fun k : J → K => ∑ i, ak i * k i) (by
      intro k k'
      show ∑ i, ak i * (k i + k' i) = ∑ i, ak i * k i + ∑ i, ak i * k' i
      simp only [mul_add, Finset.sum_add_distrib]))
    M.toAddMonoidHom hS (fun y => ⟨y / β, mul_div_cancel₀ y hβ⟩) hM (c0, a0, c)
  exact h.congr fun x => rfl

/-- The statement `fresh_core` of Code/FreshCore.lean, in its own text: one call of
`fresh_wide_one`, at the identity. -/
theorem fresh_wide_core [Fintype K] [Fintype V] [DecidableEq ι] [DecidableEq J] {γ : Type}
    (φ : V →ₗ[K] (ι → K)) (S : Finset ι) (hS : Function.Surjective (restr φ S))
    (bp c0 : S → K) (bk : J → S → K) (ak c : J → K) (a0 β : K) (hβ : β ≠ 0)
    (f : (S → K) × K × (J → K) → γ) :
    (Prob.unif (V × K × (J → K))).map (fun x => f
        (fun j => c0 j + (φ x.1 j.1 + x.2.1 * bp j + ∑ i, x.2.2 i * bk i j),
          a0 + (β * x.2.1 + ∑ i, ak i * x.2.2 i), fun i => c i + x.2.2 i)) =
      (Prob.unif ((S → K) × K × (J → K))).map f :=
  fresh_wide_one φ S hS bp c0 bk ak LinearMap.id (fun y => ⟨y, rfl⟩) c a0 β hβ γ f

/-- One pad and one answer, as plain elements; the image by a bijection of the entries that need not
be linear. -/
theorem fresh_wide_one_equiv [Fintype K] [Fintype V] [DecidableEq ι] [DecidableEq J] {W : Type}
    [Fintype W] [Nonempty W] (φ : V →ₗ[K] (ι → K)) (S : Finset ι) (hS : Surjective (restr φ S))
    (bp c0 : S → K) (bk : J → S → K) (ak : J → K) (E : (J → K) ≃ W) (a0 β : K) (hβ : β ≠ 0) :
    WideLaw fun x : V × K × (J → K) =>
      ((fun j => c0 j + (φ x.1 j.1 + x.2.1 * bp j + ∑ i, x.2.2 i * bk i j),
        a0 + (β * x.2.1 + ∑ i, ak i * x.2.2 i), E x.2.2) : (S → K) × K × W) := by
  have h := fresh_wide_one φ S hS bp c0 bk ak LinearMap.id (fun y => ⟨y, rfl⟩) 0 a0 β hβ
  have h' := h.comp_equiv ((Equiv.refl (S → K)).prodCongr ((Equiv.refl K).prodCongr E))
  refine h'.congr fun x => Prod.ext rfl (Prod.ext rfl ?_)
  show E (fun i => (0 : J → K) i + x.2.2 i) = E x.2.2
  congr 1
  funext i
  exact zero_add _

/-- Several rows under one code: tails for each row of R; a position holds a column. -/
theorem fresh_wide_table [Fintype K] [Fintype V] [Fintype I] [DecidableEq ι] [DecidableEq A]
    [DecidableEq J] [DecidableEq I] {R : Type} [Fintype R] [DecidableEq R]
    (φ : V →ₗ[K] (ι → K)) (b : ℕ) (hφ : OntoUpTo φ b) (S : Finset ι) (hS : S.card ≤ b)
    (bp : A → S → R → K) (c0 : S → R → K) (bk : J → S → R → K) (ak : A → J → K)
    (M : (J → K) →ₗ[K] (I → K)) (hM : Surjective M) (c : I → K) (a0 β : A → K)
    (hβ : ∀ a, β a ≠ 0) :
    WideLaw fun x : (R → V) × (A → K) × (J → K) =>
      ((fun j ρ => c0 j ρ + (φ (x.1 ρ) j.1 + ∑ a, x.2.1 a * bp a j ρ + ∑ i, x.2.2 i * bk i j ρ),
        fun a => a0 a + (β a * x.2.1 a + ∑ i, ak a i * x.2.2 i),
        fun i => c i + M x.2.2 i) : (S → R → K) × (A → K) × (I → K)) := by
  have hp : ∀ {N : Type} [Fintype N] (w : N → S → R → K), ∃ B : (N → K) →+ (S → R → K),
      ∀ x j ρ, B x j ρ = ∑ i, x i * w i j ρ := fun w =>
    ⟨AddMonoidHom.mk' (fun x j ρ => ∑ i, x i * w i j ρ) (by
      intro x y
      funext j ρ
      show ∑ i, (x i + y i) * w i j ρ = ∑ i, x i * w i j ρ + ∑ i, y i * w i j ρ
      simp only [add_mul, Finset.sum_add_distrib]), fun _ _ _ => rfl⟩
  obtain ⟨B₁, h₁⟩ := hp bp
  obtain ⟨B₂, h₂⟩ := hp bk
  have h := tri_law (restrTable φ R S) B₁ B₂ (padHom β)
    (sumHom fun (i : J) (a : A) => ak a i) M.toAddMonoidHom (hφ.surjective_restrTable hS)
    (padHom_onto β hβ) hM (c0, a0, c)
  refine h.congr fun x => Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext j ρ
    show c0 j ρ + (φ (x.1 ρ) j.1 + B₁ x.2.1 j ρ + B₂ x.2.2 j ρ) = _
    rw [h₁, h₂]
  · funext a
    show a0 a + (β a * x.2.1 a + ∑ i, x.2.2 i * ak a i) =
      a0 a + (β a * x.2.1 a + ∑ i, ak a i * x.2.2 i)
    simp only [mul_comm]

/-- The image by a bijection of the entries that need not be linear. -/
theorem fresh_wide_equiv [Fintype K] [Fintype V] [DecidableEq ι] [DecidableEq A] [DecidableEq J]
    {W : Type} [Fintype W] [Nonempty W] (φ : V →ₗ[K] (ι → K)) (S : Finset ι)
    (hS : Surjective (restr φ S)) (bp : A → S → K) (c0 : S → K) (bk : J → S → K) (ak : A → J → K)
    (E : (J → K) ≃ W) (a0 β : A → K) (hβ : ∀ a, β a ≠ 0) :
    WideLaw fun x : V × (A → K) × (J → K) =>
      ((fun j => c0 j + (φ x.1 j.1 + ∑ a, x.2.1 a * bp a j + ∑ i, x.2.2 i * bk i j),
        fun a => a0 a + (β a * x.2.1 a + ∑ i, ak a i * x.2.2 i), E x.2.2) :
        (S → K) × (A → K) × W) := by
  have h := fresh_wide φ S hS bp c0 bk ak LinearMap.id (fun y => ⟨y, rfl⟩) 0 a0 β hβ
  have h' := h.comp_equiv ((Equiv.refl (S → K)).prodCongr ((Equiv.refl (A → K)).prodCongr E))
  refine h'.congr fun x => Prod.ext rfl (Prod.ext rfl ?_)
  show E (fun i => (0 : J → K) i + x.2.2 i) = E x.2.2
  congr 1
  funext i
  exact zero_add _

end Coord

/-! ## A bijection of the entries at some places -/

section Block

variable {K J J₁ : Type}

/-- E₁ at the places e; elsewhere the entries as they are. -/
noncomputable def blockFun (e : J₁ ↪ J) (E₁ : (J₁ → K) → (J₁ → K)) (k : J → K) : J → K :=
  Function.extend e (E₁ (k ∘ e)) k

/-- At the places e it is E₁. -/
theorem blockFun_on (e : J₁ ↪ J) (E₁ : (J₁ → K) → (J₁ → K)) (k : J → K) :
    blockFun e E₁ k ∘ e = E₁ (k ∘ e) :=
  funext fun a => e.injective.extend_apply _ _ a

/-- Elsewhere it leaves the entries as they are. -/
theorem blockFun_off (e : J₁ ↪ J) (E₁ : (J₁ → K) → (J₁ → K)) (k : J → K) (i : J)
    (hi : i ∉ Set.range e) : blockFun e E₁ k i = k i :=
  Function.extend_apply' _ _ _ hi

/-- Two such maps, of which the second undoes the first at the places e, undo each other. -/
theorem blockFun_inv (e : J₁ ↪ J) (E₁ E₂ : (J₁ → K) → (J₁ → K)) (h : ∀ x, E₂ (E₁ x) = x)
    (k : J → K) : blockFun e E₂ (blockFun e E₁ k) = k := by
  funext i
  by_cases hi : i ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hi
    have h1 : blockFun e E₂ (blockFun e E₁ k) (e a) = E₂ (blockFun e E₁ k ∘ e) a :=
      congrFun (blockFun_on e E₂ (blockFun e E₁ k)) a
    rw [h1, blockFun_on e E₁ k, h]
    rfl
  · rw [blockFun_off e E₂ _ i hi, blockFun_off e E₁ k i hi]

/-- A bijection E₁ of the entries at the places e, carried to all entries. -/
noncomputable def blockEquiv (e : J₁ ↪ J) (E₁ : (J₁ → K) ≃ (J₁ → K)) : (J → K) ≃ (J → K) where
  toFun := blockFun e E₁
  invFun := blockFun e E₁.symm
  left_inv := blockFun_inv e E₁ E₁.symm E₁.symm_apply_apply
  right_inv := blockFun_inv e E₁.symm E₁ E₁.apply_symm_apply

/-- At the places e it is E₁. -/
theorem blockEquiv_on (e : J₁ ↪ J) (E₁ : (J₁ → K) ≃ (J₁ → K)) (k : J → K) :
    blockEquiv e E₁ k ∘ e = E₁ (k ∘ e) :=
  blockFun_on e E₁ k

/-- Elsewhere it leaves the entries as they are. -/
theorem blockEquiv_off (e : J₁ ↪ J) (E₁ : (J₁ → K) ≃ (J₁ → K)) (k : J → K) (i : J)
    (hi : i ∉ Set.range e) : blockEquiv e E₁ k i = k i :=
  blockFun_off e E₁ k i hi

/-- **Two such bijections at disjoint sets of places, one behind the other**: each at its own
places. -/
theorem blockEquiv_two {J₂ : Type} (e₁ : J₁ ↪ J) (e₂ : J₂ ↪ J) (hd : ∀ a b, e₁ a ≠ e₂ b)
    (E₁ : (J₁ → K) ≃ (J₁ → K)) (E₂ : (J₂ → K) ≃ (J₂ → K)) (k : J → K) :
    ((blockEquiv e₁ E₁).trans (blockEquiv e₂ E₂)) k ∘ e₁ = E₁ (k ∘ e₁) ∧
      ((blockEquiv e₁ E₁).trans (blockEquiv e₂ E₂)) k ∘ e₂ = E₂ (k ∘ e₂) := by
  constructor
  · rw [← blockEquiv_on e₁ E₁ k]
    funext a
    exact blockEquiv_off e₂ E₂ _ (e₁ a) fun ⟨b, hb⟩ => hd a b hb.symm
  · have h : blockEquiv e₁ E₁ k ∘ e₂ = k ∘ e₂ :=
      funext fun b => blockEquiv_off e₁ E₁ k (e₂ b) fun ⟨a, ha⟩ => hd a b ha
    rw [← h]
    exact blockEquiv_on e₂ E₂ (blockEquiv e₁ E₁ k)

end Block

end Code

#print axioms Code.wideLaw_iff
#print axioms Code.WideLaw.congr
#print axioms Code.WideLaw.comp_law
#print axioms Code.wideLaw_equiv
#print axioms Code.WideLaw.comp_equiv
#print axioms Code.WideLaw.of_coins
#print axioms Code.triHom_onto
#print axioms Code.tri_law
#print axioms Code.wideLaw_of_onto
#print axioms Code.prodMap_onto
#print axioms Code.padHom_onto
#print axioms Code.fresh_wide
#print axioms Code.fresh_wide_map
#print axioms Code.fresh_wide_one
#print axioms Code.fresh_wide_core
#print axioms Code.fresh_wide_one_equiv
#print axioms Code.fresh_wide_table
#print axioms Code.fresh_wide_equiv
#print axioms Code.blockFun_on
#print axioms Code.blockFun_off
#print axioms Code.blockFun_inv
#print axioms Code.blockEquiv_on
#print axioms Code.blockEquiv_off
#print axioms Code.blockEquiv_two
