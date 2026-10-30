/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/RingTheory/Ideal/CutFamily.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13.
Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 11 of the 15 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Proof changed, of_mem_retainedCutFamily: `.isPrime` and `.le` on a member of minimalPrimes became
  `.1.1` and `.1.2`: this Mathlib has no Ideal.IsMinimalPrime.
* Proof changed, exists_mem_iteratedRetainedCutFamily_le: `.le` on a member of minimalPrimes became
  `.1.2`: this Mathlib has no Ideal.IsMinimalPrime.
* Proof changed, sum_retainedCutFamily_le: `convert` closes the goal in Lean 4.29.1, so the two
  lines after it are removed.
-/

import ThirdParty.ArkLib.ToMathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Iterated retained principal cuts of finite ideal families

Let `R` be a Noetherian commutative semiring, `Ps` a finite family of ideals of `R`, and `s ∈ R`.
Cutting every member `P` of `Ps` by an element `f` and keeping the minimal primes of
`P ⊔ span {f}` that do not contain `s` gives a new finite family
`Ideal.retainedCutFamily Ps s f`. Repeating this for a list of elements `cuts` gives
`Ideal.iteratedRetainedCutFamily Ps s cuts`.

The iterated family has three properties.

* Every member contains a member of `Ps` and every element of `cuts`. After at least one cut
  every member is a prime not containing `s`; for the empty list this needs the same property
  of `Ps`.
* It covers every prime `Q` with `s ∉ Q` that contains a member `P` of `Ps` and every cut: some
  member lies between `P` and `Q`. Consequently every minimal prime of `P ⊔ span cuts` that does
  not contain `s` is itself a member.
* A nonnegative weight on ideals that does not increase under one retained cut of a prime does
  not increase along the whole iteration.

The covering property is the algebraic form of the statement that the zero loci of the members,
away from `s = 0`, cover the common zero locus of `P` and the cuts. The iterated family can be
strictly larger than the retained minimal primes of `P ⊔ span cuts`: in `k[x, y]`, cutting `⊥` by
`xy` and then by `x` gives `{(x), (x, y)}`, while `(xy, x) = (x)` has only the minimal prime
`(x)`. The prime `(x, y)` comes from the component `(y)` of the first cut.

## Main statements

* `Ideal.retainedCutFamily`, `Ideal.mem_retainedCutFamily`: one simultaneous retained cut.
* `Ideal.retainedCutFamily_of_forall_mem`: cutting a family of primes avoiding `s` by an element
  they all contain changes nothing.
* `Ideal.iteratedRetainedCutFamily`, with `_nil`, `_cons` and `_append`: the iteration.
* `Ideal.isPrime_of_mem_iteratedRetainedCutFamily`,
  `Ideal.notMem_of_mem_iteratedRetainedCutFamily`,
  `Ideal.exists_le_of_mem_iteratedRetainedCutFamily`: what every member contains.
* `Ideal.exists_mem_iteratedRetainedCutFamily_le`: the covering property.
* `Ideal.retainedMinimalPrimes_subset_iteratedRetainedCutFamily`: retained minimal primes of the
  total cut are members.
* `Ideal.sum_retainedCutFamily_le`, `Ideal.sum_iteratedRetainedCutFamily_le`: monotonicity of
  nonnegative weights.
-/

noncomputable section

namespace Ideal

variable {R : Type*} [CommSemiring R] [IsNoetherianRing R]

/-- One simultaneous retained cut of a finite family of ideals: the union over `P ∈ Ps` of the
minimal primes of `P ⊔ span {f}` that do not contain `s`.

Members of `Ps` containing `s` contribute nothing, and neither does a member for which
`P ⊔ span {f} = ⊤`. Children of different parents may coincide; the union counts them once. -/
def retainedCutFamily (Ps : Finset (Ideal R)) (s f : R) : Finset (Ideal R) := by
  classical
  exact Ps.biUnion fun P ↦ (P ⊔ span {f}).retainedMinimalPrimes s

/-- An ideal belongs to the retained cut family exactly when it is a retained minimal prime of the
cut of some member of `Ps`. -/
@[simp]
theorem mem_retainedCutFamily {Ps : Finset (Ideal R)} {s f : R} {Q : Ideal R} :
    Q ∈ retainedCutFamily Ps s f ↔ ∃ P ∈ Ps, Q ∈ (P ⊔ span {f}).retainedMinimalPrimes s := by
  classical
  simp [retainedCutFamily]

/-- Every member `Q` of a retained cut family is a prime containing a member of `Ps` and `f`, and
not containing `s`. No hypothesis on `Ps` is needed, because minimal primes are prime. -/
theorem of_mem_retainedCutFamily {Ps : Finset (Ideal R)} {s f : R} {Q : Ideal R}
    (hQ : Q ∈ retainedCutFamily Ps s f) :
    Q.IsPrime ∧ (∃ P ∈ Ps, P ≤ Q) ∧ f ∈ Q ∧ s ∉ Q := by
  obtain ⟨P, hP, hQ⟩ := mem_retainedCutFamily.mp hQ
  obtain ⟨hmin, hs⟩ := mem_retainedMinimalPrimes.mp hQ
  exact ⟨hmin.1.1, ⟨P, hP, le_sup_left.trans hmin.1.2⟩,
    hmin.1.2 (mem_sup_right (mem_span_singleton_self f)), hs⟩

/-- Successive retained cuts of a finite family of ideals by the elements of `cuts`, in order,
always keeping only minimal primes that do not contain the fixed element `s`. -/
def iteratedRetainedCutFamily (Ps : Finset (Ideal R)) (s : R) : List R → Finset (Ideal R)
  | [] => Ps
  | f :: cuts => iteratedRetainedCutFamily (retainedCutFamily Ps s f) s cuts

/-- With no cuts the iterated family is the starting family. -/
@[simp]
theorem iteratedRetainedCutFamily_nil (Ps : Finset (Ideal R)) (s : R) :
    iteratedRetainedCutFamily Ps s [] = Ps := rfl

/-- Cutting by `f :: cuts` is one retained cut by `f` followed by the cuts in `cuts`. -/
@[simp]
theorem iteratedRetainedCutFamily_cons (Ps : Finset (Ideal R)) (s f : R) (cuts : List R) :
    iteratedRetainedCutFamily Ps s (f :: cuts) =
      iteratedRetainedCutFamily (retainedCutFamily Ps s f) s cuts := rfl

/-- If every member of `Ps` is prime, so is every member of the iterated family.

After at least one cut the members are minimal primes and the hypothesis is not used; for
`cuts = []` the family is `Ps` itself, so the hypothesis cannot be dropped. -/
theorem isPrime_of_mem_iteratedRetainedCutFamily {Ps : Finset (Ideal R)}
    (hprime : ∀ P ∈ Ps, P.IsPrime) (s : R) (cuts : List R) {Q : Ideal R}
    (hQ : Q ∈ iteratedRetainedCutFamily Ps s cuts) : Q.IsPrime := by
  induction cuts generalizing Ps with
  | nil => exact hprime Q hQ
  | cons f cuts ih => exact ih (fun P hP ↦ (of_mem_retainedCutFamily hP).1) hQ

/-- Every member of the iterated family contains a member of `Ps` and every element of `cuts`.
No hypothesis is needed. -/
theorem exists_le_of_mem_iteratedRetainedCutFamily {Ps : Finset (Ideal R)} {s : R}
    {cuts : List R} {Q : Ideal R} (hQ : Q ∈ iteratedRetainedCutFamily Ps s cuts) :
    ∃ P ∈ Ps, P ≤ Q ∧ ∀ f ∈ cuts, f ∈ Q := by
  induction cuts generalizing Ps with
  | nil => exact ⟨Q, hQ, le_rfl, by simp⟩
  | cons f cuts ih =>
      obtain ⟨J, hJ, hJQ, hcuts⟩ := ih hQ
      obtain ⟨-, ⟨P, hP, hPJ⟩, hfJ, -⟩ := of_mem_retainedCutFamily hJ
      refine ⟨P, hP, hPJ.trans hJQ, ?_⟩
      rintro g (_ | ⟨_, hg⟩)
      exacts [hJQ hfJ, hcuts g hg]

/-- The covering property. Let `Q` be a prime not containing `s` that contains a member `P` of
`Ps` and every element of `cuts`. Then some member `J` of the iterated family satisfies
`P ≤ J ≤ Q`.

At each step `Q` contains the cut of the current member, so it contains a retained minimal prime
of that cut (`Ideal.exists_mem_retainedMinimalPrimes_le`). The hypotheses on `Q` are needed:
`s ∈ Q` would make every retained prime avoid `Q`, and a cut not in `Q` gives children not
below `Q`. No hypothesis on `Ps` is needed. -/
theorem exists_mem_iteratedRetainedCutFamily_le {Ps : Finset (Ideal R)} {s : R} {cuts : List R}
    {P Q : Ideal R} [Q.IsPrime] (hP : P ∈ Ps) (hPQ : P ≤ Q) (hsQ : s ∉ Q)
    (hcuts : ∀ f ∈ cuts, f ∈ Q) :
    ∃ J ∈ iteratedRetainedCutFamily Ps s cuts, P ≤ J ∧ J ≤ Q := by
  induction cuts generalizing Ps P with
  | nil => exact ⟨P, hP, le_rfl, hPQ⟩
  | cons f cuts ih =>
      have hcut : P ⊔ span {f} ≤ Q :=
        sup_le hPQ ((span_singleton_le_iff_mem Q).mpr (hcuts f List.mem_cons_self))
      obtain ⟨P₁, hP₁, hP₁Q⟩ := exists_mem_retainedMinimalPrimes_le hcut hsQ
      obtain ⟨J, hJ, hP₁J, hJQ⟩ := ih (mem_retainedCutFamily.mpr ⟨P, hP, hP₁⟩) hP₁Q
        (fun g hg ↦ hcuts g (List.mem_cons_of_mem f hg))
      exact ⟨J, hJ, le_sup_left.trans ((mem_retainedMinimalPrimes.mp hP₁).1.1.2.trans hP₁J), hJQ⟩

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]

/-- A nonnegative weight `w` on ideals whose total over the retained children of each member of
`Ps` is at most its value on that member does not increase under the simultaneous cut.

Nonnegativity is needed because children of different parents may coincide, and the union then
counts them once; the proof bounds the sum over the union by the sum of the sums. -/
theorem sum_retainedCutFamily_le (w : Ideal R → M) (hw : ∀ Q, 0 ≤ w Q) (Ps : Finset (Ideal R))
    (s f : R) (hchild : ∀ P ∈ Ps, ∑ Q ∈ (P ⊔ span {f}).retainedMinimalPrimes s, w Q ≤ w P) :
    ∑ Q ∈ retainedCutFamily Ps s f, w Q ≤ ∑ P ∈ Ps, w P := by
  classical
  have hunion : ∀ {S T : Finset (Ideal R)}, ∑ Q ∈ S ⊔ T, w Q ≤ ∑ Q ∈ S, w Q + ∑ Q ∈ T, w Q :=
    fun {S T} ↦ by
      rw [Finset.sup_eq_union, ← Finset.sum_union_inter]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun Q _ ↦ hw Q)
  have hbiUnion := Finset.apply_sup_le_sum (f := fun T : Finset (Ideal R) ↦ ∑ Q ∈ T, w Q)
    Finset.sum_empty hunion (s := fun P ↦ (P ⊔ span {f}).retainedMinimalPrimes s) Ps
  rw [Finset.sup_eq_biUnion] at hbiUnion
  have hfam : ∑ Q ∈ retainedCutFamily Ps s f, w Q ≤
      ∑ P ∈ Ps, ∑ Q ∈ (P ⊔ span {f}).retainedMinimalPrimes s, w Q := by
    convert hbiUnion using 2
  exact hfam.trans (Finset.sum_le_sum hchild)

/-- A nonnegative weight `w` on ideals that does not increase under one retained cut of a prime by
any element of `cuts` does not increase along the iterated family, starting from a family of
primes.

The step hypothesis is only required at primes, because every member after the first cut is
prime; primality of `Ps` makes it apply to the first cut as well. -/
theorem sum_iteratedRetainedCutFamily_le (w : Ideal R → M) (hw : ∀ Q, 0 ≤ w Q)
    {Ps : Finset (Ideal R)} (hprime : ∀ P ∈ Ps, P.IsPrime) (s : R) (cuts : List R)
    (hstep : ∀ P : Ideal R, P.IsPrime → ∀ f ∈ cuts,
      ∑ Q ∈ (P ⊔ span {f}).retainedMinimalPrimes s, w Q ≤ w P) :
    ∑ Q ∈ iteratedRetainedCutFamily Ps s cuts, w Q ≤ ∑ P ∈ Ps, w P := by
  induction cuts generalizing Ps with
  | nil => exact le_rfl
  | cons f cuts ih =>
      exact (ih (fun P hP ↦ (of_mem_retainedCutFamily hP).1)
        (fun P hP g hg ↦ hstep P hP g (List.mem_cons_of_mem f hg))).trans
        (sum_retainedCutFamily_le w hw Ps s f fun P hP ↦
          hstep P (hprime P hP) f List.mem_cons_self)

end Ideal
