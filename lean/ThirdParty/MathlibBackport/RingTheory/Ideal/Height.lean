/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Jingting Wang, Andrew Yang, Shouxin Zhang
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/RingTheory/Ideal/Height.lean, commit 5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0),
lines 44-46, 274-280, 282-283, 579-587. Licence: Apache-2.0, see ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
* Proof changed, Ideal.eq_span_singleton_of_height_eq_one: lemmas are called by their names in this
  Mathlib; the finite height of the smaller ideal is supplied, as this Mathlib's monotonicity lemma
  asks.
* Proof changed, Ideal.height_eq_zero_iff_eq_bot: proved directly from the definition of height,
  because the lemma exists_isPrime_height_eq is not taken over.
-/

import Mathlib.RingTheory.Ideal.Height

variable {R : Type*} [CommRing R] (I : Ideal R)
open Ideal

lemma PrimeSpectrum.height_eq_orderHeight (p : PrimeSpectrum R) :
    p.asIdeal.height = Order.height p :=
  p.asIdeal.height_eq_primeHeight

@[simp]
lemma Ideal.height_eq_zero_iff_eq_bot [IsDomain R] {I : Ideal R} : I.height = 0 ↔ I = ⊥ := by
  refine ⟨fun hI ↦ ?_, fun hI0 ↦ by simp [hI0]⟩
  simp only [Ideal.height, ENat.iInf_eq_zero] at hI
  obtain ⟨p, hp, hp0⟩ := hI
  haveI := hp.1.1
  rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
    Set.mem_singleton_iff] at hp0
  exact bot_unique (hp.1.2.trans_eq hp0)

theorem Ideal.ne_bot_of_height_eq_one [IsDomain R] {I : Ideal R} (h : I.height = 1) : I ≠ ⊥ :=
  I.height_eq_zero_iff_eq_bot.not.mp (ne_zero_of_eq_one h)

lemma Ideal.eq_span_singleton_of_height_eq_one [IsDomain R] {p : Ideal R} [p.IsPrime]
    (h1 : p.height = 1) {x : R} (hx : x ∈ p) (hxp : Prime x) : p = span {x} := by
  have : (span {x}).IsPrime := by simp [span_singleton_prime hxp.ne_zero, hxp]
  have : p.FiniteHeight := by simp [p.finiteHeight_iff, h1]
  have hle : span {x} ≤ p := by simp only [p.span_singleton_le_iff_mem, hx]
  have : (span {x}).FiniteHeight := finiteHeight_of_le hle (IsPrime.ne_top ‹_›)
  by_contra! hne
  apply hxp.ne_zero
  rw [← span_singleton_eq_bot, ← height_eq_zero_iff_eq_bot, ← ENat.lt_one_iff_eq_zero, ← h1]
  refine height_strict_mono_of_is_prime (lt_of_le_of_ne hle hne.symm)

