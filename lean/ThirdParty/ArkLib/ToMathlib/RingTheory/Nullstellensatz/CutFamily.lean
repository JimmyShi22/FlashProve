/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/RingTheory/Nullstellensatz/CutFamily.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* The one declaration of the file is kept. ArkLib's comment at the top of the file is unchanged.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.ToMathlib.RingTheory.Ideal.CutFamily
import ThirdParty.ArkLib.ToMathlib.RingTheory.Nullstellensatz

/-!
# Zero loci covered by iterated retained cut families

Let `k` be a field, `σ` a finite type, `Ps` a finite family of ideals of `MvPolynomial σ k`, `s` a
polynomial and `cuts` a list of polynomials. Over any field extension `K` of `k`, a zero of a
member `P` of `Ps` at which `s` does not vanish and at which every element of `cuts` vanishes is a
zero of some member `Q ⊇ P` of `Ideal.iteratedRetainedCutFamily Ps s cuts`.

The proof applies the ideal-theoretic covering property
`Ideal.exists_mem_iteratedRetainedCutFamily_le` to the kernel of evaluation at the point, which is
prime because `K` is a field. No algebraic closedness is used. For a single cut `f`, take
`cuts = [f]`: `Ideal.iteratedRetainedCutFamily Ps s [f]` is `Ideal.retainedCutFamily Ps s f` by
definition.

## Main statements

* `MvPolynomial.exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus`: the point cover.
-/

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Finite σ]

/-- Let `x` be a zero, over a field extension `K`, of a member `P` of `Ps`, at which `s` does not
vanish and every element of `cuts` vanishes. Then `x` is a zero of some member `Q` of the iterated
retained cut family with `P ≤ Q`.

The hypothesis `aeval x s ≠ 0` is needed: every member avoids `s` after one cut, so a point with
`s = 0` can be covered only for `cuts = []`. The vanishing of the cuts at `x` is needed because
every member contains every cut. -/
theorem exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus
    {Ps : Finset (Ideal (MvPolynomial σ k))} {P : Ideal (MvPolynomial σ k)} (hP : P ∈ Ps)
    {s : MvPolynomial σ k} {cuts : List (MvPolynomial σ k)} {x : σ → K}
    (hxP : x ∈ zeroLocus K P) (hxs : aeval x s ≠ 0) (hcuts : ∀ f ∈ cuts, aeval x f = 0) :
    ∃ Q ∈ Ideal.iteratedRetainedCutFamily Ps s cuts, P ≤ Q ∧ x ∈ zeroLocus K Q := by
  have : (RingHom.ker (aeval (R := k) x)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q, hQ, hPQ, hQx⟩ := Ideal.exists_mem_iteratedRetainedCutFamily_le hP
    (mem_zeroLocus_iff_le_ker_aeval.mp hxP) (mt RingHom.mem_ker.mp hxs)
    (fun f hf ↦ RingHom.mem_ker.mpr (hcuts f hf))
  exact ⟨Q, hQ, hPQ, mem_zeroLocus_iff_le_ker_aeval.mpr hQx⟩

end MvPolynomial
