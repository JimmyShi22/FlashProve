-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/AtInputProof.lean: INDEX PRIVACY PASSES TO THE SCHEME WHOSE PUBLISHED KEY BEGINS
WITH THE DIGEST OF THE KEY's CODE (withId, Johnson/WholeKey/AtInput.lean), for every scheme over one
hash function and every code: AT ONE INDEX AND ONE ENVIRONMENT, on a range of indices, and at all
indices.

General theorems with their proofs. This file states no goal of the release.

The step is the library's theorem on re-packings (ZKCP.PrivacyFor.wrap, ZKCP/PrivacyWrap.lean),
which speaks of one index and one environment, at the re-packing wrapId: the committer asks one
query more, at the code of the key that it has made; proofs, instances and witnesses stay. The
price: the inner bound at one query more.

  run_C_withId        the committer's output under a fixed hash function.
  privacyFor_withId   at one index and one environment.
  valid_env_wrapId    the reduction's environment is valid where the outer one is.
  privacyOn_withId    on a range ok of indices.
  privacy_withId      at all indices: Spec.privacy_withId (Johnson/WholeKey/AtInput.lean).

Limits. One hash function, one request a call, in the form of ZKCP/Defs.lean. Nothing on how a
scheme over typed oracles comes there.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.AtInput

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-- The committer's output under a fixed hash function: A's two keys, the digest of the verifier's
key laid in front of it. -/
theorem run_C_withId (A : ZKCP.Arg lam I X W IVK ISK Pf) (code : IVK → Option ZKCP.Str)
    (f : ZKCP.Oracle lam) (i : I) :
    ((withId A code).C i).run f =
      ((A.C i).run f).map fun keys => ((ZKCP.digestUnder f code keys.1, keys.1), keys.2) := by
  show ((A.C i).bind fun keys =>
      (ZKCP.keyDigest code keys.1).mapO fun d => ((d, keys.1), keys.2)).run f = _
  rw [ZKCP.run_bind]
  show _ = ((A.C i).run f).bind fun keys =>
    PMF.pure ((ZKCP.digestUnder f code keys.1, keys.1), keys.2)
  refine congrArg _ (funext fun keys => ?_)
  rw [ZKCP.OComp.run_mapO, ZKCP.run_keyDigest, PMF.pure_map]

/-- **At one index and one environment.** -/
theorem privacyFor_withId (R : ZKCP.IndexedRelation I X W PP) (A : ZKCP.Arg lam I X W IVK ISK Pf)
    (Sm : ZKCP.Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (code : IVK → Option ZKCP.Str) (i : I)
    (Z : ZKCP.ViewEnv lam (ZKCP.Digest lam × IVK) X W Pf)
    (hp : ZKCP.PrivacyFor R A Sm ζ i ((wrapId (W := W) code).env Z)) :
    ZKCP.PrivacyFor R (withId A code) ((wrapId (W := W) code).sim Sm id)
      (fun t N => ζ (t + 1) N) i Z :=
  ZKCP.PrivacyFor.wrap (wrapId (W := W) code) (R := R) (R' := R) (A := A) (B := withId A code) id
    rfl (fun f => (A.C i).run f) (fun _ s => s) (fun _ s => s.2)
    (fun _ => (PMF.map_id _).symm) (fun f => run_C_withId A code f i)
    (fun _ _ _ _ _ _ => (PMF.map_id _).symm) (fun _ _ _ _ => rfl) hp

/-- The reduction's environment names only true instances where the outer one does. -/
theorem valid_env_wrapId (R : ZKCP.IndexedRelation I X W PP) (code : IVK → Option ZKCP.Str) (i : I)
    (Z : ZKCP.ViewEnv lam (ZKCP.Digest lam × IVK) X W Pf) (hZ : Z.IsValid R i) :
    ((wrapId (W := W) (Pf := Pf) code).env Z).IsValid R i := by
  intro v x w hv
  unfold ZKCP.Wrap.env at hv
  obtain ⟨xw, hxw, e⟩ := Option.map_eq_some_iff.1 hv
  cases e
  exact hZ _ xw.1 xw.2 hxw

/-- **On a range of indices.** -/
theorem privacyOn_withId (R : ZKCP.IndexedRelation I X W PP) (A : ZKCP.Arg lam I X W IVK ISK Pf)
    (Sm : ZKCP.Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (code : IVK → Option ZKCP.Str)
    (ok : I → Prop)
    (h : ∀ i, ok i → ∀ Z : ZKCP.ViewEnv lam IVK X W Pf, Z.IsValid R i →
      ZKCP.PrivacyFor R A Sm ζ i Z) :
    ∀ i, ok i → ∀ Z : ZKCP.ViewEnv lam (ZKCP.Digest lam × IVK) X W Pf, Z.IsValid R i →
      ZKCP.PrivacyFor R (withId A code) ((wrapId (W := W) code).sim Sm id)
        (fun t N => ζ (t + 1) N) i Z :=
  fun i hi Z hZ =>
    privacyFor_withId R A Sm ζ code i Z (h i hi _ (valid_env_wrapId R code i Z hZ))

/-- **At all indices.** -/
theorem privacy_withId : Spec.privacy_withId :=
  fun _ _ _ _ _ _ _ _ R A Sm ζ code h i =>
    privacyOn_withId R A Sm ζ code (fun _ => True) (fun i _ Z hZ => h i Z hZ) i trivial

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.privacyFor_withId
#print axioms OnBytes.WholeKey.privacyOn_withId
#print axioms OnBytes.WholeKey.privacy_withId
