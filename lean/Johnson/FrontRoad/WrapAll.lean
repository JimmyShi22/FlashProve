-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/WrapAll.lean: if a scheme has index privacy on a range of indices, then a scheme
on another type of indices that is a re-packing of it has index privacy at all of its indices, at
one query more, if the map of indices has its image in the range and public parameters and relations
fit. For any two schemes over one hash function, one request a call (ZKCP.Arg, ZKCP/Defs.lean).
Terms and the limits that go with any quote: Spec.lean.

What this file proves.
strongPrivacy_of_wrap. Let A have ZKCP.StrongPrivacyOn with S and ζ on the range ok. Required: under
every hash function the outer committer at j outputs what the inner committer at idx j outputs, with
the key replaced by the re-packing's key and the prover's key by any function σ of the two inner
keys; the outer prover at σ of any keys is the inner prover at the inner instance and witness, with
the re-packing's map on proofs; the public parameters fit; whatever the outer relation holds of is
mapped to something of which the inner relation holds, and the outer instance can be read back from
the inner one; the image of idx is in ok. Then B has ZKCP.HasStrongIndexPrivacyWith with w.sim S hp
and ζ at one query more.
valid_env_wrap. If the relations fit, the reduction's environment names true inner instances where
the outer one names true outer ones.

How it fits. The library's theorem on re-packings (ZKCP.PrivacyFor.wrap, ZKCP/PrivacyWrap.lean) is
about one inner index, one outer index and one environment. It covers at once the committer's
further query, the maps on keys and on proofs (which read the inner key), instances, witnesses and
public parameters. Here it is applied once for each outer index j, at the inner index idx j.
FrontProof.lean applies this step.

Limits. One added error for all: the inner bound at one query more, also where the re-packing
queries nothing. One request a call. Nothing on completeness or binding.
-/
import ZKCP.OnRange
import ZKCP.PrivacyWrap

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open ZKCP

variable {lam : ℕ} {I X W PP IVK ISK Pf J X' W' PP' IVK' ISK' Pf' : Type}

/-- If whatever the outer relation holds of at j is mapped by w to something of which the inner
relation holds at i, and the outer environment Z names only true outer instances (IsValid), then the
reduction's environment w.env Z names only true inner instances. -/
theorem valid_env_wrap (w : Wrap lam IVK X W Pf IVK' X' W' Pf') (R : IndexedRelation I X W PP)
    (R' : IndexedRelation J X' W' PP') (i : I) (j : J)
    (hrel : ∀ x' w', R'.rel j x' w' → R.rel i (w.inst x') (w.wit w'))
    (Z : ViewEnv lam IVK' X' W' Pf') (hZ : Z.IsValid R' j) : (w.env Z).IsValid R i := by
  intro v x wt hv
  unfold Wrap.env at hv
  obtain ⟨xw, hxw, e⟩ := Option.map_eq_some_iff.1 hv
  cases e
  exact hrel _ _ (hZ _ xw.1 xw.2 hxw)

/-- If A has index privacy on the range ok (ZKCP.StrongPrivacyOn), B's committer and prover are A's
with the re-packing w applied (hC, hP), the public parameters fit (hpp), the relations fit (hrel)
and the image of idx is in ok (hok), then B has ZKCP.HasStrongIndexPrivacyWith at all its indices,
with the simulator w.sim S hp and the bound ζ at one query more. -/
theorem strongPrivacy_of_wrap (w : Wrap lam IVK X W Pf IVK' X' W' Pf')
    (R : IndexedRelation I X W PP) (R' : IndexedRelation J X' W' PP')
    (A : Arg lam I X W IVK ISK Pf) (B : Arg lam J X' W' IVK' ISK' Pf')
    (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) (idx : J → I)
    (hp : PP' → PP) (σ : IVK × ISK → ISK')
    (hC : ∀ j f, (B.C j).run f = ((A.C (idx j)).run f).map fun keys =>
      (w.key keys.1 ((w.ask keys.1).map f), σ keys))
    (hP : ∀ f keys x' w', (B.P (σ keys) x' w').run f =
      ((A.P keys.2 (w.inst x') (w.wit w')).run f).map (w.proof keys.1))
    (hpp : ∀ j, R.pp (idx j) = hp (R'.pp j))
    (hrel : ∀ j x' w', R'.rel j x' w' →
      R.rel (idx j) (w.inst x') (w.wit w') ∧ w.back (w.inst x') = x')
    (hok : ∀ j, ok (idx j)) (h : StrongPrivacyOn R A S ζ ok) :
    HasStrongIndexPrivacyWith R' B (w.sim S hp) fun t N => ζ (t + 1) N :=
  fun j Z hZ =>
    PrivacyFor.wrap w (R := R) (R' := R') (A := A) (B := B) hp (hpp j)
      (fun f => (A.C (idx j)).run f) (fun _ s => s) (fun _ s => σ s)
      (fun _ => (PMF.map_id _).symm) (hC j) (fun f s _ x' w' _ => hP f s x' w')
      (fun v x' w' hz => (hrel j x' w' (hZ v x' w' hz)).2)
      (h (idx j) (hok j) _
        (valid_env_wrap w R R' (idx j) j (fun x' w' hr => (hrel j x' w' hr).1) Z hZ))

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.strongPrivacy_of_wrap
