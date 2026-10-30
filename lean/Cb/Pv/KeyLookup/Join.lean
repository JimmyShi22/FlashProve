-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Join.lean: the join point: the claims on the live planes' roots become one claim on
level 0 of the table's tree, at a point of mu elements that the verifier draws.

It imports the library, Letters.lean, Idle.lean and the rules for blocks without an honest side
(Cb/Pv/Lookup/Know/KnowAt.lean: `KnowAt`, `BkK`, `drawK`, `knowAt_draw`); no file of the port.

The step. The prover sends nothing. The verifier draws ϱ, mu elements of E, in one round. The new
claim is: (extension of level 0 at ϱ) + ⟨Σ_θ eq(ϱ, θ) form_θ, entries⟩ = Σ_θ eq(ϱ, θ) target_θ,
with both sums over all 2^mu places θ. At a live place, form and target are those of the claim on
that plane's root. At a dead place there is no form and the target is the public 1 (`formAt`,
`tgtAt`); that the root there is 1 is `Dat.plane_dead` (Idle.lean). Below, q := the number of
elements of E.

  `A.joinK Ex`    the block: one draw of `Fin mu → E`. Its error, as a count of bad values:
                  mu · q^(mu − 1) of q^mu.
  `join_top_iff`  the new claim says Σ_θ eq(ϱ, θ) · gap_θ = 0, where
                  gap_θ := root_θ + ⟨form_θ, μ⟩ − target_θ.
  `gap_dead`      the gap at a dead place is 0, for all entries.
  `gap_zero_iff`  if pl ≤ 2^mu: all gaps are 0 exactly if all claims on the live planes hold.
  `join_know`     if pl ≤ 2^mu (`Pub.Adm.room`): the block is `Know` from the joint `Roots` to the
                  joint `Joined` (Letters.lean), beside every riding joint R0 and for every Mu
                  (binders of `Dat.jt`, Letters.lean). The count is the library's `ok_eqPt`.
  `join_errs`     its error and its number of values as lists, by the library's readers.
  `join_pt`       coordinate t < mu of the point handed on is the t-th element drawn.
Not shown: an honest side; anything on how the planes' claims are made.

-/
import Cb.Pv.KeyLookup.Idle
import Cb.Pv.Lookup.Know.KnowAt
import Cb.Gen.BatEvaderProofs
import Cb.Ld.LdLkpAsm2ErrProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Finset

noncomputable section
namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E)

/-- Form and target at each of the 2^mu places: at a dead one no form, the public target 1. -/
def formAt (x : A.XS) (θ : Fin A.mu → Bool) : A.J → E :=
  if numLE θ < A.pl then (x.planes (numLE θ)).mf else 0
def tgtAt (x : A.XS) (θ : Fin A.mu → Bool) : E :=
  if numLE θ < A.pl then (x.planes (numLE θ)).tg else 1

/-- The state after the draw. -/
def joinNx (x : A.XS) (ϱ : Fin A.mu → E) : A.XS :=
  { x with
    pt := fun t => if h : t < A.mu then ϱ ⟨t, h⟩ else 0
    top := ⟨fun j => ∑ θ, Alg.eqk ϱ θ * A.formAt x θ j, ∑ θ, Alg.eqk ϱ θ * A.tgtAt x θ⟩ }

/-- The block. -/
def joinK (Ex : ExtSpec) : BkK A.XS A.XS Ex :=
  drawK (Fin A.mu → E) A.joinNx Ex (A.mu * Fintype.card E ^ (A.mu - 1))

/-- By how much the claim at the place θ fails. -/
def gap (x : A.XS) (μ : A.J → E) (θ : Fin A.mu → Bool) : E :=
  A.plane x.st μ x.al (numLE θ) + ∑ j, A.formAt x θ j * μ j - A.tgtAt x θ

theorem join_pt (x : A.XS) (ϱ : Fin A.mu → E) (t : Fin A.mu) : (A.joinNx x ϱ).pt t = ϱ t :=
  dif_pos t.2

theorem gap_dead (x : A.XS) (μ : A.J → E) (θ : Fin A.mu → Bool) (h : A.pl ≤ numLE θ) :
    A.gap x μ θ = 0 := by
  unfold gap formAt tgtAt
  rw [A.plane_dead x.st μ x.al h, if_neg (Nat.not_lt.mpr h), if_neg (Nat.not_lt.mpr h)]
  simp

theorem gap_live (x : A.XS) (μ : A.J → E) (θ : Fin A.mu → Bool) (h : numLE θ < A.pl) :
    A.gap x μ θ = 0 ↔ (x.planes (numLE θ)).Holds (A.plane x.st μ x.al (numLE θ)) μ := by
  unfold gap formAt tgtAt SCl.Holds
  rw [if_pos h, if_pos h]
  exact sub_eq_zero

theorem gap_zero_iff (hr : A.pl ≤ 2 ^ A.mu) (x : A.XS) (μ : A.J → E) :
    A.gap x μ = 0 ↔ A.AllPlanes x μ := by
  constructor
  · intro h j hj
    obtain ⟨θ, rfl⟩ := numLE_surj (Nat.lt_of_lt_of_le hj hr)
    exact (A.gap_live x μ θ hj).1 (congrFun h θ)
  · intro h
    funext θ
    by_cases hθ : numLE θ < A.pl
    · exact (A.gap_live x μ θ hθ).2 (h _ hθ)
    · exact A.gap_dead x μ θ (Nat.le_of_not_lt hθ)

theorem join_top_iff (x : A.XS) (μ : A.J → E) (ϱ : Fin A.mu → E) :
    A.TopAt (A.joinNx x ϱ) μ 0 ↔ ∑ θ, Alg.eqk ϱ θ * A.gap x μ θ = 0 := by
  have hp : (fun i : Fin (A.mu + 0) => (A.joinNx x ϱ).pt i) = ϱ := funext fun i => A.join_pt x ϱ i
  have hu : (fun θ : Fin (A.mu + 0) → Bool => A.tabU x.st μ x.al 0 (numLE θ)) =
      fun θ => A.plane x.st μ x.al (numLE θ) :=
    funext fun θ => A.tabU_zero x.st μ x.al (ldLkpNum_lt _ θ)
  show Alg.mle (fun θ : Fin (A.mu + 0) → Bool => A.tabU x.st μ x.al 0 (numLE θ))
        (fun i : Fin (A.mu + 0) => (A.joinNx x ϱ).pt i) +
      ∑ j, (∑ θ, Alg.eqk ϱ θ * A.formAt x θ j) * μ j = ∑ θ, Alg.eqk ϱ θ * A.tgtAt x θ ↔ _
  rw [hp, hu]
  have e : ∑ θ, Alg.eqk ϱ θ * A.gap x μ θ =
      Alg.mle (fun θ : Fin A.mu → Bool => A.plane x.st μ x.al (numLE θ)) ϱ +
        ∑ j, (∑ θ, Alg.eqk ϱ θ * A.formAt x θ j) * μ j - ∑ θ, Alg.eqk ϱ θ * A.tgtAt x θ := by
    unfold gap Alg.mle
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
      Finset.mul_sum]
    congr 2
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  exact sub_eq_zero.symm

/-- Knowledge soundness (`BkK.Know`): from `Roots` to `Joined`. -/
theorem join_know (hr : A.pl ≤ 2 ^ A.mu) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop) :
    (A.joinK Ex).Know (A.jt R0 msg Mu A.Roots) (A.jt R0 msg Mu A.Joined) := by
  refine knowAt_draw Kc M A.XS A.XS Ex Wp (Fin A.mu → E) A.joinNx _ _ _ (fun _ _ _ h => h) ?_
  intro x y m _
  by_cases hP : A.AllPlanes x (msg m)
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro β ⟨wp, h1, h2⟩
      exact h2 ⟨h1.1, h1.2.1, hP, h1.2.2.1⟩
  · have hv : A.gap x (msg m) ≠ 0 := fun h => hP ((A.gap_zero_iff hr x (msg m)).1 h)
    refine (cnt_mono fun β hβ => ?_).trans
      ((ok_eqPt E (Fin A.mu) (A.gap x (msg m)) hv).trans (le_of_eq ?_))
    · obtain ⟨wp, h1, _⟩ := hβ
      exact (A.join_top_iff x (msg m) β).1 h1.2.2.2
    · show Fintype.card (Fin A.mu) * Fintype.card E ^ (Fintype.card (Fin A.mu) - 1) = _
      rw [Fintype.card_fin]

/-- Errors and numbers of values, by the library's own readers. -/
theorem join_errs (Ex : ExtSpec) :
    (A.joinK Ex).e.toList = [A.mu * Fintype.card E ^ (A.mu - 1)] ∧
    (A.joinK Ex).R.shape.chalList = [Fintype.card E ^ A.mu] := by
  refine ⟨rfl, ?_⟩
  show [Fintype.card (Fin A.mu → E)] = _
  rw [Fintype.card_fun, Fintype.card_fin]

end Dat
end
end Lk6
