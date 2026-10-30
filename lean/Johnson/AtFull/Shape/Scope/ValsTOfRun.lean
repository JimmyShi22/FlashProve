-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/ValsTOfRun.lean: AT AN ATTENTION LINK THE TWO TESTS ON VALUES (valsT | valsTS: the units' inner points and
the division's points share their last coordinates with the lookup's point) COME OFF THE VERIFIER's OWN TEXT: what the
attention's claim runs read (K5Law.inAt: the points, then the tables' maker) is there only where both tests pass, since
the tables' maker makes them itself (tablesP_isSome: it returns just where placeOk accepts). No thread, no prover, no
draw, no fall.

  valsT_of_inAt    inAt returns ⊢ valsT accepts, at the state's own parts
  valsT_of_first   the run "first" returns ⊢ the same (firstAt); valsT_of_second likewise
  valsTS_of_inOf   the same on the state: the runs' own reader P.inOf returns at a record that stands in an attention link

Limits. Implications from a return. THAT A CLAIM RUN OF THE BATCHING's MEMBER IS firstAt | secondAt AT THE STATE IN FRONT OF IT IS
NOT SHOWN HERE. One row's share of the cell's test. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.TabsChain
import Johnson.Desc.First.Att.Claims.InAt
import Johnson.Desc.First.Att.Claims.ReadsReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Heard)
open H2K5.Honest (valsT valsTS)

/-- **What the attention's claim runs read is there only where the two tests on values pass.** -/
theorem valsT_of_inAt (A : Attention.Plan) {gl : Forest.Heard} {h : Heard} {F : Fork}
    (hx : (K5Law.inAt (P.parCOf A) gl h F).isSome = true) : valsT A gl h F = true := by
  unfold K5Law.inAt at hx
  unfold valsT
  cases hp : P.ptsFrom (P.parCOf A).geo gl.zk h F with
  | none =>
    rw [hp] at hx
    cases hx
  | some p =>
    rw [hp] at hx
    cases ht : P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
        (P.lookOfO (P.parCOf A).geo.lmb gl) p with
    | none =>
      simp [ht] at hx
    | some t =>
      have ho := K5Law.tablesP_isSome (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
        (P.lookOfO (P.parCOf A).geo.lmb gl) p
      rw [ht] at ho
      have hk : K5Law.placeOk (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
          (P.lookOfO (P.parCOf A).geo.lmb gl) p = true := ho.symm
      unfold K5Law.placeOk at hk
      simp only [Bool.and_eq_true] at hk
      show (P.mergedPlanes (P.parCOf A).geo.lmS gl.zx p.planes &&
        P.mergedTokens (P.parCOf A).geo gl.zx p.d) = true
      rw [Bool.and_eq_true]
      exact ⟨hk.1.1.1.1.1, hk.1.1.1.1.2⟩

/-- From a return of the run "first". -/
theorem valsT_of_first (A : Attention.Plan) {gl : Forest.Heard} {h : Heard} {F : Fork}
    (hx : (K5Law.firstAt (P.parCOf A) gl h F).isSome = true) : valsT A gl h F = true := by
  refine valsT_of_inAt A ?_
  unfold K5Law.firstAt at hx
  cases hi : K5Law.inAt (P.parCOf A) gl h F with
  | none =>
    rw [hi] at hx
    cases hx
  | some _ => rfl

/-- From a return of the run "second". -/
theorem valsT_of_second (A : Attention.Plan) {gl : Forest.Heard} {h : Heard} {F : Fork}
    (hx : (K5Law.secondAt (P.parCOf A) gl h F).isSome = true) : valsT A gl h F = true := by
  refine valsT_of_inAt A ?_
  unfold K5Law.secondAt at hx
  cases hi : K5Law.inAt (P.parCOf A) gl h F with
  | none =>
    rw [hi] at hx
    cases hx
  | some _ => rfl

/-- **On the state.** -/
theorem valsTS_of_inOf (A : Attention.Plan) {e : First.S} {a : First.AttOwn} (he : e.here = .att a)
    (hx : (P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) e).isSome = true) : valsTS A e = true := by
  rw [K5Law.inOf_isAt he] at hx
  unfold valsTS
  rw [he]
  dsimp only
  cases hg : a.g with
  | none =>
    rw [hg] at hx
    cases hx
  | some gl =>
    rw [hg] at hx
    cases h5 : a.heard5 with
    | none =>
      rw [h5] at hx
      cases hx
    | some h =>
      rw [h5] at hx
      exact valsT_of_inAt A hx

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.valsT_of_inAt
#print axioms Johnson.AtFull.Shape.Scope.valsT_of_first
#print axioms Johnson.AtFull.Shape.Scope.valsT_of_second
#print axioms Johnson.AtFull.Shape.Scope.valsTS_of_inOf
