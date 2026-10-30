-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/AttRuns.lean: THE RUNS OF AN ATTENTION LINK's CLAIMS AT A GEOMETRY WITH THE
CALLS' SHIFTS AND TABLES AND AT THE SAME WITH NONE: flatIn. All but claim 4 read neither: equal; claim 4
gives forms of one shape (the shift stands in constants alone).

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.AttGeo
import Johnson.Desc.K5.Honest.Law.RunsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo CallG ScoreP DivP)
open VerifiableInference.Desc.First.Att.P.Runs (W In JoinsP)
open H2K5.Honest (ShIn RSh JSh SameF sameF_add sameF_const sh_unitKFD sh_claim3 sh_claim5 gather_sh
  formsSh)
open VerifiableInference.Desc.First.Shape (affSh)
open K5Law (OptRel forall₂_zipIdx)

/-- The input of the runs, its calls with no shift and no table. -/
def flatIn (i : In) : In := { i with g := stripG i.g }

variable {K : Nat} {i : In}

theorem claim3_flat (i : In) (j : JoinsP) : P.Runs.claim3 (flatIn i) j = P.Runs.claim3 i j := by
  unfold P.Runs.claim3
  show ((i.g.calls.map stripCG).toList.zipIdx.foldlM _ j) = _
  simp only [Array.toList_map, List.zipIdx_map, List.foldlM_map]
  rfl

theorem joinR16_flat (S : Geo) (d : DivP) (j : JoinsP) :
    P.Runs.joinR16 (stripG S) d j = P.Runs.joinR16 S d j := by
  unfold P.Runs.joinR16
  show ((S.calls.map stripCG).toList.zipIdx.foldl _ j) = _
  simp only [Array.toList_map, List.zipIdx_map, List.foldl_map]
  rfl

theorem claim5_flat (i : In) (j : JoinsP) : P.Runs.claim5 (flatIn i) j = P.Runs.claim5 i j := by
  unfold P.Runs.claim5
  show _ = _
  simp only [flatIn, joinR16_flat]
  rfl

theorem secondRun_flat (i : In) (K : Nat) :
    P.Runs.secondRun (flatIn i) K = P.Runs.secondRun i K := rfl

theorem sameF_keyKFD2 (gC gOm gC' gOm' : Nat) {k k' : ScoreP} (h : k.s0 = k'.s0) :
    SameF (P.Runs.keyKFD gC gOm k) (P.Runs.keyKFD gC' gOm' k') := by
  unfold P.Runs.keyKFD
  dsimp only
  rw [h]
  same_forms

theorem callKFD_rel (H : ShIn i i) (q : Nat) (c : CallG) :
    RSh K SameF (P.Runs.callKFD i q c) (P.Runs.callKFD (flatIn i) q (stripCG c)) := by
  unfold P.Runs.callKFD
  refine H2K5.Honest.RSh.foldlM₂ (R := SameF) (fun _ _ x x' hv h => ?_)
    (forall₂_zipIdx H.scores 0) (sameF_const _ _)
  rw [h.1.same.call, h.2]
  exact H2K5.Honest.RSh.ite Iff.rfl
    (H2K5.Honest.RSh.bind (sh_unitKFD H _ h.1) fun _ _ _ =>
      H2K5.Honest.RSh.pure (sameF_add hv (sameF_keyKFD2 _ _ _ _ h.1.s0)))
    (H2K5.Honest.RSh.pure hv)

theorem claim4_rel (H : ShIn i i) {j j' : JoinsP} (hj : JSh j j') :
    RSh K JSh (P.Runs.claim4 i j) (P.Runs.claim4 (flatIn i) j') := by
  unfold P.Runs.claim4
  show RSh K JSh _ ((i.g.calls.map stripCG).toList.zipIdx.foldlM _ j')
  simp only [Array.toList_map, List.zipIdx_map, List.foldlM_map]
  refine H2K5.Honest.RSh.foldlM1 (R := JSh) (fun j j' x hj => ?_) _ hj
  exact H2K5.Honest.RSh.ite Iff.rfl
    (H2K5.Honest.RSh.bind (callKFD_rel H x.2 x.1) fun _ _ hv =>
      H2K5.Honest.RSh.pure (hj.set _ hv))
    (H2K5.Honest.RSh.pure hj)

/-- **"first" at the input and at its flat: both refuse, or both return: one list of shapes, and key
forms of one shape.** -/
theorem first_flat (H : ShIn i i) (K : Nat) :
    OptRel (fun x x' => x.1.map affSh = x'.1.map affSh ∧ JSh x.2 x'.2) (P.Runs.firstRun i K)
      (P.Runs.firstRun (flatIn i) K) := by
  unfold P.Runs.firstRun
  refine K5Law.OptRel.map (R := fun x x' => JSh x.1 x'.1 ∧ x.2.map affSh = x'.2.map affSh)
    (gather_sh ?_) _ _ fun _ _ h => ⟨h.2, h.1⟩
  have e : (flatIn i).g.calls.size = i.g.calls.size := Array.size_map ..
  rw [e, claim3_flat]
  exact H2K5.Honest.RSh.bind (sh_claim3 H ⟨rfl, rfl⟩) fun _ _ h3 =>
    H2K5.Honest.RSh.bind (claim4_rel H h3) fun _ _ h4 => by
      rw [claim5_flat]
      exact sh_claim5 H h4

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.first_flat
#print axioms Johnson.AtFull.Shape.Scope.secondRun_flat
