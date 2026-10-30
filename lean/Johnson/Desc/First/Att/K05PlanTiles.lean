-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PlanTiles.lean: KIND K5: THE PLAN's SLOTS ARE TILED: at every return A of the planner (Attention.plan, OnBytes/Model/AttentionPlan.lean) the plan's number of
slots is the lookup on the calls' scalars, then the kind's own stretch's slots, then the lookup on the digits' scalars, and nothing more:
  `plan_tiles`: A.ns = Forest.elems A.fs + slotsOf (script A.own) + Forest.elems A.seam.tl.f9.
Why. The table of joints' promise behind the kind's block says that the ledger's next free slot is the first slot of the lookup on the digits, which the public record counts from the END
(ns less that lookup's scalars: digitsNext, Johnson/Desc/First/Look/LookAt.lean), while the kind's hearing counts from the front. That the two meet is this identity, with "the plan's ledger starts at slot 0" (the library's planA_next0, OnBytes/Tie/Pv/Lookup/Ends/FoNext0.lean), which is not called here.
It is an identity of two counts: the planner's (ownScalars; Counts.of, a fold over the calls) and the description's (slotsOf of script, Johnson/Desc/First/Att/K5AttentionKind.lean | K5Returns.lean).
  `products_slots`: a sumcheck of products takes sc3Slots. `script_slots`: slotsOf (script x) as a sum, at every x. `counts_inv`: the fold's invariant: the scalars counted for the key forms
  are three a plane segment and seven and a sumcheck a score segment.
Used of the library: seamPlan_cut, addTreesF_sameP (OnBytes/Tie/Pv/Lookup/Ends/FoZMade.lean): the seam's plan keeps the digits' lookup's record; ownSlots_eq (Johnson/Desc/Part/MaskedSumSound.lean); of the kind's own: slotsOf_append (Johnson/Desc/First/Att/K05Room.lean).
Limits: a fact on the planner's return alone. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05Room
import Johnson.Desc.Part.MaskedSumSound
import OnBytes.Model.AttentionPlan
import OnBytes.Tie.Pv.Lookup.Ends.FoZMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends ownSlots_eq)
open Fo.BatRows (bindE_ok ite_ok)

theorem foldl_plus : ∀ (l : List ℕ) (n : ℕ), l.foldl (· + ·) n = n + l.sum
  | [], n => by simp
  | a :: l, n => by
    simp only [List.foldl_cons, List.sum_cons]
    rw [foldl_plus l]
    omega

theorem slotsOf_scalars3 : ∀ n : ℕ, slotsOf (List.replicate n (.scalars 3)) = 3 * n
  | 0 => rfl
  | n + 1 => by
    show 3 + slotsOf (List.replicate n (.scalars 3)) = 3 * (n + 1)
    rw [slotsOf_scalars3 n]
    omega

/-- A sumcheck of products takes the planner's number of scalars. -/
theorem products_slots (n m : ℕ) : (products n m).slots = Attention.sc3Slots n m := by
  show MaskedSum.ownSlots (List.replicate n (Var.plain 4) ++ [Var.point zeroE (2 + 1)]) + 2 * m = _
  rw [ownSlots_eq]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Var.d, smul_eq_mul]
  show _ = 1 + n * 3 + 2 + 2 * m
  omega

theorem slotsOf_scores : ∀ l : List (ℕ × ℕ), slotsOf (l.flatMap fun u => [.scalars 7, products u.1 u.2]) =
    (l.map fun u => 7 + Attention.sc3Slots u.1 u.2).sum
  | [] => rfl
  | u :: l => by
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    rw [slotsOf_append, slotsOf_scores l]
    show 7 + ((products u.1 u.2).slots + 0) + _ = _
    rw [products_slots]
    omega

/-- The sumcheck for the key at the index takes the planner's number of scalars. -/
theorem keyAt_slots (lt lgk n : ℕ) :
    (Stage.sum ((List.replicate lt 3 ++ List.replicate lgk (lt + 3) ++ List.replicate lt (lt + 2)).map Var.plain) ⟨lt + 1, n⟩).slots =
      sumcheckSlotsDegrees (List.replicate lt 2 ++ List.replicate lgk (lt + 2) ++ List.replicate lt (lt + 1)) n (lt + 1) := by
  show MaskedSum.ownSlots (_ ++ [Var.point zeroE (lt + 1 + 1)]) + n = _
  rw [ownSlots_eq]
  unfold sumcheckSlotsDegrees
  rw [foldl_plus]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Var.d, smul_eq_mul]
  have e1 : lt + 3 - 1 = lt + 2 := by omega
  have e2 : lt + 2 - 1 = lt + 1 := by omega
  simp only [e1, e2, Nat.reduceSub]
  omega

/-- **The stretch's slots, as a sum.** -/
theorem script_slots (x : Params.AttentionRounds) : slotsOf (script x) =
    3 * x.planeMessages + (x.score.map fun u => 7 + Attention.sc3Slots u.1 u.2).sum +
      (7 + x.lt + Attention.sc3Slots x.e x.pairs) +
      (2 + Attention.sc3Slots x.valueM x.pairs + Attention.sc3Slots x.valueD x.pairs) +
      (x.pairs + Attention.sc3Slots x.attained x.pairs +
        sumcheckSlotsDegrees (List.replicate x.lt 2 ++ List.replicate x.lgk (x.lt + 2) ++ List.replicate x.lt (x.lt + 1))
          (x.Lam + x.pairs * x.lt) (x.lt + 1) + Attention.sc3Slots x.bits x.pairs) := by
  unfold script
  dsimp only
  rw [slotsOf_append, slotsOf_append, slotsOf_scalars3, slotsOf_scores]
  simp only [slotsOf]
  have k := keyAt_slots x.lt x.lgk (x.Lam + x.pairs * x.lt)
  have p1 := products_slots x.e x.pairs
  have p2 := products_slots x.valueM x.pairs
  have p3 := products_slots x.valueD x.pairs
  have p4 := products_slots x.attained x.pairs
  have p5 := products_slots x.bits x.pairs
  rw [p1, p2, p3, p4, p5, k]
  clear p1 p2 p3 p4 p5 k
  generalize Attention.sc3Slots x.e x.pairs = s1
  generalize Attention.sc3Slots x.valueM x.pairs = s2
  generalize Attention.sc3Slots x.valueD x.pairs = s3
  generalize Attention.sc3Slots x.attained x.pairs = s4
  generalize Attention.sc3Slots x.bits x.pairs = s5
  generalize sumcheckSlotsDegrees _ _ _ = s6
  generalize (List.map (fun u : ℕ × ℕ => 7 + Attention.sc3Slots u.1 u.2) x.score).sum = s7
  show 3 * x.planeMessages + s7 + (5 + (x.lt + (2 + (s1 + (0 + (2 + (s2 + (s3 + (0 + (x.pairs + (0 + (s4 + (0 + (s6 + (0 + (s5 + 0)))))))))))))))) = _
  omega

/-- What the fold over the calls keeps. -/
def CountsInv (x : Attention.Counts) : Prop :=
  x.msg = 3 * x.nKRp + (x.score.toList.map fun u => 7 + Attention.sc3Slots u.1 u.2).sum

theorem inv_plane (k : Attention.ACall) (x : Attention.Counts) (s : Attention.Seg) (h : CountsInv x) :
    CountsInv (Attention.Counts.plane k x s) := by
  unfold Attention.Counts.plane
  split
  · unfold CountsInv at h ⊢
    dsimp only
    omega
  · exact h

theorem inv_scores (S : Attention.Shape) (k : Attention.ACall) (x : Attention.Counts) (s : Attention.Seg) (h : CountsInv x) :
    CountsInv (Attention.Counts.scores S k x s) := by
  unfold Attention.Counts.scores
  split
  · unfold CountsInv at h ⊢
    dsimp only
    rw [Array.toList_push, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · exact h

theorem inv_call (S : Attention.Shape) (x : Attention.Counts) (k : Attention.ACall) (h : CountsInv x) :
    CountsInv (Attention.Counts.call S x k) := by
  unfold Attention.Counts.call
  dsimp only
  have hy : CountsInv (if k.kind == .kr then [Attention.Seg.rm, Attention.Seg.rd].foldl (Attention.Counts.plane k) x else x) := by
    split
    · exact inv_plane k _ _ (inv_plane k _ _ h)
    · exact h
  split
  · exact inv_scores S k _ _ (inv_scores S k _ _ hy)
  · exact hy

theorem inv_fold (S : Attention.Shape) : ∀ (l : List Attention.ACall) (x : Attention.Counts), CountsInv x →
    CountsInv (l.foldl (Attention.Counts.call S) x)
  | [], _, h => h
  | k :: l, x, h => inv_fold S l _ (inv_call S x k h)

/-- **The fold's invariant at its end.** -/
theorem counts_inv (S : Attention.Shape) : CountsInv (Attention.Counts.of S) := by
  unfold Attention.Counts.of
  rw [← Array.foldl_toList]
  exact inv_fold S _ _ (by unfold CountsInv; rfl)

/-- **THE PLAN's SLOTS ARE TILED.** -/
theorem plan_tiles {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (e : Attention.plan settings i cf = .ok A) :
    A.ns = Forest.elems A.fs + slotsOf (script A.own) + Forest.elems A.seam.tl.f9 := by
  unfold Attention.plan at e
  dsimp only at e
  split at e
  · cases e
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · cases e
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · cases e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨⟨S, fs⟩, hS, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · cases e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam0, h0, e⟩ := bindE_ok e
  split at e
  · cases e
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · cases e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam, h1, e⟩ := bindE_ok e
  cases e
  obtain ⟨T, hT⟩ := Fo.ZPlan.seamPlan_cut h1
  have hf : seam.tl.f9 = seam0.tl.f9 := (Fo.ZPlan.addTreesF_sameP hT).f9
  show Attention.ownScalars S fs (Attention.Counts.of S) + seam0.smallElems = Forest.elems fs + slotsOf (script _) + Forest.elems seam.tl.f9
  rw [hf, script_slots]
  have hc := counts_inv S
  unfold CountsInv at hc
  unfold Attention.ownScalars Attention.Seam.smallElems HTailF2.smallElems Attention.Shape.scdDegrees
  dsimp only
  omega

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.script_slots
#print axioms VerifiableInference.Desc.First.Att.P.counts_inv
#print axioms VerifiableInference.Desc.First.Att.P.plan_tiles
