-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SpecProof.lean: the honest side of the kind "lookup" (K3). The
proof of `LawfulSpec` (Honest/K3/Law/SpecLawful.lean): conditional on `Fit R`, `Numbered R` and
`SpecAt R N w`, the specification's summands meet `Lawful`, the hypothesis of every statement on
values of Honest/K3/Law/Statements.lean. Theorems.

Terms. Honest/K3/GLOSSARY.md ("course", "lawful", "specification", "stage").

What is shown.
  `sums_tie0`, `sums_tie`, `sums_key`, `sums_tab`, `sums_bits`, `sums_leaves`: stage by stage.
  `bits_end`, `count_ok`, `key_end`: the three clauses that sum nothing.
  `lawfulSpec`: the statement.
Others: `key_claimed`, `tab_claimed`, `varsFit_nil`, `varsFit_tie`, `claimed_tie0`, `claimed_tie1`,
`claimed_tie2`, `len_tie`, `byBit_toArray`.

Hypotheses that remain. `Fit R`, `Numbered R` and `SpecAt R N w`. `Fit R` is not used by the proof:
what it would give stands in `Numbered R`. In the steps they are `hW` and `hS`; besides: `hs`, `hc`:
the tie's step is one of the row's, with its call; `hm`, `hl`: a level's number is in range; `h`:
(in `varsFit_nil`) the job has no variable.

How the proof goes. It rests on the specification's own theorems (Johnson/HonestTrace/LookCube.lean,
Johnson/HonestTrace/LookJobs.lean, Johnson/HonestTrace/LookRows.lean), on
Honest/K3/JobsSpecSums.lean and Honest/K3/JobsSpecStages.lean, and on the files
Honest/K3/Law/Spec*.lean beside it.

Users. This file is imported by Honest/K3/Law/SpecMember.lean.

Limits. The three hypotheses are not shown of any course here. One part of keys.
An instance: Honest/K3/Law/SpecMember.lean (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecCourse
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE oneE addE subE mulE)
open OnBytes.Model (orderDefault ofNat)
open OnBytes.Slice (readE readE_zero)
open OnBytes.HonestTrace.Look (Job Data pj ext tieJob keyJob tabJob leavesJob bitsJob)
open VerifiableInference.Desc.First.ProdV (levelVars levelEnds)
open VerifiableInference.Desc.K3 (leafVars bitsCall noVar eqPairs)

variable {P : Type} {N : KE → TwV.Nums P KE} {w : Hidden} {R : Course Ask}

-- `Sums` is never unfolded below. At a sumcheck without a variable its list of variables is a
-- literal, so that Lean, left to itself, goes on to unfold the run's list of challenges, which is
-- costly and serves nothing.
attribute [local irreducible] Sums

/-- No variable: nothing to fit. -/
theorem varsFit_nil (J : Job KE) (h : J.zs = []) : VarsFit [] J :=
  ⟨by simp [h], fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

/-- What is claimed at the tie's first step: 0. -/
theorem claimed_tie0 (R : Course Ask) : R.claimed (.tie 0) = zeroE := rfl
/-- At its second: the first step's second end value. -/
theorem claimed_tie1 (R : Course Ask) : R.claimed (.tie 1) = R.T (.tie 0) 1 := rfl
/-- At a later one: the first end value of the step in front. -/
theorem claimed_tie2 (R : Course Ask) (i : Nat) : R.claimed (.tie (i + 2)) = R.T (.tie (i + 1)) 0 :=
  rfl

/-- The tie's steps have no variable. -/
theorem varsFit_tie (D : Data P KE) (j dY n : Nat) (zs : List E) :
    VarsFit (withPoints (noVar dY n).vs zs) (tieJob D j) := by
  show VarsFit [] _
  exact varsFit_nil _ rfl

/-- Conditional on `Numbered R`: a step of the tie has one challenge: Y's. -/
theorem len_tie (hW : Numbered R) (j dY n : Nat) (hs : Stage.tie j ∈ stages R.f)
    (hc : (Stage.tie j).call R.f = some (noVar dY n)) :
    (R.r (.tie j)).length = (noVar dY n).vs.length + 1 := by
  rw [hW.len _ hs, shapeAt_eq R _ _ hc]
  rfl

/-- Conditional on `Numbered R` and `SpecAt R N w`: the tie's first step sums as `Lawful` asks. -/
theorem sums_tie0 (hW : Numbered R) (hS : SpecAt R N w) :
    Sums R (.tie 0) (rd (R.claimed (.tie 0))) (rd (endTerm R.factor (.tie 0) (R.shown (.tie 0)))) :=
      by
  have hs := mem_tie0 hS
  have hc : (Stage.tie 0).call R.f = some (noVar 3 3) := rfl
  have hm : (R.masks (.tie 0)).length = 3 := hW.masks _ hs
  have hn : ∀ xs, ((tieJob (dataAt N w R.pts) 0).ends xs).length = 3 := fun xs => by
    rw [OnBytes.HonestTrace.Look.tie_ends_zero]
    rfl
  have key := sums_stage_ends R (.tie 0) (noVar 3 3) ⟨3, 3⟩ (tieJob (dataAt N w R.pts) 0) hc rfl
    (carried_tie hW hS 0 hs)
    (OnBytes.HonestTrace.Look.tieJob_lawful _ hS.mid (Nat.zero_le _)) (sized_tie _ 0) rfl
    (varsFit_tie _ 0 3 3 _) hn (len_tie hW 0 3 3 hs hc) hm
  have e1 : rd (R.claimed (.tie 0)) = (tieJob (dataAt N w R.pts) 0).sum := by
    rw [OnBytes.HonestTrace.Look.tie_sum_zero, claimed_tie0]
    exact readE_zero
  rw [endTerm_tie0 (dataAt N w R.pts) R.factor hS.factor, e1]
  exact key

/-- Conditional on `Numbered R` and `SpecAt R N w`: a later step of the tie. -/
theorem sums_tie (hW : Numbered R) (hS : SpecAt R N w) (j : Nat)
    (hs : Stage.tie (j + 1) ∈ stages R.f) :
    Sums R (.tie (j + 1)) (rd (R.claimed (.tie (j + 1))))
      (rd (endTerm R.factor (.tie (j + 1)) (R.shown (.tie (j + 1))))) := by
  have hj := tie_lt hs
  have hpl := hS.nums.planes
  have hn0 : j + 1 ≤ (dataAt N w R.pts).N.n := by
    show j + 1 ≤ (N (up R.pts.theta)).n
    omega
  have hc : (Stage.tie (j + 1)).call R.f = some (noVar 3 2) := rfl
  have hm : (R.masks (.tie (j + 1))).length = 2 := hW.masks _ hs
  have hn : ∀ xs, ((tieJob (dataAt N w R.pts) (j + 1)).ends xs).length = 2 := fun xs => by
    rw [OnBytes.HonestTrace.Look.tie_ends_succ]
    rfl
  have key := sums_stage_ends R (.tie (j + 1)) (noVar 3 2) ⟨3, 2⟩ (tieJob (dataAt N w R.pts)
    (j + 1))
    hc rfl (carried_tie hW hS (j + 1) hs)
    (OnBytes.HonestTrace.Look.tieJob_lawful _ hS.mid hn0) (sized_tie _ _) rfl
    (varsFit_tie _ _ 3 2 _) hn (len_tie hW _ 3 2 hs hc) hm
  have e1 : rd (R.claimed (.tie (j + 1))) = (tieJob (dataAt N w R.pts) (j + 1)).sum := by
    rw [OnBytes.HonestTrace.Look.tie_sum_succ]
    cases j with
    | zero =>
      rw [claimed_tie1, T_read R (.tie 0) (noVar 3 3) _ rfl (carried_tie hW hS 0 (mem_tie0 hS)),
        OnBytes.HonestTrace.Look.tie_ends_zero]
      rfl
    | succ i =>
      rw [claimed_tie2, T_read R (.tie (i + 1)) (noVar 3 2) _ rfl
        (carried_tie hW hS (i + 1) (mem_tie (by omega))),
        OnBytes.HonestTrace.Look.tie_ends_succ]
      rfl
  rw [endTerm_tie (dataAt N w R.pts) R.factor j, e1]
  exact key

/-- Conditional on `Numbered R` and `SpecAt R N w`: what is claimed in front of the key tree's level
with m variables; at m := v: behind the tree. -/
theorem key_claimed (hW : Numbered R) (hS : SpecAt R N w) (m : Nat)
    (hm : m ≤ (dataAt N w R.pts).v) :
    rd (R.claimed (.key 0 m)) =
      ext m ((dataAt N w R.pts).kLvl m) (byBit (R.pts.keyPt 0 m)) := by
  cases m with
  | zero => exact key_zero hW hS
  | succ m => exact key_succ hW hS m hm

/-- Conditional on `Numbered R` and `SpecAt R N w`: a level of the key tree. -/
theorem sums_key (hW : Numbered R) (hS : SpecAt R N w) (m : Nat)
    (hm : m < (dataAt N w R.pts).v) :
    Sums R (.key 0 m) (rd (R.claimed (.key 0 m)))
      (rd (endTerm R.factor (.key 0 m) (R.shown (.key 0 m)))) := by
  have hs : Stage.key 0 m ∈ stages R.f := mem_key hS.nums.parts hm
  obtain ⟨_, _, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  have hp : ((dataAt N w R.pts).N.oK m).Perm (List.range m) := hS.nums.permK m hm
  have hK : (dataAt N w R.pts).N.oK m = R.f.orders 0 m := hS.nums.oK m
  have hz : (R.pts.keyPt 0 m).size = m := size_keyPt _ _ _ 0 m
  have hv : VarsFit (withPoints (levelCall m).vs (pointsAt R.f (.key 0 m) (R.ptsAt (.key 0 m))))
      (keyJob (dataAt N w R.pts) m (byBit (R.pts.keyPt 0 m))) := by
    rw [withPoints_key R.f 0 m _ (by rw [← hK, hp.length_eq, List.length_range]), h3, ← hK]
    exact varsFit_level m 0 _ _ _ _ hz hp
  have key := sums_stage_ends R (.key 0 m) (levelCall m) levelEnds
    (keyJob (dataAt N w R.pts) m (byBit (R.pts.keyPt 0 m))) rfl rfl (carried_key hW hS m hs)
    (OnBytes.HonestTrace.Look.pj_lawful m 0 _ _ _ _ hp (by rw [byBit_length, hz]))
    (sized_pj m 0 _ _ _ _ (by rw [hp.length_eq, List.length_range])) rfl hv (fun _ => rfl)
    (by rw [len_level hW _ m hs rfl, levelCall_len]) (hW.masks _ hs)
  rw [key_claimed hW hS m (Nat.le_of_lt hm), ← OnBytes.HonestTrace.Look.keyJob_sum _ hm,
    show rd (endTerm R.factor (.key 0 m) (R.shown (.key 0 m))) = _ from
      endTerm_level m _ _ ((dataAt N w R.pts).N.oK m) (byBit (R.pts.keyPt 0 m)) _]
  exact key

/-- Conditional on `Numbered R` and `SpecAt R N w`: what is claimed in front of the table side's
level number l; at l := d: in front of the leaves. -/
theorem tab_claimed (hW : Numbered R) (hS : SpecAt R N w) (l : Nat) (hl : l ≤ R.f.d) :
    rd (R.tabV l) = ext ((dataAt N w R.pts).N.w + l) ((dataAt N w R.pts).tLvl l)
      (byBit (R.pts.tabPt l)) := by
  cases l with
  | zero => exact tab_zero hW hS
  | succ l => exact tab_succ hW hS l hl

/-- Conditional on `Numbered R` and `SpecAt R N w`: a level of the table side. -/
theorem sums_tab (hW : Numbered R) (hS : SpecAt R N w) (l : Nat) (hl : l < R.f.d) :
    Sums R (.tab l) (rd (R.claimed (.tab l)))
      (rd (endTerm R.factor (.tab l) (R.shown (.tab l)))) := by
  have hs : Stage.tab l ∈ stages R.f := mem_tabOf hl
  obtain ⟨_, _, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  have hw : (dataAt N w R.pts).N.w = R.f.mu := hS.nums.w
  have hd : (dataAt N w R.pts).N.d = R.f.d := hS.nums.d
  have hT : (dataAt N w R.pts).N.oT l = orderDefault (R.f.mu + l) := hS.nums.oT l
  have hp : ((dataAt N w R.pts).N.oT l).Perm (List.range ((dataAt N w R.pts).N.w + l)) := by
    rw [hT, hw]
    exact perm_orderDefault _
  have hz : (R.pts.tabPt l).size = (dataAt N w R.pts).N.w + l := by
    rw [hw]
    exact size_tabPt _ _ _ l
  have hv : VarsFit
      (withPoints (levelCall (R.f.mu + l)).vs (pointsAt R.f (.tab l) (R.ptsAt (.tab l))))
      (tabJob (dataAt N w R.pts) l (byBit (R.pts.tabPt l))) := by
    rw [withPoints_tab, h3, ← hT, ← hw]
    exact varsFit_level _ 0 _ _ _ _ hz hp
  have key := sums_stage_ends R (.tab l) (levelCall (R.f.mu + l)) levelEnds
    (tabJob (dataAt N w R.pts) l (byBit (R.pts.tabPt l))) rfl rfl (carried_tab hW hS l hs)
    (OnBytes.HonestTrace.Look.pj_lawful _ 0 _ _ _ _ hp (by rw [byBit_length, hz]))
    (sized_pj _ 0 _ _ _ _ (by rw [hp.length_eq, List.length_range])) rfl hv (fun _ => rfl)
    (by rw [len_level hW _ _ hs rfl, levelCall_len]) (hW.masks _ hs)
  rw [show R.claimed (.tab l) = R.tabV l from rfl, tab_claimed hW hS l (Nat.le_of_lt hl),
    ← OnBytes.HonestTrace.Look.tabJob_sum _ (by rw [hd]; exact hl),
    show rd (endTerm R.factor (.tab l) (R.shown (.tab l))) = _ from
      endTerm_level ((dataAt N w R.pts).N.w + l) _ _ ((dataAt N w R.pts).N.oT l)
        (byBit (R.pts.tabPt l)) _]
  exact key

/-- Conditional on `Numbered R` and `SpecAt R N w`: the bits. -/
theorem sums_bits (hW : Numbered R) (hS : SpecAt R N w) :
    Sums R .bits (rd (R.claimed .bits)) (rd (endTerm R.factor .bits (R.shown .bits))) := by
  have hs : Stage.bits ∈ stages R.f := mem_bits R.f
  obtain ⟨_, _, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  have hw : (dataAt N w R.pts).N.w = R.f.mu := hS.nums.w
  have hd : (dataAt N w R.pts).N.d = R.f.d := hS.nums.d
  have hB : (dataAt N w R.pts).N.oB =
      orderDefault ((dataAt N w R.pts).N.w + (dataAt N w R.pts).N.d) := by
    rw [hw, hd]
    exact hS.nums.oB
  have hz : R.pts.zeroPt.size = (dataAt N w R.pts).N.w + (dataAt N w R.pts).N.d := by
    rw [hw, hd]
    exact size_zeroPt _ _ _
  have hv : VarsFit (withPoints (bitsCall (List.replicate (R.f.mu + R.f.d) zeroE)).vs
      (pointsAt R.f .bits (R.ptsAt .bits))) (bitsJob (dataAt N w R.pts) (byBit R.pts.zeroPt)) := by
    rw [withPoints_bits R.f _ (size_zeroPt _ _ _), h3]
    exact varsFit_bits _ _ hB hz
  have key := sums_stage_ends R .bits (bitsCall (List.replicate (R.f.mu + R.f.d) zeroE)) ⟨2, 1⟩
    (bitsJob (dataAt N w R.pts) (byBit R.pts.zeroPt)) rfl rfl (carried_bits hW hS hs)
    (OnBytes.HonestTrace.Look.bitsJob_lawful _ _ (by rw [byBit_length, hz])
      (by rw [hB]; exact perm_orderDefault _))
    (sized_bits _ _ (by rw [hB, (perm_orderDefault _).length_eq, List.length_range])) rfl hv
    (fun _ => rfl)
    (by
      rw [hW.len _ hs, shapeAt_eq R _ _ rfl]
      show (_ ++ [_]).length = _
      rw [List.length_append]
      rfl) (hW.masks _ hs)
  rw [endTerm_bits (dataAt N w R.pts) R.factor (byBit R.pts.zeroPt),
    show rd (R.claimed .bits) = (bitsJob (dataAt N w R.pts) (byBit R.pts.zeroPt)).sum by
      rw [OnBytes.HonestTrace.Look.bitsJob_sum _ hS.mid]
      exact readE_zero]
  exact key

/-- A list as an array, translated: the readings reversed. -/
theorem byBit_toArray (l : List E) : byBit l.toArray = (ups l).reverse := by
  simp [byBit, ups]

/-- Conditional on `Numbered R` and `SpecAt R N w`: the leaves. -/
theorem sums_leaves (hW : Numbered R) (hS : SpecAt R N w) :
    Sums R .leaves (rd (R.claimed .leaves))
      (1 + rd (R.f.leaf R.pts.theta R.pts.alpha R.zb0) *
        planesOf (dataAt N w R.pts) (eqPairs (R.f.mu + R.f.d) R.zb0)) := by
  have hs : Stage.leaves ∈ stages R.f := mem_leaves R.f
  obtain ⟨_, _, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  have hw : (dataAt N w R.pts).N.w = R.f.mu := hS.nums.w
  have hd : (dataAt N w R.pts).N.d = R.f.d := hS.nums.d
  have hE : (dataAt N w R.pts).N.oE = orderDefault (R.f.mu + R.f.d) := hS.nums.oE
  have hz : (R.pts.tabPt R.f.d).size = R.f.mu + R.f.d := size_tabPt _ _ _ _
  have hlen : (R.r .leaves).length = R.f.mu + R.f.d := by
    rw [hW.len _ hs, shapeAt_eq R _ _ rfl]
    show (leafVars R.f #[]).length = _
    simp [leafVars]
  have hv : VarsFit (withPoints (leafVars R.f #[]) (pointsAt R.f .leaves (R.ptsAt .leaves)))
      (leavesJob (dataAt N w R.pts) (byBit (R.pts.tabPt R.f.d))) := by
    rw [withPoints_leaves, h3]
    exact varsFit_leaves R.f _ _ hw hE hz
  have key := sums_stage_open R .leaves ⟨0, leafVars R.f #[], none⟩
    (leavesJob (dataAt N w R.pts) (byBit (R.pts.tabPt R.f.d))) rfl rfl (carried_leaves hW hS hs)
    (OnBytes.HonestTrace.Look.leavesJob_lawful _ _ (by rw [byBit_length, hz, hw, hd])
      (by rw [hE, hw, hd]; exact perm_orderDefault _))
    (sized_leaves _ _) hv (by rw [hlen]; simp [leafVars])
  have hz0 : R.zb0.size = R.f.mu + R.f.d := by rw [hW.zb0]; simpa using hlen
  have hb : byBit R.zb0 = (ups (R.r .leaves)).reverse := by rw [hW.zb0, byBit_toArray]
  rw [show R.claimed .leaves = R.tabV R.f.d from rfl, tab_claimed hW hS _ (Nat.le_refl _), ← hd,
    ← OnBytes.HonestTrace.Look.leavesJob_sum]
  rw [hd]
  have e : (1 : KE) + rd (R.f.leaf R.pts.theta R.pts.alpha R.zb0) *
      planesOf (dataAt N w R.pts) (eqPairs (R.f.mu + R.f.d) R.zb0) =
      (leavesJob (dataAt N w R.pts) (byBit (R.pts.tabPt R.f.d))).fin (ups (R.r .leaves)) := by
    rw [leaves_fin _ _ _ (by simp [ups, hlen, hw, hd]) (by rw [hE, hw, hd]), ← hb,
      show rd (R.f.leaf R.pts.theta R.pts.alpha R.zb0) = _ from hS.leaf, hw, hd,
      ← hw, ← hd, planes_eq _ _ (by rw [hz0, hw, hd]), mul_comm]
    rfl
  rw [e]
  exact key

/-- Conditional on `Numbered R` and `SpecAt R N w`: the bits' sumcheck's true end value is the
planes' value at its point. -/
theorem bits_end (hW : Numbered R) (hS : SpecAt R N w) :
    rd (R.T .bits 0) = planesOf (dataAt N w R.pts) (eqPairs (R.f.mu + R.f.d) R.zb1) := by
  have hs : Stage.bits ∈ stages R.f := mem_bits R.f
  have hw : (dataAt N w R.pts).N.w = R.f.mu := hS.nums.w
  have hd : (dataAt N w R.pts).N.d = R.f.d := hS.nums.d
  have hvl : (bitsCall (List.replicate (R.f.mu + R.f.d) zeroE)).vs.length = R.f.mu + R.f.d := by
    simp [bitsCall]
  have hlen : (R.r .bits).length = R.f.mu + R.f.d + 1 := by
    rw [hW.len _ hs, shapeAt_eq R _ _ rfl]
    show (_ ++ [_]).length = _
    rw [List.length_append, hvl]
    rfl
  have hl : ((R.r .bits).take (R.f.mu + R.f.d)).length = R.f.mu + R.f.d := by
    rw [List.length_take, hlen]
    omega
  have hx : (ups ((R.r .bits).take (R.f.mu + R.f.d))).length = R.f.mu + R.f.d := by
    unfold ups
    rw [List.length_map, hl]
  have hbv := byVar_down (ups ((R.r .bits).take (R.f.mu + R.f.d)))
  rw [hx] at hbv
  have e := planes_eq (dataAt N w R.pts) R.zb1 (by rw [hW.zb1, hw, hd]; simpa using hl)
  rw [hw, hd] at e
  rw [e, T_read R .bits _ _ rfl (carried_bits hW hS hs), hvl, hW.zb1,
    byBit_toArray ((R.r .bits).take (R.f.mu + R.f.d)), ← hbv,
    ← show (dataAt N w R.pts).N.oB = orderDefault (R.f.mu + R.f.d) from hS.nums.oB, ← hw, ← hd]
  rfl

/-- Conditional on `SpecAt R N w`: the counts add up. -/
theorem count_ok (hS : SpecAt R N w) :
    planesOf (dataAt N w R.pts) (countPairs R.f) = rd (ofNat R.f.count) := by
  rw [planes_count R.f _ hS.nums.w hS.nums.room
    (fun u j hj => if_neg (Nat.not_lt.2 hj)) hS.mid,
    show rd (ofNat R.f.count) = ((R.f.count : Nat) : KE) from OnBytes.Ends.A.readE_ofNat _]
  congr 1
  unfold VerifiableInference.Desc.K3.Face.count VerifiableInference.Desc.K3.Face.allKeys
  rw [hS.nums.parts, ← hS.padding]
  simp [Cb.Lkp.padNum, Data.v]
  rfl

/-- Conditional on `Numbered R` and `SpecAt R N w`: behind the key tree: alpha less the keys' value
at the tree's last point. -/
theorem key_end (hW : Numbered R) (hS : SpecAt R N w) :
    rd (R.claimed (.key 0 (dataAt N w R.pts).v)) =
      rd R.pts.alpha - keysOf (dataAt N w R.pts) 0 (R.pts.keyPt 0 (dataAt N w R.pts).v) := by
  rw [key_claimed hW hS _ (Nat.le_refl _),
    key_top _ _ (by rw [byBit_length]; exact size_keyPt _ _ _ 0 _)]
  rfl

/-- **Conditional on `Fit R`, `Numbered R` and `SpecAt R N w`: the specification's summands are
lawful.** An instance of the three hypotheses: Honest/K3/Law/SpecMember.lean (by evaluation). -/
theorem lawfulSpec : LawfulSpec := by
  intro P N w R _ hW hS
  refine ⟨fun s hs ht => ?_, sums_leaves hW hS, bits_end hW hS, count_ok hS, fun y hy => ?_⟩
  · cases s with
    | tie j =>
      cases j with
      | zero => exact sums_tie0 hW hS
      | succ j => exact sums_tie hW hS j hs
    | split i =>
      have := split_lt hs
      rw [hS.nums.parts] at this
      exact absurd this (Nat.not_lt_zero _)
    | key i m =>
      obtain ⟨rfl, hm⟩ := key_lt hS.nums.parts hs
      exact sums_key hW hS m hm
    | tab l => exact sums_tab hW hS l (tab_lt hs)
    | bits => exact sums_bits hW hS
    | shift => exact absurd ht (Nat.lt_irrefl 0)
    | alpha => exact absurd ht (Nat.lt_irrefl 0)
    | join => exact absurd ht (Nat.lt_irrefl 0)
    | keyLine i m => exact absurd ht (Nat.lt_irrefl 0)
    | tabLine l => exact absurd ht (Nat.lt_irrefl 0)
    | leaves => exact absurd ht (Nat.lt_irrefl 0)
    | zero => exact absurd ht (Nat.lt_irrefl 0)
  · rw [hS.nums.parts] at hy
    have e : y = ((N (up R.pts.theta)).v' + 1, 0) := by simpa using hy
    subst e
    exact key_end hW hS

#print axioms ProofFile.Honest.K3.Law.Spec.sums_bits
#print axioms ProofFile.Honest.K3.Law.Spec.sums_leaves
#print axioms ProofFile.Honest.K3.Law.Spec.bits_end
#print axioms ProofFile.Honest.K3.Law.Spec.count_ok
#print axioms ProofFile.Honest.K3.Law.Spec.key_end
#print axioms ProofFile.Honest.K3.Law.Spec.lawfulSpec
#print axioms ProofFile.Honest.K3.Law.Spec.sums_tie0
#print axioms ProofFile.Honest.K3.Law.Spec.sums_tie
#print axioms ProofFile.Honest.K3.Law.Spec.key_claimed
#print axioms ProofFile.Honest.K3.Law.Spec.sums_key
#print axioms ProofFile.Honest.K3.Law.Spec.tab_claimed
#print axioms ProofFile.Honest.K3.Law.Spec.sums_tab
#print axioms ProofFile.Honest.K3.Law.Spec.varsFit_nil
#print axioms ProofFile.Honest.K3.Law.Spec.claimed_tie0
#print axioms ProofFile.Honest.K3.Law.Spec.claimed_tie1
#print axioms ProofFile.Honest.K3.Law.Spec.claimed_tie2
#print axioms ProofFile.Honest.K3.Law.Spec.varsFit_tie
#print axioms ProofFile.Honest.K3.Law.Spec.len_tie
#print axioms ProofFile.Honest.K3.Law.Spec.byBit_toArray

end ProofFile.Honest.K3.Law.Spec
