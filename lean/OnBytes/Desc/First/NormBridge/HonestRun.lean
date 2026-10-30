--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/NormBridge/HonestRun.lean: the premises of bridge_world
(OnBytes/Desc/First/NormBridge/BridgeWorld.lean) can be met together: at data that hold there is a
run and a world that meet Shapes, Consts, Ledger, FormsZero, ReadsTrue, Clean and Good. Definitions,
statement and proof.

  floorB_not_empty. Given: a finite field of more than two elements; a reading with a lift (onto);
    data c that hold, with d <= 2^lPd and NI <= 2^lNI; any masks M; an element h with 1 - h = h; and
    any draws outside the sumchecks: the point P (lt elements), gam, the point rho (lNI elements),
    om. Then there are a run R with just these draws, whose squares' point is rho ++ (lPd times h)
    ++ P, and a world W, that meet all seven.
With OnBytes/Desc/First/NormBridge/BridgeHonest.lean (data that hold exist) the law is not empty at
any sizes with d <= 2^16, M <= 47, 1 <= eps < 2^48.

What is honest in this run, and what is only a filling. Honest: the hidden sums and products are the
true ones; both sumchecks are the honest prover's (OnBytes/Desc/First/NormBridge/HonestHeard.lean),
on the tables of OnBytes/Desc/First/NormBridge/BridgeTables.lean, with the given masks; the hidden
end values are the tables' extensions at the challenges; the slots are laid one behind the other in
the order of the rounds. Fillings: THE CALLER's FORMS ARE CONSTANT FORMS: the digits' forms D, D',
the streams' form XS, two, and the two start forms are "the true value as a constant", not sums over
entries of reads or over slots; both targets are 0.

Limits. So this theorem shows that the seven premises do not contradict each other; it does not show
that a kind's own forms meet them. The sumchecks' own draws (eps, the rounds' challenges, beta) are
chosen, round by round, outside the bad sets: that every honest run is clean is not shown here.
Not claimed: anything on soundness or hiding; that the prover's program sends what is written here.

-/
import OnBytes.Desc.First.NormBridge.BridgeWorld
import OnBytes.Desc.First.NormBridge.BridgeJoints
import OnBytes.Desc.First.NormBridge.HonestHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D6.Bridge
open Finset
open OnBytes OnBytes.Model
open Blocks (ext eqN nat ofList)
open Inst.Model.Ledger (idnP sa sb Rlo Rhi)
open OnBytes.Desc.First.P1 (Term sumTerms)
open OnBytes.Desc.First.P6 (Row dv)

variable {K : Type} [Field K]

/-! ## Lists as points -/

theorem ofList_app_right (l1 l2 : List K) (t : ℕ) :
    ofList (l1 ++ l2) (l1.length + t) = ofList l2 t := by
  unfold Blocks.ofList
  induction l1 with
  | nil => simp
  | cons a l ih =>
    rw [List.cons_append, List.length_cons, show l.length + 1 + t = (l.length + t) + 1 by omega,
      List.getD_cons_succ]
    exact ih

theorem ofList_app_left : ∀ (l1 l2 : List K) {t : ℕ}, t < l1.length →
    ofList (l1 ++ l2) t = ofList l1 t
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | a :: l, l2, t + 1, h => by
    have ih := ofList_app_left l l2 (t := t) (by simpa using h)
    unfold Blocks.ofList at ih ⊢
    rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ]
    exact ih

theorem ofList_rep (x : K) : ∀ (n i : ℕ), i < n → ofList (List.replicate n x) i = x
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | n + 1, i + 1, h => by
    have ih := ofList_rep x n i (by omega)
    unfold Blocks.ofList at ih ⊢
    rw [List.replicate_succ, List.getD_cons_succ]
    exact ih

/-! ## The slots, one behind the other -/

/-- n0 values f0; n1 values f1; twice x2; n3 values f3; once x4; n5 values f5; then f6. -/
def lay (n0 n1 n3 n5 : ℕ) (f0 f1 : ℕ → K) (x2 : K) (f3 : ℕ → K) (x4 : K) (f5 f6 : ℕ → K)
    (j : ℕ) : K :=
  if j < n0 then f0 j
  else if j < n0 + n1 then f1 (j - n0)
  else if j < n0 + n1 + 2 then x2
  else if j < n0 + n1 + 2 + n3 then f3 (j - (n0 + n1 + 2))
  else if j < n0 + n1 + 2 + n3 + 1 then x4
  else if j < n0 + n1 + 2 + n3 + 1 + n5 then f5 (j - (n0 + n1 + 2 + n3 + 1))
  else f6 (j - (n0 + n1 + 2 + n3 + 1 + n5))

section Lay
omit [Field K]
variable (n0 n1 n3 n5 : ℕ) (f0 f1 : ℕ → K) (x2 : K) (f3 : ℕ → K) (x4 : K) (f5 f6 : ℕ → K)

theorem lay0 {i : ℕ} (h : i < n0) : lay n0 n1 n3 n5 f0 f1 x2 f3 x4 f5 f6 (0 + i) = f0 i := by
  unfold lay
  rw [Nat.zero_add, if_pos h]

theorem lay1 {i : ℕ} (h : i < n1) : lay n0 n1 n3 n5 f0 f1 x2 f3 x4 f5 f6 (n0 + i) = f1 i := by
  unfold lay
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem lay2 {i : ℕ} (h : i < 2) :
    lay n0 n1 n3 n5 f0 f1 x2 f3 x4 f5 f6 (n0 + n1 + i) = x2 := by
  unfold lay
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem lay3 {i : ℕ} (h : i < n3) :
    lay n0 n1 n3 n5 f0 f1 x2 f3 x4 f5 f6 (n0 + n1 + 2 + i) = f3 i := by
  unfold lay
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left]

theorem lay4 : lay n0 n1 n3 n5 f0 f1 x2 f3 x4 f5 f6 (n0 + n1 + 2 + n3) = x4 := by
  unfold lay
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]

theorem lay5 {i : ℕ} (h : i < n5) :
    lay n0 n1 n3 n5 f0 f1 x2 f3 x4 f5 f6 (n0 + n1 + 2 + n3 + 1 + i) = f5 i := by
  unfold lay
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem lay6 (i : ℕ) :
    lay n0 n1 n3 n5 f0 f1 x2 f3 x4 f5 f6 (n0 + n1 + 2 + n3 + 1 + n5 + i) = f6 i := by
  unfold lay
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]

end Lay

/-! ## True sums and products read a point at its own coordinates alone -/

theorem trueW_congr (c : Data K) {u v : ℕ → K} (h : ∀ t < c.lt, u t = v t) :
    c.trueW u = c.trueW v := by
  funext m
  exact ext_congr_pt c.lt _ h

theorem trueP_congr (c : Data K) {u v : ℕ → K} (h : ∀ t < c.lt, u t = v t) :
    c.trueP u = c.trueP v := by
  funext m
  exact ext_congr_pt c.lt _ h

/-! ## The statement -/

/-- **THE PREMISES OF bridge_world CAN BE MET TOGETHER.** -/
theorem floorB_not_empty [Fintype K] (hK : 2 < Fintype.card K) (ρ : Reading K) (lift : K → E)
    (hlift : ∀ k, ρ.val (lift k) = k) (c : Data K) (hc : c.Holds) (lPd : ℕ) (hd : c.d ≤ 2 ^ lPd)
    (hN : c.NI ≤ 2 ^ c.lNI) (M : Masks K) (half : E) (hh : 1 - ρ.val half = ρ.val half)
    (PE : List E) (hPE : PE.length = c.lt) (gam : E) (rhoE : List E) (hrho : rhoE.length = c.lNI)
    (om : E) :
    ∃ (R : Run) (W : World K), R.PE = PE ∧ R.gam = gam ∧ R.om = om ∧
      R.zsS = rhoE ++ List.replicate lPd half ++ PE ∧
      R.Shapes ρ c lPd ∧ R.Consts ρ c lPd W ∧ R.Ledger ρ c M W ∧ R.FormsZero ρ c W ∧
      R.ReadsTrue ρ c lPd W ∧ R.Clean ρ c lPd M W ∧ R.Good ρ c W := by
  -- the points
  obtain ⟨zsS, hzs⟩ : ∃ z, z = rhoE ++ List.replicate lPd half ++ PE := ⟨_, rfl⟩
  obtain ⟨aS, haS⟩ : ∃ a : ℕ → K, a = ofList (zsS.map ρ.val) := ⟨_, rfl⟩
  obtain ⟨pk, hpk⟩ : ∃ a : ℕ → K, a = ofList (PE.map ρ.val) := ⟨_, rfl⟩
  obtain ⟨uP, huP⟩ : ∃ a : ℕ → K, a = nat (fun v : Fin c.lt => pk v) := ⟨_, rfl⟩
  have hlenS : zsS.length = c.lNI + lPd + c.lt := by
    rw [hzs, List.length_append, List.length_append, List.length_replicate, hrho, hPE]
  have hmapS : zsS.map ρ.val =
      rhoE.map ρ.val ++ List.replicate lPd (ρ.val half) ++ PE.map ρ.val := by
    rw [hzs, List.map_append, List.map_append, List.map_replicate]
  have hl12 : (rhoE.map ρ.val ++ List.replicate lPd (ρ.val half)).length = c.lNI + lPd := by
    rw [List.length_append, List.length_map, List.length_replicate, hrho]
  have hmid : ∀ t < lPd, aS (c.lNI + t) = ρ.val half := by
    intro t ht
    rw [haS, hmapS, ofList_app_left _ _ (by rw [hl12]; omega)]
    have e := ofList_app_right (rhoE.map ρ.val) (List.replicate lPd (ρ.val half)) t
    rw [List.length_map, hrho] at e
    rw [e, ofList_rep _ _ _ ht]
  have hlast : ∀ t, aS (c.lNI + lPd + t) = pk t := by
    intro t
    rw [haS, hmapS, hpk, ← hl12]
    exact ofList_app_right _ _ t
  have huPk : ∀ t < c.lt, uP t = pk t := fun t ht => by
    rw [huP]
    exact nat_apply c.lt pk ht
  -- the claims of the two sumchecks, which are true
  obtain ⟨cv, hcv⟩ : ∃ x : K, x = ρ.val half ^ lPd * ∑ i ∈ range c.NI,
      eqN c.lNI 0 aS i * ∑ s ∈ range 9, ρ.val gam ^ s * c.trueW uP (9 * i + s) := ⟨_, rfl⟩
  obtain ⟨cl, hcl⟩ : ∃ x : K, x = ∑ m ∈ range (7 * c.NI), ρ.val om ^ m * c.trueP uP m := ⟨_, rfl⟩
  have hcvT : cv = ext zsS.length
      (fun X => sumTerms [((1 : K), 0, 1)] fun _ => c.sqTab lPd (ρ.val gam) X)
      (ofList (zsS.map ρ.val)) := by
    have hsum : (fun X => sumTerms [((1 : K), 0, 1)] fun _ => c.sqTab lPd (ρ.val gam) X) =
        fun X => c.sqTab lPd (ρ.val gam) X * c.sqTab lPd (ρ.val gam) X := by
      funext X
      simp [OnBytes.Desc.First.P1.sumTerms]
    rw [hsum, hlenS, ← haS, ← joint_squares c lPd hd hN (ρ.val gam) (ρ.val half) hh aS hmid, hcv,
      trueW_congr c (u := uP) (v := fun t => aS (c.lNI + lPd + t))
        fun t ht => (huPk t ht).trans (hlast t).symm]
  have hclT : cl = ext PE.length
      (fun X => sumTerms (prTerms c.NI (ρ.val om)) fun e => c.field e X)
      (ofList (PE.map ρ.val)) := by
    rw [hPE, ← hpk, ← joint_products c pk (ρ.val om), hcl, trueP_congr c huPk]
  -- the two honest sumchecks
  obtain ⟨nS, hnS⟩ : ∃ n, n = OnBytes.Psc.hidingEntries (eqWs zsS ++ [wY]) := ⟨_, rfl⟩
  obtain ⟨nP, hnP⟩ : ∃ n, n = OnBytes.Psc.hidingEntries (eqWs PE ++ [wY]) := ⟨_, rfl⟩
  obtain ⟨S, s1, s2, s3, s4, s5, s6, s7⟩ := honest_clean ρ hK lift hlift zsS
    (fun _ => c.sqTab lPd (ρ.val gam)) M.mS [((1 : K), 0, 1)] M.hS zeroE (Aff.ofConst (lift cv))
    (9 * c.NI) cv hcvT
  obtain ⟨Pr, p1, p2, p3, p4, p5, p6, p7⟩ := honest_clean ρ hK lift hlift PE c.field M.mP
    (prTerms c.NI (ρ.val om)) M.hP zeroE (Aff.ofConst (lift cl))
    (9 * c.NI + nS + 2 + 7 * c.NI + 1) cl hclT
  obtain ⟨xS, hxS⟩ : ∃ x : K, x = ext (c.lNI + lPd + c.lt) (c.sqTab lPd (ρ.val gam))
      (ofList (S.r ρ)) := ⟨_, rfl⟩
  -- the world
  obtain ⟨sl, hsl⟩ : ∃ f : ℕ → K, f = lay (9 * c.NI) nS (7 * c.NI) nP (c.trueW uP) M.hS xS
      (c.trueP uP) cl M.hP (fun e => ext c.lt (c.field e) (ofList (Pr.r ρ))) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : World K, W = ⟨sl, fun _ _ _ => 0⟩ := ⟨_, rfl⟩
  have hWs : W.slot = sl := by rw [hW]
  have w0 : ∀ i < 9 * c.NI, W.slot (0 + i) = c.trueW uP i := fun i hi => by
    rw [hWs, hsl]
    exact lay0 _ _ _ _ _ _ _ _ _ _ _ hi
  have w1 : ∀ i < nS, W.slot (9 * c.NI + i) = M.hS i := fun i hi => by
    rw [hWs, hsl]
    exact lay1 _ _ _ _ _ _ _ _ _ _ _ hi
  have w2 : ∀ i < 2, W.slot (9 * c.NI + nS + i) = xS := fun i hi => by
    rw [hWs, hsl]
    exact lay2 _ _ _ _ _ _ _ _ _ _ _ hi
  have w3 : ∀ i < 7 * c.NI, W.slot (9 * c.NI + nS + 2 + i) = c.trueP uP i := fun i hi => by
    rw [hWs, hsl]
    exact lay3 _ _ _ _ _ _ _ _ _ _ _ hi
  have w4 : W.slot (9 * c.NI + nS + 2 + 7 * c.NI) = cl := by
    rw [hWs, hsl]
    exact lay4 _ _ _ _ _ _ _ _ _ _ _
  have w5 : ∀ i < nP, W.slot (9 * c.NI + nS + 2 + 7 * c.NI + 1 + i) = M.hP i := fun i hi => by
    rw [hWs, hsl]
    exact lay5 _ _ _ _ _ _ _ _ _ _ _ hi
  have w6 : ∀ i, W.slot (9 * c.NI + nS + 2 + 7 * c.NI + 1 + nP + i) =
      ext c.lt (c.field i) (ofList (Pr.r ρ)) := fun i => by
    rw [hWs, hsl]
    exact lay6 _ _ _ _ _ _ _ _ _ _ _ i
  -- the run
  obtain ⟨R, hR⟩ : ∃ R : Run, R =
      { PE := PE, sW := 0, gam := gam, zsS := zsS, half := half, S := S
        sL := 9 * c.NI + nS
        shS := fun e => lift (xS + S.beta ρ * M.mS e)
        XS := Aff.ofConst (lift xS)
        sPv := 9 * c.NI + nS + 2, om := om, sCl := 9 * c.NI + nS + 2 + 7 * c.NI, Pr := Pr
        sE := 9 * c.NI + nS + 2 + 7 * c.NI + 1 + nP
        shP := fun e => lift (ext c.lt (c.field e) (ofList (Pr.r ρ)) + Pr.beta ρ * M.mP e)
        D := fun i n => Aff.ofConst (lift (c.digAt uP i n))
        D' := fun i n => Aff.ofConst (lift (c.digAt (ofList (Pr.r ρ)) i n))
        eps := fun i => lift (((c.np i).eps : ℤ) : K)
        two := fun i => Aff.ofConst (lift (2 ^ ((c.np i).M + 1))) } := ⟨_, rfl⟩
  have rP : nat (R.P ρ c) = uP := by
    rw [huP, hpk, hR]
    rfl
  have raS : R.aS ρ = aS := by
    rw [haS, hR]
    rfl
  have rpk : R.pk ρ = pk := by
    rw [hpk, hR]
    rfl
  have rWt : ∀ j < 9 * c.NI, R.Wt W j = c.trueW uP j := fun j hj => by
    rw [← w0 j hj, hR]
    rfl
  have rPt : ∀ m < 7 * c.NI, R.Pt W m = c.trueP uP m := fun m hm => by
    rw [← w3 m hm, hR]
    rfl
  have rcv : R.cvS ρ c lPd W = cv := by
    unfold Run.cvS
    rw [raS, hcv]
    have e1 : R.half = half := by rw [hR]
    have e2 : R.gam = gam := by rw [hR]
    rw [e1, e2]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    congr 1
    refine sum_congr rfl fun s hs => ?_
    rw [rWt (9 * i + s) (by
      have := mem_range.mp hi
      have := mem_range.mp hs
      omega)]
  have vC : ∀ (x : K) (V : World K), (Aff.ofConst (lift x)).value ρ V = x := fun x V => by
    rw [Aff.value_ofConst, hlift]
  -- misses are 0
  have dW0 : ∀ i < c.NI, ∀ s < 9, c.dW uP (R.Wt W) i s = 0 := by
    intro i hi s hs
    unfold Data.dW
    rw [rWt (9 * i + s) (by omega)]
    exact dW_true c uP i s hs
  have dP0 : ∀ m < 7 * c.NI, c.dP uP (R.Pt W) m = 0 := by
    intro m hm
    unfold Data.dP
    rw [rPt m hm]
    exact dP_true c uP m
  have hLines : c.Lines uP (R.Wt W) (R.Pt W) :=
    (lines_iff_of_true c uP _ _ dW0 dP0).mpr fun i hi k hk =>
      Blocks.ext_zero_of_forall (fun t ht => hc i hi k hk t ht) uP
  have hz : ∀ i < c.NI, ∀ k, idnP (c.np i) (dv ρ W fun s => Aff.slot (R.sW + (9 * i + s)))
      (dv ρ W (R.D i)) (dv ρ W fun n => Aff.slot (R.sPv + (7 * i + n))) k = 0 := by
    intro i hi k
    have eD : dv ρ W (R.D i) = c.digAt uP i := by
      funext n
      rw [hR]
      exact vC _ W
    have eW : (dv ρ W fun s => Aff.slot (R.sW + (9 * i + s))) = fun s => R.Wt W (9 * i + s) :=
      funext fun s => Aff.value_slot ρ W _
    have eP : (dv ρ W fun n => Aff.slot (R.sPv + (7 * i + n))) = fun n => R.Pt W (7 * i + n) :=
      funext fun n => Aff.value_slot ρ W _
    rw [eD, eW, eP]
    by_cases hk : k < 17
    · exact hLines i hi k hk
    · exact Inst.Model.Ledger.idnP_of_le _ _ _ _ (by omega)
  have hforms := fun i (hi : i < c.NI) =>
    forms_of_idnP ρ W (R.D i) (fun s => Aff.slot (R.sW + (9 * i + s)))
      (fun n => Aff.slot (R.sPv + (7 * i + n))) (c.np i) (R.eps i) (R.two i)
      (by rw [hR]; exact hlift _) (by rw [hR]; exact vC _ W) (hz i hi)
  refine ⟨R, W, by rw [hR], by rw [hR], by rw [hR], by rw [hR, hzs], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Shapes
    refine ⟨by rw [hR]; exact hPE, by rw [hR]; exact hlenS, ?_, ?_, by rw [hR]; exact s1,
      by rw [hR]; exact p1⟩
    · intro t ht
      rw [raS, hmid t ht, hR]
    · intro t _
      rw [raS, rpk, hlast t]
  · -- Consts
    refine ⟨by rw [hR]; exact hh, fun i _ => by rw [hR]; exact hlift _,
      fun i _ => by rw [hR]; exact vC _ W, ?_, ?_, ?_, ?_⟩
    · rw [rcv, hR]
      show S.p.start.value ρ W = cv
      rw [s2, vC]
    · rw [hR]
      show Pr.p.start.value ρ W = W.slot (9 * c.NI + nS + 2 + 7 * c.NI)
      rw [p2, vC, w4]
    · rw [hR]
      show ρ.val S.S0 = ρ.val (lift (xS + S.beta ρ * M.mS 0)) *
        ρ.val (lift (xS + S.beta ρ * M.mS 1))
      rw [s5, hlift, hlift, hlenS, ← hxS]
      simp [OnBytes.Desc.First.P1.sumTerms]
    · rw [hR]
      show ρ.val Pr.S0 = sumTerms (prTerms c.NI (ρ.val om)) fun e =>
        ρ.val (lift (ext c.lt (c.field e) (ofList (Pr.r ρ)) + Pr.beta ρ * M.mP e))
      rw [p5, hPE]
      congr 1
      funext e
      rw [hlift]
  · -- Ledger
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [hR] at hi ⊢
      show W.slot (S.p.first + i) = M.hS i
      rw [s4]
      exact w1 i (by rw [hnS]; exact hi)
    · intro i hi
      rw [hR] at hi ⊢
      show W.slot (Pr.p.first + i) = M.hP i
      rw [p4]
      exact w5 i (by rw [hnP]; exact hi)
    · intro e he
      rw [hR]
      show ρ.val (lift (xS + S.beta ρ * M.mS e)) = W.slot (9 * c.NI + nS + e) + S.beta ρ * M.mS e
      rw [hlift, w2 e he]
    · intro e _
      rw [hR]
      show ρ.val (lift (ext c.lt (c.field e) (ofList (Pr.r ρ)) + Pr.beta ρ * M.mP e)) =
        W.slot (9 * c.NI + nS + 2 + 7 * c.NI + 1 + nP + e) + Pr.beta ρ * M.mP e
      rw [hlift, w6 e]
  · -- FormsZero
    have eD' : ∀ i, dv ρ W (R.D' i) = c.digAt (ofList (Pr.r ρ)) i := fun i => by
      funext n
      rw [hR]
      exact vC _ W
    have eSE : R.sE = 9 * c.NI + nS + 2 + 7 * c.NI + 1 + nP := by rw [hR]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hR]
      exact s7 W (vC _ W) fun i hi => w1 i (by rw [hnS]; exact hi)
    · rw [hR]
      show (Aff.slot (9 * c.NI + nS) - Aff.slot (9 * c.NI + nS + 1)).value ρ W = 0
      have a0 := w2 0 (by omega)
      rw [Nat.add_zero] at a0
      rw [Aff.value_sub, Aff.value_slot, Aff.value_slot, a0, w2 1 (by omega), sub_self]
    · rw [hR]
      show (Aff.slot (9 * c.NI + nS) - Aff.ofConst (lift xS)).value ρ W = 0
      have a0 := w2 0 (by omega)
      rw [Nat.add_zero] at a0
      rw [Aff.value_sub, Aff.value_slot, a0, vC, sub_self]
    · have e1 : R.sCl = 9 * c.NI + nS + 2 + 7 * c.NI := by rw [hR]
      have e2 : R.om = om := by rw [hR]
      rw [e1, e2, w4, hcl, sub_eq_zero]
      exact sum_congr rfl fun m hm => by rw [rPt m (mem_range.mp hm)]
    · rw [hR]
      exact p7 W (vC _ W) fun i hi => w5 i (by rw [hnP]; exact hi)
    · intro i _
      rw [Aff.value_sub, Aff.value_slot, OnBytes.Desc.First.P6.a_value ρ W, eD', eSE, w6,
        c.ext_field0, sub_self]
    · intro i _
      rw [Aff.value_sub, Aff.value_slot, OnBytes.Desc.First.P6.b_value ρ W, eD', eSE, w6,
        c.ext_field1, sub_self]
    · intro i _
      rw [Aff.value_sub, Aff.value_slot, OnBytes.Desc.First.P6.Rlo_value ρ W, eD', eSE, w6,
        c.ext_field2, sub_self]
    · intro i _
      rw [Aff.value_sub, Aff.value_slot, OnBytes.Desc.First.P6.Rhi_value ρ W, eD', eSE, w6,
        c.ext_field3, sub_self]
    · exact fun i hi => (hforms i hi).1
    · exact fun i hi => (hforms i hi).2
  · -- ReadsTrue
    refine
      ⟨fun i _ n _ => by rw [rP, hR]; exact vC _ W, ?_, fun i _ n _ => by rw [hR]; exact vC _ W⟩
    rw [hR]
    show (Aff.ofConst (lift xS)).value ρ W = _
    rw [vC, hxS]
    rfl
  · -- Clean
    refine ⟨?_, ?_⟩
    · rw [rcv, hR]
      show S.Clean ρ zsS (fun _ => c.sqTab lPd (ρ.val gam)) M.mS [(1, 0, 1)] M.hS
        (ρ.val S.p.target) cv
      rw [s3]
      exact s6
    · rw [hR]
      show Pr.Clean ρ PE c.field M.mP (prTerms c.NI (ρ.val om)) M.hP (ρ.val Pr.p.target)
        (W.slot (9 * c.NI + nS + 2 + 7 * c.NI))
      rw [p3, w4]
      exact p6
  · -- Good
    refine ⟨fun hb => hb.1 hc, ?_, ?_, ?_⟩
    · rw [rP]
      intro hb
      obtain ⟨i, hi, s, hs, hne⟩ := hb.1
      exact hne (dW0 i hi s hs)
    · rw [rP]
      intro hb
      obtain ⟨i, hi, hne⟩ := hb.1
      apply hne
      unfold Data.dWg
      exact sum_eq_zero fun s hs => by rw [dW0 i hi s (mem_range.mp hs), mul_zero]
    · rw [rP]
      intro hb
      obtain ⟨m, hm, hne⟩ := hb.1
      exact hne (dP0 m hm)

end D6.Bridge

#print axioms D6.Bridge.floorB_not_empty
