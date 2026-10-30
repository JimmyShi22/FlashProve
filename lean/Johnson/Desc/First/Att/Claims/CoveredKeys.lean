-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/CoveredKeys.lean: kind K5: the key forms that "first" hands on, and so
those that "keys" returns, name no entry of the array of tables outside the tables' part.
Johnson/Desc/First/Att/Claims/Covered.lean leaves them out. Each is made of slots and constants:
keyKR, padTerm, keyKFD, remForm, indexForm, keyWL, keyIX, keyWH, joinR16.

Main names:
  `cov_keyKR` … `cov_keyWH`. `CovJ iU3 K nW j`: every key form of the record meets Cov.
    `covJ_empty`, `covJ_set`, `covJ_joinR16`; `cvk_claim3`, `cvk_claim4`, `cvk_claim5`.
  `keys_covered_K05`, `keysRun_covered`.
Premises: LenIn and RowsCov, as in Johnson/Desc/First/Att/Claims/Covered.lean: the way through the
claims gathers forms.
Used of OnBytes: the plain records Aff and Ent and the pure functions on them
(OnBytes/Model/Hide.lean). No routine in a context and no theorem on a run.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Covered

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P.Runs (W JoinsP)

variable {K iU3 nW : ℕ}

local macro "covs" : tactic => `(tactic| repeat (first
  | with_reducible exact cov_slot _ | with_reducible exact cov_ofConst _ | with_reducible assumption
  | with_reducible refine cov_add ?_ ?_ | with_reducible refine cov_sub ?_ ?_
  | with_reducible refine cov_scale ?_ _ | with_reducible refine cov_addMul ?_ ?_ _))

theorem cov_keyKR (pc : P.RemP) : Cov iU3 K nW (P.Runs.keyKR pc) := by
  unfold P.Runs.keyKR; dsimp only; covs
theorem cov_padTerm (c : P.CallG) (zk : Array E) : Cov iU3 K nW (P.Runs.padTerm c zk) := by
  unfold P.Runs.padTerm; covs
theorem cov_keyKFD (gC gOm : ℕ) (k : P.ScoreP) : Cov iU3 K nW (P.Runs.keyKFD gC gOm k) := by
  unfold P.Runs.keyKFD; dsimp only; covs
theorem cov_remForm (d : P.DivP) : Cov iU3 K nW (P.Runs.remForm d) := by
  unfold P.Runs.remForm; covs
theorem cov_indexForm (d : P.DivP) (lt : ℕ) : Cov iU3 K nW (P.Runs.indexForm d lt) := by
  unfold P.Runs.indexForm
  have key : ∀ (l : List ℕ) (s : Aff), Cov iU3 K nW s → Cov iU3 K nW
      (l.foldl (fun s k => Aff.addMul s (Aff.slot (d.sIB + k)) (P.ofNat (2 ^ k))) s) := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons k l ih => intro s hs; exact ih _ (cov_addMul hs (cov_slot _) _)
  exact key _ _ (cov_ofConst _)
theorem cov_keyWL (d : P.DivP) : Cov iU3 K nW (P.Runs.keyWL d) := by
  have := cov_remForm (iU3 := iU3) (K := K) (nW := nW) d
  unfold P.Runs.keyWL; dsimp only; covs
theorem cov_keyIX (S : P.Geo) (d : P.DivP) : Cov iU3 K nW (P.Runs.keyIX S d) := by
  have := cov_indexForm (iU3 := iU3) (K := K) (nW := nW) d S.lt
  unfold P.Runs.keyIX; covs
theorem cov_keyWH (d : P.DivP) : Cov iU3 K nW (P.Runs.keyWH d) := by
  unfold P.Runs.keyWH; dsimp only; covs

/-- Every key form of the record names no entry outside the part. -/
def CovJ (iU3 K nW : ℕ) (j : JoinsP) : Prop := ∀ f ∈ j.kf.toList, Cov iU3 K nW f

theorem covJ_empty (n : ℕ) : CovJ iU3 K nW (JoinsP.empty n) := by
  intro f hf
  unfold JoinsP.empty at hf
  simp only [Array.toList_replicate, List.mem_replicate] at hf
  rw [hf.2]
  exact cov_ofConst _

theorem covJ_set {j : JoinsP} (hj : CovJ iU3 K nW j) (q : ℕ) {v : Aff} (hv : Cov iU3 K nW v) :
    CovJ iU3 K nW (j.set q v) := by
  intro f hf
  unfold JoinsP.set at hf
  simp only [Array.toList_setIfInBounds] at hf
  rcases List.mem_or_eq_of_mem_set hf with h | rfl
  · exact hj f h
  · exact hv

theorem covJ_joinR16 (S : P.Geo) (d : P.DivP) {j : JoinsP} (hj : CovJ iU3 K nW j) :
    CovJ iU3 K nW (P.Runs.joinR16 S d j) := by
  unfold P.Runs.joinR16
  dsimp only
  have key : ∀ (l : List (P.CallG × ℕ)) (j : JoinsP), CovJ iU3 K nW j → CovJ iU3 K nW
      (l.foldl (fun j x => if x.1.tab == .r16 then
        j.set x.2 (if x.1.holds .ix then (if x.1.holds .wl then Aff.ofConst zeroE + P.Runs.keyWL d
          else Aff.ofConst zeroE) + P.Runs.keyIX S d
          else (if x.1.holds .wl then Aff.ofConst zeroE + P.Runs.keyWL d else Aff.ofConst zeroE))
        else j) j) := by
    intro l
    induction l with
    | nil => intro j hj; exact hj
    | cons x l ih =>
      intro j hj
      refine ih _ ?_
      dsimp only
      split
      · refine covJ_set hj _ ?_
        have a : Cov iU3 K nW (if x.1.holds .wl then Aff.ofConst zeroE + P.Runs.keyWL d
            else Aff.ofConst zeroE) := by
          split
          · exact cov_add (cov_ofConst _) (cov_keyWL d)
          · exact cov_ofConst _
        split
        · exact cov_add a (cov_keyIX S d)
        · exact a
      · exact hj
  exact key _ j hj

variable {i : P.Runs.In}

local notation "CC" => Cov i.iU3 K nW
local notation "CJ" => CovJ i.iU3 K nW

theorem cvk_callKR (hL : LenIn i nW) (q : ℕ) : CV K CC CC (P.Runs.callKR i q) := by
  unfold P.Runs.callKR
  rw [← Array.foldlM_toList]
  exact CV.foldlM (fun v pc hv => CV.ite (CV.bind (cv_linPlanes hL pc) fun _ _ =>
    CV.pure (cov_add hv (cov_keyKR pc))) (CV.pure hv)) _ _ (cov_ofConst _)

theorem cvk_claim3 (hL : LenIn i nW) {j : JoinsP} (hj : CJ j) : CV K CC CJ (P.Runs.claim3 i j) := by
  unfold P.Runs.claim3
  exact CV.foldlM (fun j x hj => CV.ite (CV.bind (cvk_callKR hL x.2) fun v hv =>
    CV.pure (covJ_set hj _ hv)) (CV.pure hj)) _ _ hj

theorem cvk_callKFD (hL : LenIn i nW) (hR : RowsCov i K nW) (q : ℕ) (c : P.CallG) :
    CV K CC CC (P.Runs.callKFD i q c) := by
  unfold P.Runs.callKFD
  refine CV.foldlM_mem _ _ (fun v x hx hv => CV.ite (CV.bind (cv_unitKFD hL x.2 x.1 (hR.units x.1 ?_))
    fun _ _ => CV.pure (cov_add hv (cov_keyKFD _ _ _))) (CV.pure hv)) (cov_padTerm _ _)
  exact (List.mem_zipIdx hx).2.2 ▸ List.getElem_mem _

theorem cvk_claim4 (hL : LenIn i nW) (hR : RowsCov i K nW) {j : JoinsP} (hj : CJ j) :
    CV K CC CJ (P.Runs.claim4 i j) := by
  unfold P.Runs.claim4
  exact CV.foldlM (fun j x hj => CV.ite (CV.bind (cvk_callKFD hL hR x.2 x.1) fun v hv =>
    CV.pure (covJ_set hj _ hv)) (CV.pure hj)) _ _ hj

theorem cvk_claim5 (hL : LenIn i nW) (hR : RowsCov i K nW) {j : JoinsP} (hj : CJ j) :
    CV K CC CJ (P.Runs.claim5 i j) := by
  unfold P.Runs.claim5
  dsimp only
  refine CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readDenominator hL _ _ _ _) fun zc hzc => ?_
  refine CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readHead hL _ _ _ _ _ _) fun rh hrh => ?_
  refine CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readHead hL _ _ _ _ _ _) fun rhp hrhp => ?_
  refine CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readHead hL _ _ _ _ _ _) fun r2 hr2 => ?_
  refine CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readHead hL _ _ _ _ _ _) fun r2p hr2p => ?_
  refine CV.bind (CV.lin hzc) fun _ _ => CV.bind (CV.lin hrh) fun _ _ => CV.bind (CV.lin hrhp) fun _ _ => ?_
  refine CV.bind (CV.forIn (fun k => ?_) _) fun _ _ => ?_
  · exact CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readIndexBit hL _ _ _ _ _) fun f hf =>
      CV.bind (CV.lin hf) fun _ _ => CV.pure trivial
  refine CV.bind (CV.lin hr2) fun _ _ => CV.bind (CV.lin hr2p) fun _ _ =>
    CV.bind (CV.lin (f := P.Runs.leftOf i.p.d.scE.row) hR.scE) fun _ _ => ?_
  refine CV.bind (CV.forIn (fun b => ?_) _) fun _ _ =>
    CV.pure (covJ_set (covJ_joinR16 _ _ hj) _ (cov_keyWH _))
  exact CV.bind (cv_endValuesE hL b _) fun _ _ => CV.pure trivial

/-- **The key forms that "first" hands on, and so those that "keys" returns, name no entry outside the part.** -/
theorem keys_covered_K05 {l₁ : List Aff} {j : JoinsP} (hL : LenIn i nW) (hR : RowsCov i K nW)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) : CovJ i.iU3 K nW j := by
  unfold P.Runs.firstRun P.Runs.gather at h1
  simp only [Option.map_eq_some_iff] at h1
  obtain ⟨_, ⟨y1, hy1, rfl⟩, e1⟩ := h1
  have c1 := (CV.bind (C := Cov i.iU3 K nW) (cvk_claim3 hL (covJ_empty _)) fun j3 h3 =>
    CV.bind (cvk_claim4 hL hR h3) fun j4 h4 => cvk_claim5 hL hR h4) #[] y1 hy1 (by simp)
  rw [← (Prod.mk.inj e1).2]
  exact c1.1

theorem keysRun_covered {l₁ : List Aff} {j : JoinsP} {k3 : P.Runs.PadIn} {kf : Array Aff}
    (hL : LenIn i nW) (hR : RowsCov i K nW) (h1 : P.Runs.firstRun i K = some (l₁, j))
    (hk : P.Runs.keysRun i k3 j = some kf) : ∀ f ∈ kf.toList, Cov i.iU3 K nW f := by
  rw [keys_is _ _ _ _ hk]
  exact keys_covered_K05 hL hR h1

end K5Law
