-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/PlanRow.lean: THE MEMBER OF THE LAW "the pending row can be made of what K4's
hearing leaves" (Johnson/Road/K4/Total/RowReturns.lean), MADE BY CODE OFF THE PLAN: so that the
law's premise "wsPending returns at a leaving of this skeleton" becomes ONE PUBLIC TEST WITH CODE.
Statements and proofs; the definitions: Johnson/Road/K4/Total/PlanRowDefs.lean.

THE THOUGHT. The routine's return hangs on the leavings' skeleton alone (pend_skel,
Johnson/Road/K4/Total/RowProofs.lean): the length of the merge's point; how many claims' rests there
are; for each rest its unit's number and its factors' sizes. Behind a return of the hearing the
point has the layout's column bits; the units' numbers, in order, are a function of the layout, the
calls of the second token sumcheck, the group and the layout of the weights; the sizes are pinned by
the merge's own test to the unit's groups (shape_pin, Johnson/Road/K4/Total/HearRowSkel.lean). So a
leaving of that skeleton can be written down with 0 for every element.

A SECOND TEXT, HELD AGAINST THE FIRST. unitsA, unitsT, unitsW list the units' numbers as claimsA,
claimsT, weightClaims (OnBytes/Model/LayerPanels.lean) list the claims: the same kinds X and layers
lam, without the factors. unitsA_of, unitsT_of, unitsW_of: WHERE THE FIRST TEXT RETURNS, THE SECOND
RETURNS ITS CLAIMS' UNITS, IN ORDER.

  `zeroFac`, `zeroClaim`: a factor of the sizes that a group asks, and a claim on a unit, at zeros;
    `zeroFac_fits`, `zeroClaim_shape`: they pass the merge's test.
  `unitsA`, `unitsT`, `unitsW`, `planEnv`, `unitsOf P g`: the units' numbers off the plan.
  `planWoOf`, `planWo P g`: the leaving.
  `rowB P g n lin`: **THE TEST**: wsPending returns at that leaving.
  `units_of_merge`: the list that a hearing hands to the merge names just unitsOf's units.
  `rowSkel_plan`: behind a return of the hearing planWo is there, and the merge's leavings have its
    skeleton.
  `rowB_tokv`: the test does not read the tokens.
  **`row_returns_of_plan`**, `rowB_of_return` (THE CONVERSE, behind a hearing's return at the same P
    and g: the test asks no more than the truth; where no hearing returns it says nothing).
New: the second text and its tie; the leaving by code.
**Limits.** rowB IS A PREMISE: NOTHING HERE SAYS THAT IT IS TRUE AT ANY PLAN. NO RUN OF IT IS CITED
HERE. AN EVALUATION OUTSIDE THE KERNEL IS A RUN, NO THEOREM. P is the public parameters at which the
hearing ran; the test does not read the tokens (rowB_tokv). ONE YES IS OWED FOR EACH LAYERS' PLACE
(P, g). That P.wsLay, n and lin are the layout, the number of claims and the shape at which the
frame's reader is asked is not said. It says that wsPending returns, not what the row says; the
ledger's entry (roomB) stays a premise of the law. Nothing on soundness. K04_law, the law of K4's
block itself, IS NOT PROVED. Met through Lean at no member.


-/
import Johnson.Road.K4.Total.PlanRowDefs
import Johnson.Road.K4.Total.RowProofs
import Johnson.Road.K4.Total.HearRowSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Env ClaimEnv isAcc callsTS callsAC)
open OnBytes.Params (LinShape)
open OnBytes.Flat (All2 RecSizes ClaimAlike)
open Johnson.Desc.First.ForkMerge (facFits claimFits)
open VerifiableInference.Desc.First.MergeLaw (facFits_iff claimFits_iff claimFits_eq hear_of_flat
  mergeHear_inv)
open OnBytes.Desc.First.P1 (powers_size)

/-! ## A claim at zeros -/

theorem zeroFac_fits (G : WsGrp) : facFits (zeroFac G) G = true := by
  refine (facFits_iff _ G).2 ?_
  unfold zeroFac
  by_cases h : G.cls = 'E'
  · refine Or.inl ⟨h, ?_⟩
    rw [if_pos (by rw [h]; rfl)]
    exact ⟨Array.size_replicate, Array.size_replicate, rfl⟩
  · refine Or.inr ⟨h, ?_⟩
    rw [if_neg (by simpa using h)]
    exact ⟨Array.size_replicate, rfl, rfl⟩

theorem zeroClaim_shape {lay : WsLay} {ui : Nat} {u : WsUnit} (h : lay.U[ui]? = some u) :
    (wsClaimShape lay (zeroClaim lay ui)).isOk = true := by
  rw [← claimFits_eq]
  refine (claimFits_iff lay _).2 ⟨u, h, ?_, ?_⟩
  · show ((((lay.U[ui]?).map (·.g)).getD []).map zeroFac).length = u.g.length
    rw [h]
    exact List.length_map _
  · show ∀ y ∈ ((((lay.U[ui]?).map (·.g)).getD []).map zeroFac).zip u.g, facFits y.1 y.2 = true
    rw [h]
    show ∀ y ∈ (u.g.map zeroFac).zip u.g, facFits y.1 y.2 = true
    generalize u.g = gs
    induction gs with
    | nil => exact fun _ hy => nomatch hy
    | cons G gs ih =>
      intro y hy
      rw [List.map_cons, List.zip_cons_cons] at hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact zeroFac_fits G
      · exact ih y hy

/-! ## The units' numbers: the second text -/

theorem mapM_map {α β γ : Type} {f : α → Option β} {f' : α → Option γ} {φ : β → γ}
    (h : ∀ a b, f a = some b → f' a = some (φ b)) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → l.mapM f' = some (r.map φ)
  | [], r, h1 => by
    rw [List.mapM_nil] at h1
    obtain rfl := Option.some.inj h1
    rfl
  | a :: l, r, h1 => by
    rw [List.mapM_cons] at h1
    obtain ⟨b, hb, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨bs, hbs, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain rfl := Option.some.inj h1
    rw [List.mapM_cons, h a b hb, mapM_map h l bs hbs]
    rfl

variable {c c₀ : ClaimEnv}

theorem unitsA_of {sn : String} {l : List WsClaim} (h : c.claimsA sn = some l) :
    unitsA c sn = some (l.map (·.ui)) := by
  unfold ClaimEnv.claimsA at h
  unfold unitsA
  dsimp only at h ⊢
  by_cases ha : (!isAcc sn) = true
  · rw [if_pos ha] at h ⊢
    obtain rfl := Option.some.inj h
    rfl
  · rw [if_neg ha] at h ⊢
    exact mapM_map (fun _ _ hb => claim_ui hb) _ _ h

theorem unitsT_of {sn : String} {l : List WsClaim} (h : c.claimsT sn = some l) :
    unitsT c sn = some (l.map (·.ui)) := by
  unfold ClaimEnv.claimsT at h
  unfold unitsT
  dsimp only at h ⊢
  by_cases h1 : (sn == "QK") = true
  · rw [if_pos h1] at h ⊢
    obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
    exact mapM_map (fun _ _ hb => claim_ui hb) _ _ h
  · rw [if_neg h1] at h ⊢
    by_cases h2 : (c.v.y.h.p3 && (sn == "G" || sn == "U" || sn == "D")) = true
    · rw [if_pos h2] at h ⊢
      exact mapM_map (fun _ _ hb => claim_ui hb) _ _ h
    · rw [if_neg h2] at h ⊢
      obtain rfl := Option.some.inj h
      rfl

theorem unitsW_of {TS : List Nat} {l : List WsClaim} (h : c.weightClaims TS = some l) :
    unitsW c TS = some (l.map (·.ui)) := by
  unfold ClaimEnv.weightClaims at h
  unfold unitsW
  dsimp only at h ⊢
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := Option.some.inj h
  rw [mapM_map (φ := List.map (·.ui)) (fun _ _ hb => unitsA_of hb) _ _ ha,
    mapM_map (φ := List.map (·.ui)) (fun _ _ hb => unitsT_of hb) _ _ ht]
  show some ((a.map (List.map (·.ui))).flatten ++ (t.map (List.map (·.ui))).flatten) = _
  rw [List.map_append, List.map_flatten, List.map_flatten]

/-- The second text reads the layout, the group and the layout of the weights alone, beside its own
argument TS. -/
theorem unitsW_pub (E : EnvPub c c₀) (TS : List Nat) : unitsW c TS = unitsW c₀ TS := by
  have hm : ∀ lam, c.v.isMoe lam = c₀.v.isMoe lam := fun lam => by
    unfold Env.isMoe
    rw [E.y]
  have hl : ∀ lam, c.v.lay lam = c₀.v.lay lam := fun lam => by
    unfold Env.lay
    rw [E.y, E.g]
  have eA : unitsA c = unitsA c₀ := by
    funext sn
    unfold unitsA
    dsimp only
    rw [E.y, E.lay]
    simp only [hm, hl]
  have eT : unitsT c = unitsT c₀ := by
    funext sn
    unfold unitsT
    dsimp only
    rw [E.y, E.lay]
    simp only [hl]
  unfold unitsW
  dsimp only
  rw [E.y, eA, eT]

theorem units_of_merge {P : Pub} {g : Nat} {o : Own} (ey : o.v.y = P.y) (eg : o.v.g = g)
    {cl : Array WsClaim} (h : mergeClaims P g o = some cl) :
    unitsOf P g = some (cl.toList.map (·.ui)) := by
  have E : EnvPub (envOf P o) (planEnv P g) := ⟨ey, eg, rfl⟩
  unfold mergeClaims at h
  obtain ⟨TS, hTS, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨cp, hcp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ce, hce, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold unitsOf
  rw [hTS, Option.bind_some, ← unitsW_pub E TS, unitsW_of hcp, Option.bind_some,
    List.toList_toArray, List.map_append]
  by_cases hg : (g == 0) = true
  · rw [if_pos hg] at hce ⊢
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hce
    have e1 := claimE_ui hx
    have e2 : P.wsLay.unitOf 12 P.y.h.L = some x.ui := by
      rw [← ey]
      exact e1
    rw [e2]
    rfl
  · rw [if_neg hg] at hce ⊢
    obtain rfl := Option.some.inj hce
    rfl

/-! ## The leaving, and the test -/

/-- The test does not read the tokens. -/
theorem rowB_tokv (P : Pub) (x : Array Nat) (g n : Nat) (lin : LinShape) :
    rowB { P with tokv := x } g n lin = rowB P g n lin := rfl

/-- The rests of claims that pass the merge's test, against the rests of the claims at zeros on
their units. -/
theorem rests_plan (lay : WsLay) (f : WsClaim × E → E) :
    ∀ (l : List WsClaim) (r : List E), l.length = r.length →
      (∀ x ∈ l, (wsClaimShape lay x).isOk = true) →
      All2 RecSizes ((l.zip r).map fun y => wsRowPart lay y.1 (f y))
        ((l.map (·.ui)).map fun ui => wsRowPart lay (zeroClaim lay ui) zeroE)
  | [], _, _, _ => by
    rw [List.zip_nil_left]
    exact .nil
  | _ :: _, [], h, _ => by simp at h
  | x :: l, k :: r, h, hs => by
    rw [List.zip_cons_cons, List.map_cons, List.map_cons, List.map_cons]
    have hx := hs x List.mem_cons_self
    have hx' := hx
    rw [← claimFits_eq] at hx'
    obtain ⟨u, hu, _⟩ := (claimFits_iff lay x).1 hx'
    exact .cons (rowPart_sizes lay
        (shape_pin lay (c := x) (c' := zeroClaim lay x.ui) rfl hx (zeroClaim_shape hu)) _ _)
      (rests_plan lay f l r (by simpa using h) fun y hy => hs y (List.mem_cons_of_mem _ hy))

variable {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}

/-- Behind a return of the hearing the plan's leaving is there, and the merge's leavings have its
skeleton. -/
theorem rowSkel_plan (h : hear engFl P hp g fo F t = some (o, G, u)) :
    ∃ w₀, planWo P g = some w₀ ∧ RowSkel o.wo w₀ := by
  obtain ⟨_, ey, _, eg, _, _, cl, _, _, _, _, G5, _, _, _, _, u5, _, _, _, _, _, _, hc, hs, hE⟩ :=
    hear_parts h
  have hU := units_of_merge ey eg hc
  have sh := merge_shapes hE
  obtain ⟨x, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr, _⟩ :=
    mergeHear_inv (hear_of_flat hE)
  obtain ⟨h0, _, _⟩ := OnBytes.Road.K4.merge_sizes hE
  have hsz : (mergeSlots hp g o).size = cl.size := by
    by_cases hg : (g == 0) = true
    · have e : (mergeSlots hp g o).size = hp.NCL - 1 + 1 := by simp [mergeSlots, hg]
      omega
    · have e : (mergeSlots hp g o).size = hp.NCL := by simp [mergeSlots, hg]
      omega
  refine ⟨planWoOf P.wsLay (cl.toList.map (·.ui)), by unfold planWo; rw [hU]; rfl, ?_, ?_⟩
  · rw [(OnBytes.Road.K4.wo_sizes h).2.2]
    show _ = (Array.replicate P.wsLay.lk zeroE).size
    rw [Array.size_replicate]
  · have hl : cl.toList.length = (Model.powers x (mergeSlots hp g o).size).toList.length := by
      rw [Array.length_toList, Array.length_toList, powers_size, hsz]
    rw [hr, Array.toList_zip]
    exact rests_plan P.wsLay _ _ _ hl sh

/-- **A return of the hearing and a yes of the test: the routine wsPending returns at the merge's
leavings.** -/
theorem row_returns_of_plan (h : hear engFl P hp g fo F t = some (o, G, u)) {n : Nat}
    {lin : LinShape} (hB : rowB P g n lin = true) :
    (wsPending P.wsLay o.wo n lin).toOption.isSome = true := by
  obtain ⟨w₀, e, S⟩ := rowSkel_plan h
  unfold rowB at hB
  rw [e] at hB
  exact (pend_skel P.wsLay n lin o.wo w₀ S).trans hB

/-- **The converse: the test asks no more than the truth.** -/
theorem rowB_of_return (h : hear engFl P hp g fo F t = some (o, G, u)) {n : Nat} {lin : LinShape}
    (hr : (wsPending P.wsLay o.wo n lin).toOption.isSome = true) : rowB P g n lin = true := by
  obtain ⟨w₀, e, S⟩ := rowSkel_plan h
  unfold rowB
  rw [e]
  exact (pend_skel P.wsLay n lin o.wo w₀ S).symm.trans hr

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.zeroFac_fits
#print axioms OnBytes.Desc.First.K4.Total.zeroClaim_shape
#print axioms OnBytes.Desc.First.K4.Total.mapM_map
#print axioms OnBytes.Desc.First.K4.Total.unitsA_of
#print axioms OnBytes.Desc.First.K4.Total.unitsT_of
#print axioms OnBytes.Desc.First.K4.Total.unitsW_of
#print axioms OnBytes.Desc.First.K4.Total.unitsW_pub
#print axioms OnBytes.Desc.First.K4.Total.units_of_merge
#print axioms OnBytes.Desc.First.K4.Total.rowB_tokv
#print axioms OnBytes.Desc.First.K4.Total.rests_plan
#print axioms OnBytes.Desc.First.K4.Total.rowSkel_plan
#print axioms OnBytes.Desc.First.K4.Total.row_returns_of_plan
#print axioms OnBytes.Desc.First.K4.Total.rowB_of_return
