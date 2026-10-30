-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/HearingMovesShapes.lean: from a return of the hearing of the
layers' own rounds: the shapes of three row forms and of the two sumchecks that are left open, in
closed form, in the record's own slots. General; nothing is evaluated.

Why. OwnRecordClosedForm.lean writes the shape of what the hearing leaves as a function of the plan,
and needs these five equations. Beneath them stand three laws on the flat engine's moves (levelIn,
tscIn, flatForkEnd), from the library's levelIn_spec, tscIn_spec, tscIn_flags, hear_of_flat and
mergeHear_inv. The walk's length is the library's win_len
(Johnson/Desc/ProofFile/Honest/K4/Law/Live/PscLive.lean).

  slotsFold_shape, slotsDoubleFold_shape, forkStart_shape, normsStart_shape   sums of slots, seen
                          through affSh.
  productLevel_rowShape, tokenSumcheck_openShape, mergeMove_openShape   the three moves, from a
                          return.
  hearGated_levelCalls    the gated products' two calls, with their start forms.
  **squaresLayer_rowShape, gatedLayers_rowShapes**   the rows of the squares' product layer and of
                          the two gated layers.
  **rowProductsSumcheck_openShape, mergeSumcheck_openShape**   the two sumchecks that the hearing
                          leaves open.

Limits. From a return alone: that the hearing returns is not said here. What any of this costs
Lean's kernel is not measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.AtStep
import OnBytes.Desc.First.P1.TscKit
import OnBytes.Desc.First.P1.TscEnded
import OnBytes.Desc.First.P1.BatchPoint
import OnBytes.Desc.First.K4.MergeClaims
import OnBytes.Desc.First.K4.NormsCalls
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.PscLive
import Johnson.Top.H0.MergeLaw.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Desc.First.P1 (bind_some pure_some must_some need_some onTape_some pscRound_spec stepP
  levelIn_spec levelWs tscIn_spec tscIn_flags tscWs pscBegin_spec pscEnds_spec batch_spec
  powers_size Rnd)
open VerifiableInference.Desc.First.Shape

/-! ## 0 Sums of slots, seen through affSh -/

/-- A sum of slots under weights, seen through affSh, appends the slots in order. -/
theorem slotsFold_shape {α : Type} (f : α → Nat) (c : α → E) : ∀ (l : List α) (a : Aff),
    affSh (l.foldl (fun C x => Aff.addMul C (Aff.slot (f x)) (c x)) a) =
      (affSh a).append (AffSh.mk [] (l.map f))
  | [], a => by simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]
  | x :: l, a => by
    rw [List.foldl_cons, slotsFold_shape f c l, affSh_addMul, affSh_slot]
    simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]

/-- The same for a sum over two lists. -/
theorem slotsDoubleFold_shape {α β : Type} (f : α → β → Nat) (c : α → β → E) (m : List β) :
    ∀ (l : List α) (a : Aff),
    affSh (l.foldl (fun C i => m.foldl (fun C s => Aff.addMul C (Aff.slot (f i s)) (c i s)) C) a) =
      (affSh a).append (AffSh.mk [] (l.flatMap fun i => m.map (f i)))
  | [], a => by simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]
  | i :: l, a => by
    rw [List.foldl_cons, slotsDoubleFold_shape f c m l, slotsFold_shape (f i) (c i)]
    simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots, List.flatMap_cons]

/-- The shape of the merge's start form. -/
theorem forkStart_shape (sv : Array Nat) (rho : Array E) (h : rho.size = sv.size) :
    affSh (wsForkStart sv rho) = AffSh.mk [] sv.toList := by
  unfold wsForkStart
  rw [← Array.foldl_toList, Array.toList_zip, slotsFold_shape Prod.fst Prod.snd,
    List.map_fst_zip (Nat.le_of_eq (by rw [Array.length_toList, Array.length_toList, h]))]
  rfl

/-- The shape of the norms' start form. -/
theorem normsStart_shape (y : Lay) (sW : Nat) (gp rhoI PV : Array E) :
    affSh (normsStart y sW gp rhoI PV).1 =
      AffSh.mk [] ((List.range y.NI).flatMap fun i =>
        (List.range (ledNS y.h.xl)).map fun s => sW + ledNS y.h.xl * i + s) := by
  unfold normsStart
  dsimp only
  rw [slotsDoubleFold_shape (fun i s => sW + ledNS y.h.xl * i + s)
    (fun i s => mulE (mulE (powE (invE (ofNat 2)) y.lPd) ((eqTab rhoI).getD i zeroE))
      (gp.getD s zeroE))]
  rfl

/-! ## 1 Three moves of the flat engine, from a return -/

/-- **A layer of a product tree**: its row's shape, and its left end value's slot. -/
theorem productLevel_rowShape {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {lv : Level} (h : Fl.levelIn mu rho C order F t = some (lv, G, u)) :
    affSh lv.row = rowFormSh F.next (2 * mu + 3) (affSh C) (AffSh.mk [] []) ∧
      lv.sL = F.next + 1 + 2 * mu + 2 := by
  obtain ⟨ho, T, mu0, eps, ms, y, shL, shR, v, G1, p, -, a1, -, -, -, hv, hr, -, -, -, hst, hf,
      hrow,
    -, hsL, -⟩ := levelIn_spec h
  have hlen : (levelWs mu rho order).length = mu := by
    unfold levelWs
    rw [List.length_map, ho]
  have hm : ms.length = (levelWs mu rho order).length := by
    rw [← a1, List.length_map]
  have hw : p.walk.1.length = 1 + 2 * (levelWs mu rho order).length + 2 :=
    ProofFile.Honest.K4.Live.win_len p (levelWs mu rho order) 2
      (fun w hw => by
        obtain ⟨v, -, rfl⟩ := List.mem_map.1 hw
        rfl) hv
      (by
        rw [hr, List.length_map, List.length_append, hm]
        rfl)
  refine ⟨?_, hsL⟩
  rw [hrow, affSh_rowForm, hst, hf, hw, hlen, show 1 + 2 * mu + 2 = 2 * mu + 3 by omega]
  rfl

/-- **A token sumcheck**: the shape of the sumcheck that it leaves open. -/
theorem tokenSumcheck_openShape {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    pscSh o.p = PscSh.mk false true (List.replicate lt 3 ++ [dY + 1]) (lt + 1) (F.next + 1)
        (AffSh.mk [] [F.next]) true ∧ o.sCl = F.next := by
  obtain ⟨hlt, T, mu0, eps, ms, y, v1, v, G0, hcl, -, hG0, -, a1, -, -, -, hv, hr, -, -, -, hst, hf,
    -⟩ := tscIn_spec h
  obtain ⟨f1, f2, f3⟩ := tscIn_flags h
  have hn : G0.next = F.next + 1 := congrArg LedSh.next (hideRun_sh hG0)
  have hz : (P.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]
    omega
  have hd : (tscWs (P.toList.take lt)).map (·.d) = List.replicate lt 3 := by
    unfold tscWs
    rw [List.map_map]
    show (P.toList.take lt).map (fun _ => 3) = _
    rw [List.map_const', hz]
  have hm : ms.length = lt := by
    have e := congrArg List.length a1
    rw [List.length_map] at e
    rw [e]
    unfold tscWs
    rw [List.length_map, hz]
  have hrs : o.p.r.size = lt + 1 := by
    rw [← Array.length_toList, hr, List.length_map, List.length_append, hm]
    rfl
  refine ⟨?_, hcl⟩
  unfold pscSh
  rw [f3, f1, f2, hv, hst, hf, hn, hrs, List.map_append, hd, affSh_slot]
  rfl

/-- **The merge of the weight claims**: the shape of the sumcheck that it leaves open. By the
library's hear_of_flat and mergeHear_inv (Johnson/Top/H0/MergeLaw/Flat.lean,
Johnson/Top/H0/MergeLaw/Hear.lean), which have six of the seven places; the start form's shape is
forkStart_shape's. -/
theorem mergeMove_openShape {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork}
    {t u : Tape}
    {w : WsForkOut} (h : flatForkEnd lay cl sv F t = some (w, G, u)) :
    pscSh w.p = PscSh.mk false true (List.replicate lay.lk 3 ++ [2]) (lay.lk + 1) F.next
      (AffSh.mk [] sv.toList) true := by
  obtain ⟨x, mu, eps, c, beta, v, T, r1, rY, rV, qs, hn, -, -, -, -, -, -, -, -, hr, -, -, -, -, hv,
    hf, hs, f1, f2, f3⟩ := VerifiableInference.Desc.First.MergeLaw.mergeHear_inv
      (VerifiableInference.Desc.First.MergeLaw.hear_of_flat h)
  have hrs : w.p.r.size = lay.lk + 1 := by
    rw [← Array.length_toList, hr, List.length_append, List.length_map, hn]
    rfl
  unfold pscSh
  rw [f2, f1, f3, hv, hrs, hf, hs, forkStart_shape sv _ (powers_size x sv.size), List.map_append,
    List.map_replicate]
  rfl

/-! ## 2 The gated products' two calls, with their start forms -/

/-- The two calls of levelIn that a return of the gated products makes. -/
theorem hearGated_levelCalls {P : Pub} {H : Heard} {K : HeardStack} {F G : Fork} {t u : Tape}
    {hd hd2 : Level} (h : hearGated engFl P H K F t = some ((hd, hd2), G, u)) :
    ∃ (rho1 rho2 e : Array E) (Ga : Fork) (ua ub : Tape),
      Fl.levelIn P.rd.muH rho1 (Aff.slot K.sH1) (orderRange P.rd.muH) F t = some (hd, Ga, ua) ∧
      Fl.levelIn P.rd.muH2 rho2
        ((List.range P.y.LamM).foldl
          (fun (C : Aff) lm => C.addMul (Aff.slot (K.sH1 + 1 + lm)) (e.getD lm zeroE)) aff0)
        (orderRange P.rd.muH2) Ga ub = some (hd2, G, u) := by
  unfold hearGated at h
  obtain ⟨x1, A1, a1, c1, k1⟩ := bind_some.mp h
  obtain ⟨x2, A2, a2, c2, k2⟩ := bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c2
  obtain ⟨x3, A3, a3, c3, k3⟩ := bind_some.mp k2
  have c3' : Fl.point _ _ A1 a1 = some (x3, A3, a3) := c3
  obtain ⟨_, rfl⟩ := onTape_some.mp c3'
  obtain ⟨x4, A4, a4, c4, k4⟩ := bind_some.mp k3
  obtain ⟨e, rfl, rfl⟩ := pure_some.mp k4
  have e1 : x1 = hd := congrArg Prod.fst e
  have e2 : x4 = hd2 := congrArg Prod.snd e
  subst e1
  subst e2
  exact ⟨_, _, _, A1, a1, a3, c1, c4⟩

/-! ## 3 The five shapes, at the hearing -/

variable {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}

/-- The row of the squares' product layer. f: its sumcheck's first slot. -/
theorem squaresLayer_rowShape (hh : hearFl P hp g fo F t = some (o, G, u)) :
    ∃ f, o.H.wpl.sL = f + 1 + 2 * P.rd.muV + 2 ∧
      affSh o.H.wpl.row = rowFormSh f (2 * P.rd.muV + 3)
        (AffSh.mk [] ((List.range P.y.NI).flatMap fun i =>
          (List.range (ledNS P.y.h.xl)).map fun s => o.H.sW + ledNS P.y.h.xl * i + s))
        (AffSh.mk [] []) := by
  obtain ⟨-, -, -, -, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, h1, h2, -⟩ :=
    hear_parts hh
  obtain ⟨-, -, -, -, -, k6, -, k8, -⟩ := hearTerms_keeps h2
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, -, -, -, -, -, -,
    rhoI, -, c, -⟩ := hearNorms_calls h1
  obtain ⟨a, b⟩ := productLevel_rowShape c
  rw [k8, k6]
  exact ⟨F6.next, b, by rw [a, normsStart_shape]⟩

/-- The rows of the two gated layers. f, f2: their sumchecks' first slots. -/
theorem gatedLayers_rowShapes (hh : hearFl P hp g fo F t = some (o, G, u)) :
    ∃ f f2 hd2, o.hd2 = some hd2 ∧ o.hd.sL = f + 1 + 2 * P.rd.muH + 2 ∧
      hd2.sL = f2 + 1 + 2 * P.rd.muH2 + 2 ∧
      affSh o.hd.row = rowFormSh f (2 * P.rd.muH + 3) (AffSh.mk [] [o.K.sH1]) (AffSh.mk [] []) ∧
      affSh hd2.row = rowFormSh f2 (2 * P.rd.muH2 + 3)
        (AffSh.mk [] ((List.range P.y.LamM).map fun lm => o.K.sH1 + 1 + lm)) (AffSh.mk [] []) := by
  obtain ⟨-, -, -, -, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, -, -, -, h4, e5, -⟩ :=
    hear_parts hh
  obtain ⟨rho1, rho2, e, Ga, ua, ub, c1, c2⟩ := hearGated_levelCalls h4
  obtain ⟨a1, b1⟩ := productLevel_rowShape c1
  obtain ⟨a2, b2⟩ := productLevel_rowShape c2
  refine ⟨G3.next, Ga.next, hd2, e5, b1, b2, by rw [a1, affSh_slot], ?_⟩
  rw [a2, slotsFold_shape (fun lm => o.K.sH1 + 1 + lm) (fun lm => e.getD lm zeroE)]
  rfl

/-- The row products' token sumcheck, which the hearing leaves open. -/
theorem rowProductsSumcheck_openShape (hh : hearFl P hp g fo F t = some (o, G, u)) :
    pscSh o.H.tV.p = PscSh.mk false true (List.replicate P.y.h.lt 3 ++ [3]) (P.y.h.lt + 1)
      (o.H.tV.sCl + 1) (AffSh.mk [] [o.H.tV.sCl]) true := by
  obtain ⟨-, -, -, -, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, h1, h2, -⟩ :=
    hear_parts hh
  obtain ⟨-, -, -, -, -, -, -, -, -, -, k11⟩ := hearTerms_keeps h2
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, -, -, -, -, -, -,
    rhoI, -, -, -, -, c, -⟩ := hearNorms_calls h1
  obtain ⟨a, b⟩ := tokenSumcheck_openShape c
  rw [k11, a, b]

/-- The merge's sumcheck, which the hearing leaves open. -/
theorem mergeSumcheck_openShape (hh : hearFl P hp g fo F t = some (o, G, u)) :
    pscSh o.wo.p = PscSh.mk false true (List.replicate P.wsLay.lk 3 ++ [2]) (P.wsLay.lk + 1)
      o.wo.p.first (AffSh.mk [] (mergeSlots hp g o).toList) true := by
  obtain ⟨cl, G5, u5, -, -, d⟩ := hear_merge hh
  have a := mergeMove_openShape d
  have b : o.wo.p.first = G5.next := congrArg PscSh.first a
  rw [a, b]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.slotsFold_shape
#print axioms OnBytes.Desc.First.K4.Rt.slotsDoubleFold_shape
#print axioms OnBytes.Desc.First.K4.Rt.forkStart_shape
#print axioms OnBytes.Desc.First.K4.Rt.normsStart_shape
#print axioms OnBytes.Desc.First.K4.Rt.productLevel_rowShape
#print axioms OnBytes.Desc.First.K4.Rt.tokenSumcheck_openShape
#print axioms OnBytes.Desc.First.K4.Rt.mergeMove_openShape
#print axioms OnBytes.Desc.First.K4.Rt.hearGated_levelCalls
#print axioms OnBytes.Desc.First.K4.Rt.squaresLayer_rowShape
#print axioms OnBytes.Desc.First.K4.Rt.gatedLayers_rowShapes
#print axioms OnBytes.Desc.First.K4.Rt.rowProductsSumcheck_openShape
#print axioms OnBytes.Desc.First.K4.Rt.mergeSumcheck_openShape
