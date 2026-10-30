-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnRecsG.lean: THE SEVEN CALLS OF THE HEARING OF THE LAYERS' OWN ROUNDS, EACH ON ITS
NAMED TAPE, IN EVERY GROUP; and the seven records as the library's `RecAt`. OwnRecs.lean says this
of a group that is not the first. Here the tape behind the points in front is `t0.drop (k0 g)`
(`k0`, OnBytes/Desc/First/K4/NormsTape.lean: three rounds in the first group, one in a later one).
Statements and proofs.

  `own_callsG`: from a return of `hear` on a tape t0: the six calls of OwnRecs.lean's `own_calls6`
    on the cuts `Ks.tc1` … `Ks.tc6` of `t0.drop (k0 g)`; that the three words of the terms'
    coefficient are not all 0; `Chain7` (OwnRecs.lean: what ties H1, tT and the ledgers between the
    calls to the record o, the first ledger and the tape); what the text does between the gated
    layers and the merge (`mergeFront`, OnBytes/Desc/First/K4/MergeClaims.lean: in the first group
    it takes the embedding's one scalar off the round in front of the merge); the merge's call, on a
    tape u5 that agrees with the cut `Ks.tcW` behind its first round and in the first word that this
    round drew.
  `own_recsG`: `Recs6` (OwnRecs.lean) at that tape, and the seventh record's `RecAt`.

NO NEW ARGUMENT: `own_calls7`'s proof, with k0 g in the place of 1, over `hear_parts`
(MergeClaims.lean); `claimsIn_spec` (OnBytes/Desc/First/P1/BatchPoint.lean); `merge_recAt`
(MergeRec.lean).

Limits. One direction: from a return. The ledgers stand under "there are". In the first group the
two further points in front, and the embedding's claim, are not spoken of. Nothing on rows, slots or
soundness.
-/
import Johnson.Road.K4.MergeRec
import OnBytes.Desc.First.K4.MergeClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Tie.Pv.Lay (RecAt)
open OnBytes.Desc.First.P1 (pscT drawnOf Ks levelRec tscIn_heard tapeEps pscRow_spec claimsIn_spec
  sentOf)

/-- **The seven calls, each on its named tape, in every group.** -/
theorem own_callsG {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} (h : hear engFl P hp g fo F t0 = some (o, G, u)) :
    ∃ (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork)
      (v1 v2 v5 u4 u5 : Tape) (cl : Array WsClaim),
      o.hd2 = some hd2 ∧ o.H.ztF = H1.ztF ∧ isZeroE tT.p.eps = false ∧
      Fl.levelIn P.rd.muV
          (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
          (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
          (orderDefault P.rd.muV) F4 ((ksOf P hp).tc1 (t0.drop (k0 g))) = some (H1.wpl, F7, v1) ∧
      Fl.tscIn H1.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F8
          (((ksOf P hp).tcP (t0.drop (k0 g))).drop 1) = some (H1.tV, G1, v2) ∧
      Fl.tscIn H1.ztF P.y.h.lt (nEndT P.y) 1 G1
          ((((ksOf P hp).tcP (t0.drop (k0 g))).drop 1).drop (P.y.h.lt + 3)) =
        some (tT, G1', (ksOf P hp).tc4 (t0.drop (k0 g))) ∧
      hearStack engFl P o.v o.H hp.lamS (hp.NCL - (if (g == 0) = true then 1 else 0)) G2
          ((ksOf P hp).tc4 (t0.drop (k0 g))) = some (o.K, G3, (ksOf P hp).tc5 (t0.drop (k0 g))) ∧
      Fl.levelIn P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
          (orderRange P.rd.muH) G3 ((ksOf P hp).tc5 (t0.drop (k0 g))) = some (o.hd, G3', v5) ∧
      Fl.levelIn P.rd.muH2
          ((drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray ++
            downFrom o.K.rs P.y.lfe ++ tT.r)
          (Road.Rows.start2 P.y.LamM o.K.sH1
            (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray)
          (orderRange P.rd.muH2) G3' ((ksOf P hp).tc6 (t0.drop (k0 g))) = some (hd2, G4, u4) ∧
      Chain7 P hp F t0 (t0.drop (k0 g)) o H1 tT F4 F7 F8 G1' G2 ∧
      u4 = (ksOf P hp).tcW (t0.drop (k0 g)) ∧
      mergeFront g o G4 u4 G5 u5 ∧ mergeClaims P g o = some cl ∧ cl.size = hp.NCL ∧
      flatForkEnd P.wsLay cl (mergeSlots hp g o) G5 u5 = some (o.wo, G, u) ∧
      u5.drop 1 = ((ksOf P hp).tcW (t0.drop (k0 g))).drop 1 ∧
      tapeEps u5 = tapeEps ((ksOf P hp).tcW (t0.drop (k0 g))) := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, h1, h2, h3, h4, e5, e6,
    e7, e8, e9⟩ := hear_parts h
  obtain ⟨F4, F7, F8, rhoI, vW, vP, gam, om, w0, wI, d0, dI, a1, _, a3, a4, _, a6, a7, a8, a9, _,
    a11, a12, a13, _, a15, a16, a17, a18, a19⟩ := hearNorms_tape h1
  obtain ⟨tT, G1', u1', row, p', b1, b2, b3, b4⟩ := hearTerms_calls h2
  obtain ⟨tT', G3', c1, c2, _, c4⟩ := hearGated_tape h4
  -- the lengths of the two token points
  have l2 : (H1.PV.toList.take P.y.h.lt).length = P.y.h.lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left (tscIn_heard a18).1
  have l3 : (H1.ztF.toList.take P.y.h.lt).length = P.y.h.lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left (tscIn_heard b1).1
  -- the tapes
  have T0 : (t0.drop (k0 g)).drop 1 = t0.drop (k0 g + 1) := drop_drop' (k0 g) 1 t0
  have T1 : (ksOf P hp).tc1 (t0.drop (k0 g)) = t0.drop (k0 g + 2) := by
    unfold Ks.tc1
    rw [T0, drop_drop']
  have TP : (ksOf P hp).tcP (t0.drop (k0 g)) = t0.drop (k0 g + P.rd.muV + 6) := by
    unfold Ks.tcP
    rw [T1, drop_drop', drop_drop']
    congr 1
    show k0 g + 2 + (P.rd.muV + 3) + 1 = _
    omega
  have T2 : ((ksOf P hp).tcP (t0.drop (k0 g))).drop 1 = t0.drop (k0 g + P.rd.muV + 7) := by
    rw [TP, drop_drop']
  have hu1 : u1 = (((ksOf P hp).tcP (t0.drop (k0 g))).drop 1).drop (P.y.h.lt + 3) := by
    rw [a19, l2, T2, drop_drop']
  have hu1' : u1' = u1.drop (P.y.h.lt + 3) := by
    have e := (tscIn_heard b1).2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [l3] at e
    exact e
  have hu2 : u2 = (ksOf P hp).tc4 (t0.drop (k0 g)) := by
    rw [(pscRow_spec b3).2.1, hu1', hu1]
    rfl
  have hu3 : u3 = (ksOf P hp).tc5 (t0.drop (k0 g)) := by
    rw [stack_rest h3, hu2]
    unfold Ks.tc5
    rw [drop_drop']
    congr 1
    show hp.lamS + 4 = 1 + (hp.lamS + 3)
    omega
  have T5 : (((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1 =
      u3.drop (P.rd.muH + 4) := by
    rw [hu3, drop_drop']
  have T6 : (ksOf P hp).tc6 (t0.drop (k0 g)) = u3.drop (P.rd.muH + 4 + 1) := by
    unfold Ks.tc6
    show ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1).drop 1 = _
    rw [T5, drop_drop']
  -- the two joins' points
  have hI : (drawnOf ((t0.drop (k0 g)).drop 1)).toArray = rhoI := by
    rw [T0, a9, a11]
    rfl
  have hM : drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1) =
      drawnAt u3 (P.rd.muH + 4) := by
    rw [T5]
    rfl
  -- what the terms' stretch keeps
  have hz : o.H.ztF = H1.ztF := by rw [b4]
  have hr : tT'.r = tT.r := by
    rw [b4] at c1
    rw [← Option.some.inj c1]
  have hH : Chain7 P hp F t0 (t0.drop (k0 g)) o H1 tT F4 F7 F8 G1' G2 := by
    have s1 : (sentOf (t0.drop (k0 g))).toArray = vW := by
      rw [a4]
      exact Array.toArray_toList
    have s2 : (sentOf ((ksOf P hp).tcP (t0.drop (k0 g)))).toArray = vP := by
      rw [TP, a13]
      exact Array.toArray_toList
    refine ⟨?_, ?_, a6, ?_, ?_, a15, ?_, ?_, (pscRow_spec b3).2.2⟩
    · rw [b4, pscRow_made b3, (pscRow_spec b3).1]
      rfl
    · rw [a3, a1]
      rfl
    · rw [s1]
      exact a7
    · rw [a8, a4]
      rfl
    · rw [s2]
      exact a16
    · rw [a17, TP, a13]
      rfl
  have hu4 : u4 = (ksOf P hp).tcW (t0.drop (k0 g)) := by
    rw [levelIn_rest c4]
    unfold Ks.tcW
    rw [T6]
    show (u3.drop (P.rd.muH + 4 + 1)).drop (P.rd.muH2 + 4) =
      ((u3.drop (P.rd.muH + 4 + 1)).drop (P.rd.muH2 + 3)).drop 1
    rw [drop_drop' (P.rd.muH2 + 3) 1]
  have h5 : u5.drop 1 = u4.drop 1 ∧ tapeEps u5 = tapeEps u4 := by
    unfold mergeFront at e6
    by_cases hg : (g == 0) = true
    · rw [if_pos hg] at e6
      obtain ⟨_, v, _, et, _, _⟩ := claimsIn_spec e6
      rw [et]
      cases u5 with
      | nil => exact ⟨rfl, rfl⟩
      | cons r rest => exact ⟨rfl, rfl⟩
    · rw [if_neg hg] at e6
      rw [e6.2.2]
      exact ⟨rfl, rfl⟩
  refine ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, t0.drop (k0 g + P.rd.muV + 6), u1,
    u3.drop (P.rd.muH + 4), u4, u5, cl, e5, hz, b2, ?_, ?_, ?_, ?_, ?_, ?_, hH, hu4, e6, e7, e8, e9,
    by rw [h5.1, hu4], by rw [h5.2, hu4]⟩
  · rw [T1, hI]
    exact a12
  · rw [T2]
    exact a18
  · rw [← hu1, ← hu2, (pscRow_spec b3).2.1]
    exact b1
  · rw [← hu2, ← hu3]
    exact h3
  · rw [← hu3]
    exact c2
  · rw [T6, hM, ← hr]
    exact c4

/-- **The seven records, in every group.** The four records that the text does not hand on are
named, as in `own_recs6`. -/
theorem own_recsG {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} (h : hear engFl P hp g fo F t0 = some (o, G, u)) :
    ∃ (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 G2 G3 G3' : Fork),
      o.hd2 = some hd2 ∧ o.H = heardOf H1 tT ∧
      Recs6 P hp o H1 tT hd2 (t0.drop (k0 g))
        (levelRec P.rd.muV
          (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
          (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
          (orderDefault P.rd.muV) F4 ((ksOf P hp).tc1 (t0.drop (k0 g))))
        (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop (k0 g))))
        (levelRec P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
          (orderRange P.rd.muH) G3 ((ksOf P hp).tc5 (t0.drop (k0 g))))
        (levelRec P.rd.muH2
          ((drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray ++
            downFrom o.K.rs P.y.lfe ++ tT.r)
          (Road.Rows.start2 P.y.LamM o.K.sH1
            (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray)
          (orderRange P.rd.muH2) G3' ((ksOf P hp).tc6 (t0.drop (k0 g)))) ∧
      RecAt (pscT 0 P.wsLay.lk (((ksOf P hp).tcW (t0.drop (k0 g))).drop 1))
        (List.replicate P.wsLay.lk (OnBytes.Psc.Weight.plain 3)) P.wsLay.lk 1
        (pscT 0 P.wsLay.lk (((ksOf P hp).tcW (t0.drop (k0 g))).drop 1)).v.length o.wo.p := by
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, v1, v2, v5, u4, u5, cl, e5, _, _,
    c1, c2, c3, c4, c5, c6, hH, _, _, _, _, c7, h5, _⟩ := own_callsG h
  refine ⟨H1, hd2, tT, F4, G2, G3, G3', e5, hH.heard, ⟨level_recAt c1, tsc_recAt c2, tsc_recAt c3,
    stack_recAt c4, level_recAt c5, level_recAt c6⟩, ?_⟩
  rw [← h5]
  exact (merge_recAt c7).1

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.own_callsG
#print axioms OnBytes.Road.K4.own_recsG
