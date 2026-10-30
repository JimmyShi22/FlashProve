-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/MergeRecordsClosedForm.lean: the shapes of what the merge leaves
of each weight claim (own.wo.recs), from a return of the hearing of the layers' own rounds at tokens
0 with HearLeft and zkFits: they are the shapes at the blank environment of the claims
(blankClaims), with the embedding's claim in its second text (embeddingClaimZeros): a term in the
plan that runs no hearing. General; nothing is evaluated.

Why. The rest of the own record has a closed form in OwnRecordClosedForm.lean; this list is its last
piece. The proof calls the library's hear_merge, hear_of_flat, mergeHear_inv, skel_blank,
weightClaims_rel, claimE_rel, powers_size and zip_recs
(Johnson/Desc/First/K4/Returns/FlRelWhole.lean), and embeddingClaim_alikeZeros
(WeightClaimsTests.lean).

  mergeRecordsShapes      that term. n: the number of the merge's slots. none where a claim is
                          lacking.
  claimAlike_trans        ClaimAlike is transitive.
  **hearing_mergeRecordsShapes**   from a return at tokens 0 with HearLeft and zkFits, the term is
                          the list of the shapes.

Limits. From a return with HearLeft and zkFits, at tokens 0 alone. What any of this costs Lean's
kernel is not measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.WeightClaimsTests
import Johnson.Desc.First.K4.Returns.FlRelWhole
import Johnson.Desc.First.K4.Returns.Whole
import Johnson.Top.H0.MergeLaw.Flat
import OnBytes.Desc.First.K4.MergeClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 Own TableAt ClaimEnv callsTS)
open OnBytes.Flat (All2 OptRel ClaimAlike)
open OnBytes.Desc.First.K4.RtPub (blankClaims embeddingClaimZeros embeddingClaim_alikeZeros
    skel_blank weightClaims_rel claimE_rel
  zkFits)
open OnBytes.Desc.First.P1 (powers_size)
open VerifiableInference.Desc.First.Shape

/-- **The shapes of what the merge leaves of each weight claim, as a term in the plan**: n: the
number of the merge's slots. none where a claim is lacking. -/
def mergeRecordsShapes (P : Pub) (hp : HPlan2) (g n : Nat) : Option (List RecSh) :=
  (callsTS P).bind fun TS => ((blankClaims P hp g).weightClaims TS).bind fun cp =>
    (if (g == 0) = true then
      (embeddingClaimZeros (blankClaims P hp g) (Array.replicate (P.y.ls + P.y.h.lt) zeroE)
        (Array.replicate (P.y.lPd - P.y.ls) zeroE) P.V (Array.replicate P.y.T 0)).map ([·])
    else some []).map fun ce =>
      (((cp ++ ce).zip (List.replicate n zeroE)).map fun y => wsRowPart P.wsLay y.1 zeroE).map recSh

/-- ClaimAlike is transitive. -/
theorem claimAlike_trans {a b c : WsClaim} (h1 : ClaimAlike a b) (h2 : ClaimAlike b c) :
    ClaimAlike a c := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  have key : ∀ {l1 l2 l3 : List WsFac}, All2 OnBytes.Flat.FacAlike l1 l2 →
      All2 OnBytes.Flat.FacAlike l2 l3 → All2 OnBytes.Flat.FacAlike l1 l3 := by
    intro l1 l2 l3 u
    induction u generalizing l3 with
    | nil =>
      intro v
      cases v
      exact All2.nil
    | cons x _ ih =>
      intro v
      cases v with
      | cons y w =>
        exact All2.cons ⟨x.1.trans y.1, x.2.1.trans y.2.1, x.2.2.trans y.2.2⟩ (ih w)
  exact key h1.2 h2.2

/-- **What the merge leaves of each weight claim is mergeRecordsShapes**, from a return at tokens 0
with HearLeft and zkFits. -/
theorem hearing_mergeRecordsShapes {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard}
    {F G : Fork} {t u : Tape}
    {o : Own} {iU3 : Nat} {tab : List TableAt} (hh : hearFl P hp g fo F t = some (o, G, u))
    (hL : HearLeft P hp g fo iU3 tab F G o) (hz : zkFits P fo.zk = true)
    (htk : P.tokv = Array.replicate P.y.T 0) :
    mergeRecordsShapes P hp g (mergeSlots hp g o).size = some (o.wo.recs.map recSh) := by
  have N := hL.nums
  obtain ⟨cl, G5, u5, hm, -, d⟩ := hear_merge hh
  obtain ⟨x, mu, eps, c, beta, v, T, r1, rY, rV, qs, -, -, -, -, -, -, -, -, -, -, -, -, -, hrec,
      -⟩ :=
    VerifiableInference.Desc.First.MergeLaw.mergeHear_inv
      (VerifiableInference.Desc.First.MergeLaw.hear_of_flat d)
  have S : RtPub.ClaimSkel (OnBytes.Desc.First.K4.envOf P o) (blankClaims P hp g) :=
    skel_blank (v := o.v) (by rw [hL.v]; rfl) (by rw [hL.v]; rfl) (by rw [hL.v]; exact hz) N.rs
      P.rope _
  unfold mergeClaims at hm
  unfold mergeRecordsShapes
  cases hT : callsTS P with
  | none =>
    rw [hT] at hm
    cases hm
  | some TS =>
    rw [hT] at hm
    have hm1 : ((OnBytes.Desc.First.K4.envOf P o).weightClaims TS).bind (fun cp =>
      (if (g == 0) = true then ((OnBytes.Desc.First.K4.envOf P o).claimE o.H.ZE o.H.tkh P.V
          P.tokv).map ([·])
        else some []).map fun ce => (cp ++ ce).toArray) = some cl := hm
    have rel1 := weightClaims_rel S TS
    cases hW : (OnBytes.Desc.First.K4.envOf P o).weightClaims TS with
    | none =>
      rw [hW] at hm1
      cases hm1
    | some cp =>
      rw [hW] at hm1 rel1
      cases hW0 : (blankClaims P hp g).weightClaims TS with
      | none =>
        rw [hW0] at rel1
        exact rel1.elim
      | some cp0 =>
        rw [hW0] at rel1
        have rel1' : All2 ClaimAlike cp cp0 := rel1
        have hm2 : (if (g == 0) = true then
            ((OnBytes.Desc.First.K4.envOf P o).claimE o.H.ZE o.H.tkh P.V P.tokv).map ([·]) else some
                []).map
              (fun ce => (cp ++ ce).toArray) = some cl := hm1
        have fin : ∀ ce ce0 : List WsClaim, All2 ClaimAlike ce ce0 → (cp ++ ce).toArray = cl →
            (((cp0 ++ ce0).zip (List.replicate (mergeSlots hp g o).size zeroE)).map
              fun y => wsRowPart P.wsLay y.1 zeroE).map recSh = o.wo.recs.map recSh := by
          intro ce ce0 hce hcl
          rw [hrec, ← hcl, Array.toList_zip]
          exact (zip_recs P.wsLay (fun c e => mulE e (wsEpsT P.wsLay c o.wo.rm)) (fun _ _ => zeroE)
            (rel1'.append hce) (powers x (mergeSlots hp g o).size).toList
            (List.replicate (mergeSlots hp g o).size zeroE) (by
              rw [Array.length_toList, powers_size, List.length_replicate])).symm
        show ((blankClaims P hp g).weightClaims TS).bind _ = _
        rw [hW0]
        show Option.map _ (if (g == 0) = true then _ else _) = _
        by_cases hg : (g == 0) = true
        · rw [if_pos hg] at hm2 ⊢
          have rel2 := claimE_rel S (ZE := o.H.ZE)
            (ZE₀ := Array.replicate (P.y.ls + P.y.h.lt) zeroE) (tkh := o.H.tkh)
            (tkh₀ := Array.replicate (P.y.lPd - P.y.ls) zeroE)
            (by rw [N.ze, if_pos hg, Array.size_replicate])
            (by rw [N.tkh, if_pos hg, Array.size_replicate]) P.V (t := P.tokv)
            (t₀ := Array.replicate P.y.T 0) (by rw [htk]) (by rw [htk])
          have rel3 := embeddingClaim_alikeZeros (blankClaims P hp g) (Array.replicate (P.y.ls +
              P.y.h.lt) zeroE)
            (Array.replicate (P.y.lPd - P.y.ls) zeroE) P.V (Array.replicate P.y.T 0)
          cases e1 : (OnBytes.Desc.First.K4.envOf P o).claimE o.H.ZE o.H.tkh P.V P.tokv with
          | none =>
            rw [e1] at hm2
            cases hm2
          | some ce =>
            rw [e1] at hm2 rel2
            cases e2 : (blankClaims P hp g).claimE (Array.replicate (P.y.ls + P.y.h.lt) zeroE)
              (Array.replicate (P.y.lPd - P.y.ls) zeroE) P.V (Array.replicate P.y.T 0) with
            | none =>
              rw [e2] at rel2
              exact rel2.elim
            | some cb =>
              rw [e2] at rel2 rel3
              cases e3 : embeddingClaimZeros (blankClaims P hp g) (Array.replicate (P.y.ls +
                  P.y.h.lt) zeroE)
                (Array.replicate (P.y.lPd - P.y.ls) zeroE) P.V (Array.replicate P.y.T 0) with
              | none =>
                rw [e3] at rel3
                exact rel3.elim
              | some cz =>
                rw [e3] at rel3
                have a13 : ClaimAlike ce cz := claimAlike_trans rel2 rel3
                exact congrArg some (fin [ce] [cz] (All2.cons a13 All2.nil) (Option.some.inj hm2))
        · rw [if_neg hg] at hm2 ⊢
          exact congrArg some (fin [] [] All2.nil (Option.some.inj hm2))

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.mergeRecordsShapes
#print axioms OnBytes.Desc.First.K4.Rt.claimAlike_trans
#print axioms OnBytes.Desc.First.K4.Rt.hearing_mergeRecordsShapes
