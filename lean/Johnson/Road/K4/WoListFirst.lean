-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/WoListFirst.lean: WHICH LIST OF CLAIMS K4's hearing hands to the merge IN THE FIRST
GROUP, at the ledger and on the tape that `LedG` names (Johnson/Road/K4/OwnLedgersG.lean). The first
group's twin of WoList.lean. `LedG.c7` says "there is a list cl on which `flatForkEnd` returned".
Here the list is named: what `weightClaims` returns at the plan's calls, then the one claim that
`claimE` returns (the embedding's); and its front is the list X.cl of a public record `Pub34`
(Johnson/Road/Rows/LayerEnds34.lean) whose environment of claims is the text's and whose reads are
the plan's. Statements and proofs.

  `ledG_merge`: the merge's call at LedG's own ledger G5 and tape u5, on the named list.
  `ledG_merge_pub34`: the merge's call on (X.cl ++ [cE]).toArray; that list has hp.NCL members.
  `ledG_flat`: so `FlatSpec` (Johnson/Road/K4/WoRecs.lean) at that list and LedG's tape u5.

HOW. No new argument: WoList.lean's, at the first group's letters. The hearing's calls are
functions: `hear_parts_first` (OnBytes/Desc/First/K4/HearParts.lean) keeps the list and has its
ledgers and tapes under "there are"; LedG names them; call by call, equal arguments give equal
returns.

Limits. One direction: from a return. The first group alone (hg). The embedding's claim cE stands
under "there is", tied by `claimE`'s return. Premises on X, in `ledG_merge_pub34` and `ledG_flat`:
its environment of claims is the text's, with the end point of LedG's second token sumcheck; its
reads are the plan's. That there is such an X is not said. What a claim is worth is not said.
Nothing on a draw or on soundness.
-/
import Johnson.Road.K4.OwnLedgersG
import Johnson.Road.K4.WoList

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Desc.First.P1 (drawnOf Ks tapeEps some_triple)

variable {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {o : Own} {F G : Fork}
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **The merge's call at LedG's ledger and tape, on the named list**: where the hearing returns in
the first group, and Ld names its ledgers and tapes. -/
theorem ledG_merge (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hg : (g == 0) = true) :
    ∃ (TS : List Nat) (cp : List WsClaim) (cE : WsClaim),
      callsTS P = some TS ∧ (envOf P o).weightClaims TS = some cp ∧
      (envOf P o).claimE o.H.ZE o.H.tkh P.V P.tokv = some cE ∧
      (cp ++ [cE]).toArray.size = hp.NCL ∧
      flatForkEnd P.wsLay (cp ++ [cE]).toArray
        ((Array.range (hp.NCL - 1)).map (o.K.sV + ·) ++ #[o.sVE]) G5 u5 = some (o.wo, G, u) := by
  obtain ⟨_, _, _, _, H1', hd2', TS, cp, cE, A1, A2, A3, A4, A5, u1, u2, u3, u4, v5, h1, h2, h3, h4,
    _, e6, e7, eE, e8, d2, e9⟩ := hear_parts_first h hg
  obtain ⟨v1, n1, n2⟩ := Ld.nt
  obtain ⟨rfl, rfl, rfl⟩ := some_triple.mp (h1.symm.trans n1)
  obtain ⟨_, rfl, rfl⟩ := some_triple.mp (h2.symm.trans n2)
  have c4 := Ld.c4
  rw [if_pos hg] at c4
  obtain ⟨_, rfl, rfl⟩ := some_triple.mp (h3.symm.trans c4)
  obtain ⟨tT', B, c1, c2, _, c4'⟩ := hearGated_tape h4
  obtain ⟨w5, d5⟩ := Ld.c5
  obtain ⟨_, rfl, _⟩ := some_triple.mp (c2.symm.trans d5)
  have hT := Option.some.inj (c1.symm.trans Ld.kTT)
  have hr : tT'.r = tT.r := by rw [hT]
  have T5 : (((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1 =
      ((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 4) := drop_drop' _ _ _
  have T6 : (ksOf P hp).tc6 (t0.drop (k0 g)) =
      ((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 4 + 1) := by
    unfold Ks.tc6
    show ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1).drop 1 = _
    rw [T5, drop_drop']
  have hM : drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1) =
      drawnAt ((ksOf P hp).tc5 (t0.drop (k0 g))) (P.rd.muH + 4) := by
    rw [T5]
    rfl
  have c6 := Ld.c6
  rw [T6, hM, ← hr] at c6
  obtain ⟨_, rfl, rfl⟩ := some_triple.mp (c4'.symm.trans c6)
  have fr := Ld.front
  unfold mergeFront at fr
  rw [if_pos hg] at fr
  obtain ⟨_, rfl, rfl⟩ := some_triple.mp (d2.symm.trans fr)
  exact ⟨TS, cp, cE, e6, e7, eE, e8, e9⟩

/-- **The merge's call on the record's list with the embedding's claim behind it**: where the
hearing returns in the first group, Ld names its ledgers and tapes, and X has the text's environment
of claims and the plan's reads. -/
theorem ledG_merge_pub34
    (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hg : (g == 0) = true)
    {K : Type} [Field K] (X : Rows.Pub34 K)
    (Xc : X.c = { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := tT.r })
    (Xrd : X.rd = P.rd) :
    ∃ cE : WsClaim, (envOf P o).claimE o.H.ZE o.H.tkh P.V P.tokv = some cE ∧
      (X.cl ++ [cE]).toArray.size = hp.NCL ∧
      flatForkEnd P.wsLay (X.cl ++ [cE]).toArray
        ((Array.range (hp.NCL - 1)).map (o.K.sV + ·) ++ #[o.sVE]) G5 u5 = some (o.wo, G, u) := by
  obtain ⟨TS, cp, cE, e1, e2, eE, e3, e5⟩ := ledG_merge Ld h hg
  have Xc' : X.c = envOf P o := Xc.trans (envOf_at Ld.kTT).symm
  have Xy : X.p.v.y = P.y := by
    rw [X.env, Xc]
    exact (hear_parts_first h hg).2.1
  obtain ⟨_, rfl⟩ := cl_of_pub34 X e1 e2 Xc' Xrd Xy
  exact ⟨cE, eE, e3, e5⟩

/-- **What the merge's text has tested and left, at that list and LedG's tape**, under the premises
of `ledG_merge_pub34`. -/
theorem ledG_flat (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hg : (g == 0) = true)
    {K : Type} [Field K] (X : Rows.Pub34 K)
    (Xc : X.c = { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := tT.r })
    (Xrd : X.rd = P.rd) :
    ∃ cE : WsClaim, (envOf P o).claimE o.H.ZE o.H.tkh P.V P.tokv = some cE ∧
      (X.cl ++ [cE]).toArray.size = hp.NCL ∧
      FlatSpec P.wsLay (X.cl ++ [cE]).toArray
        ((Array.range (hp.NCL - 1)).map (o.K.sV + ·) ++ #[o.sVE]) u5 o.wo := by
  obtain ⟨cE, eE, e3, e5⟩ := ledG_merge_pub34 Ld h hg X Xc Xrd
  exact ⟨cE, eE, e3, flat_spec e5⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ledG_merge
#print axioms OnBytes.Road.K4.ledG_merge_pub34
#print axioms OnBytes.Road.K4.ledG_flat
