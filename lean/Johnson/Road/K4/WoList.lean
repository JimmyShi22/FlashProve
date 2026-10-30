-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/WoList.lean: WHICH LIST OF CLAIMS K4's hearing hands to the merge, in a group that
is not the first, at the ledger and on the tape that `Led7` names. `Led7.c7`
(Johnson/Road/K4/OwnLedgers.lean) says "there is a list cl on which `flatForkEnd` returned". Here
the list is named: it is what `weightClaims` returns at the plan's calls, which is `mergeClaims`
(OnBytes/Desc/First/K4/MergeClaims.lean), and it is the list X.cl of a public record `Pub34`
(Johnson/Road/Rows/LayerEnds34.lean) whose environment of claims is the text's and whose reads are
the plan's. Statements and proofs.

  `envOf_at`: the text's environment of claims, where the second token sumcheck is there.
  `mergeClaims_later`: in a later group `mergeClaims` is what `weightClaims` returns, as an array.
  `led7_merge`: the merge's call at Led7's own ledger G4 and tape, on the named list.
  `cl_of_pub34`: the record's calls and claims are those that the text's two functions return.
  `led7_merge_pub34`: the merge's call on X.cl.toArray; X.cl has hp.NCL members.
  `led7_flat`: so `FlatSpec` (Johnson/Road/K4/WoRecs.lean) at X.cl.toArray and Led7's tape.

HOW. No new argument. The hearing's calls are functions: `hear_parts_later` (HearParts.lean) keeps
the list and has its ledgers and tapes under "there are"; Led7 names them; call by call, equal
arguments give equal returns.

Limits. One direction: from a return. A group that is not the first. Premises on X, in
`led7_merge_pub34` and `led7_flat`: its environment of claims is the text's, with the end point of
Led7's second token sumcheck; its reads are the plan's. (That its layout is the plan's follows:
X.env, and the hearing's o.v.y = P.y. In `cl_of_pub34`, which knows no hearing, it is a premise.)
That there is such an X is not said. What a claim is worth is not said. Nothing on a draw or on
soundness.


-/
import Johnson.Road.K4.OwnLedgers
import Johnson.Road.K4.WoRecs
import Johnson.Road.Rows.LayerEnds34
import OnBytes.Desc.First.K4.MergeClaims

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
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- The text's environment of claims, where the second token sumcheck is there. -/
theorem envOf_at {tT' : Tsc} (h : o.H.tT = some tT') :
    envOf P o =
      { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := tT'.r } := by
  unfold envOf
  rw [h]
  rfl

/-- In a later group, where `callsTS` returns TS and `weightClaims` returns cp at TS, the merge's
claims are cp, as an array. -/
theorem mergeClaims_later {TS : List Nat} {cp : List WsClaim} (hg : (g == 0) = false)
    (e1 : callsTS P = some TS) (e2 : (envOf P o).weightClaims TS = some cp) :
    mergeClaims P g o = some cp.toArray := by
  have hg' : ¬ (g == 0) = true := by
    rw [hg]
    exact Bool.false_ne_true
  unfold mergeClaims
  rw [e1, Option.bind_some, e2, Option.bind_some, if_neg hg']
  show some (cp ++ []).toArray = _
  rw [List.append_nil]

/-- **The merge's call at Led7's ledger and tape, on the named list**: where the hearing returns in
a later group, and Ld names its ledgers and tapes. -/
theorem led7_merge (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hg : (g == 0) = false) :
    ∃ (TS : List Nat) (cp : List WsClaim),
      callsTS P = some TS ∧ (envOf P o).weightClaims TS = some cp ∧
      cp.toArray.size = hp.NCL ∧ mergeClaims P g o = some cp.toArray ∧
      flatForkEnd P.wsLay cp.toArray ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]) G4
        ((ksOf P hp).tcW (t0.drop 1)) = some (o.wo, G, u) := by
  obtain ⟨_, _, _, _, _, H1', hd2', TS, cp, A1, A2, A3, A4, u1, u2, u3, u4, h1, h2, h3, h4, _, e6,
    e7, e8, e9⟩ := hear_parts_later h hg
  obtain ⟨v1, n1, n2⟩ := Ld.nt
  obtain ⟨rfl, rfl, rfl⟩ := some_triple.mp (h1.symm.trans n1)
  obtain ⟨_, rfl, rfl⟩ := some_triple.mp (h2.symm.trans n2)
  obtain ⟨_, rfl, rfl⟩ := some_triple.mp (h3.symm.trans Ld.c4)
  obtain ⟨tT', B, c1, c2, _, c4⟩ := hearGated_tape h4
  obtain ⟨v5, d5⟩ := Ld.c5
  obtain ⟨_, rfl, _⟩ := some_triple.mp (c2.symm.trans d5)
  have hT := Option.some.inj (c1.symm.trans Ld.kTT)
  have hr : tT'.r = tT.r := by rw [hT]
  have T5 : (((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1 =
      ((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 4) := drop_drop' _ _ _
  have T6 : (ksOf P hp).tc6 (t0.drop 1) =
      ((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 4 + 1) := by
    unfold Ks.tc6
    show ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1).drop 1 = _
    rw [T5, drop_drop']
  have hM : drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1) =
      drawnAt ((ksOf P hp).tc5 (t0.drop 1)) (P.rd.muH + 4) := by
    rw [T5]
    rfl
  have c6 := Ld.c6
  rw [T6, hM, ← hr] at c6
  obtain ⟨_, rfl, rfl⟩ := some_triple.mp (c4.symm.trans c6)
  rw [List.append_nil] at e8 e9
  exact ⟨TS, cp, e6, e7, e8, mergeClaims_later hg e6 e7, e9⟩

/-- **The record's calls and claims are TS and cp**, if `callsTS` returns TS, `weightClaims` returns
cp at TS in the text's environment, and X has that environment, the plan's reads and its layout. -/
theorem cl_of_pub34 {K : Type} [Field K] (X : Rows.Pub34 K) {TS : List Nat} {cp : List WsClaim}
    (e1 : callsTS P = some TS) (e2 : (envOf P o).weightClaims TS = some cp)
    (Xc : X.c = envOf P o) (Xrd : X.rd = P.rd) (Xy : X.p.v.y = P.y) :
    TS = X.TS ∧ cp = X.cl := by
  have hTS := X.hTS
  rw [Xrd, Xy] at hTS
  have eT : TS = X.TS := Option.some.inj (e1.symm.trans hTS)
  have hcl := X.hcl
  rw [Xc, ← eT, e2] at hcl
  exact ⟨eT, Option.some.inj hcl⟩

/-- **The merge's call on the record's list**: where the hearing returns in a later group, Ld names
its ledgers and tapes, and X has the text's environment of claims and the plan's reads. -/
theorem led7_merge_pub34 (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hg : (g == 0) = false)
    {K : Type} [Field K] (X : Rows.Pub34 K)
    (Xc : X.c = { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := tT.r })
    (Xrd : X.rd = P.rd) :
    X.cl.toArray.size = hp.NCL ∧ mergeClaims P g o = some X.cl.toArray ∧
      flatForkEnd P.wsLay X.cl.toArray ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]) G4
        ((ksOf P hp).tcW (t0.drop 1)) = some (o.wo, G, u) := by
  obtain ⟨TS, cp, e1, e2, e3, e4, e5⟩ := led7_merge Ld h hg
  have Xc' : X.c = envOf P o := Xc.trans (envOf_at Ld.kTT).symm
  have Xy : X.p.v.y = P.y := by
    rw [X.env, Xc]
    exact (hear_parts_later h hg).2.1
  obtain ⟨_, rfl⟩ := cl_of_pub34 X e1 e2 Xc' Xrd Xy
  exact ⟨e3, e4, e5⟩

/-- **What the merge's text has tested and left, at the record's list and Led7's tape**, under the
premises of `led7_merge_pub34`. -/
theorem led7_flat (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hg : (g == 0) = false)
    {K : Type} [Field K] (X : Rows.Pub34 K)
    (Xc : X.c = { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := tT.r })
    (Xrd : X.rd = P.rd) :
    FlatSpec P.wsLay X.cl.toArray ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[])
      ((ksOf P hp).tcW (t0.drop 1)) o.wo :=
  flat_spec (led7_merge_pub34 Ld h hg X Xc Xrd).2.2

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.envOf_at
#print axioms OnBytes.Road.K4.mergeClaims_later
#print axioms OnBytes.Road.K4.led7_merge
#print axioms OnBytes.Road.K4.cl_of_pub34
#print axioms OnBytes.Road.K4.led7_merge_pub34
#print axioms OnBytes.Road.K4.led7_flat
