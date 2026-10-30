-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnLedgersG.lean: THE CALLS OF K4's HEARING IN EVERY GROUP, EACH ON ITS NAMED TAPE,
WITH WHAT IS KNOWN OF THE LEDGERS BETWEEN THEM. A record and one statement with its proof. The twin,
for every group, of Johnson/Road/K4/OwnLedgers.lean, which treats a group that is not the first.

`own_callsG` (Johnson/Road/K4/OwnRecsG.lean) names the seven calls on the cuts of the tape behind
the points in front, `t0.drop (k0 g)` (three points in the first group, one in a later group); its
ledgers stand under "there are", and its record `Chain7` (Johnson/Road/K4/OwnRecs.lean) ties them to
the ledger in front by the runs that lay the sums', the products' and the terms' row's values. What
`LedG` has more: that each ledger between has arrays of the right sizes, which ledger is later than
which, the lengths of the two joins' points, and what stands between the gated layers and the
merge.

  `LedG`: the record: the fields of `Led7`, on these cuts; the batched sumcheck hears one end value
    fewer in the first group; between the gated layers and the merge stands `mergeFront`
    (OnBytes/Desc/First/K4/MergeClaims.lean): in the first group the embedding's hidden value is
    laid, in a later group nothing is done; the merge is called from the ledger G5 and the tape u5
    behind that, at the slots `mergeSlots`; u5 and the cut `tcW` have the same rounds behind the
    first and the same first drawn element; and, in the first group: the field for the embedding's
    slot holds G4's next slot, and every ledger later than G5 shows under it the first word that
    the round at the cut `tcW` sent.
  `own_ledG`: where `hear` returns over the plain engine, from a ledger with arrays of the right
    sizes: there are ledgers and records with `LedG`.

The proof's first half is `own_callsG`'s, typed again with more of the parts' facts kept.

Limits. One direction: from a return. The ledgers stand under "there are"; the calls' equations fix
them. Nothing on the two further points in front in the first group, nor on the embedding's claim.
What the words mean is not said.
-/
import Johnson.Road.K4.OwnRecsG
import OnBytes.Desc.First.K4.TermsShown
import OnBytes.Desc.First.K4.ShownUnder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (hideRun_ok)
open OnBytes.Desc.First.Grow (Grows)
open OnBytes.Desc.First.P1 (drawnOf sentOf Ks tscIn_heard tapeEps pscRow_spec claimsIn_spec)

/-- The calls on their named tapes, and the ledgers between them, in every group. -/
structure LedG (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (o : Own) (F G : Fork)
    (t0 u : Tape) (H1 : Heard) (hd2 : Level) (tT : Tsc)
    (F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork) (u5 : Tape) : Prop where
  eHd2 : o.hd2 = some hd2
  ztF : o.H.ztF = H1.ztF
  eps : isZeroE tT.p.eps = false
  sW : H1.sW = F.next
  runW : ∃ vW : Array E, vW.toList = sentOf (t0.drop (k0 g)) ∧ vW.size = ledNS P.y.h.xl * P.y.NI ∧
    ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork).hideRun F.next vW oneE = some F4
  gp : H1.gp = powers (tapeEps (t0.drop (k0 g))) (ledNS P.y.h.xl)
  lI : (drawnOf ((t0.drop (k0 g)).drop 1)).length = P.rd.lNI
  c1 : ∃ v1, Fl.levelIn P.rd.muV
      (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
      (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
      (orderDefault P.rd.muV) F4 ((ksOf P hp).tc1 (t0.drop (k0 g))) = some (H1.wpl, F7, v1)
  c2 : ∃ v2, Fl.tscIn H1.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F8
      (((ksOf P hp).tcP (t0.drop (k0 g))).drop 1) = some (H1.tV, G1, v2)
  c3 : Fl.tscIn H1.ztF P.y.h.lt (nEndT P.y) 1 G1
      ((((ksOf P hp).tcP (t0.drop (k0 g))).drop 1).drop (P.y.h.lt + 3)) =
    some (tT, G1', (ksOf P hp).tc4 (t0.drop (k0 g)))
  nt : ∃ u1, hearNorms engFl P g fo F t0 = some (H1, G1, u1) ∧
    hearTerms engFl P H1 G1 u1 = some (o.H, G2, (ksOf P hp).tc4 (t0.drop (k0 g)))
  c4 : hearStack engFl P o.v o.H hp.lamS (hp.NCL - (if (g == 0) = true then 1 else 0)) G2
      ((ksOf P hp).tc4 (t0.drop (k0 g))) = some (o.K, G3, (ksOf P hp).tc5 (t0.drop (k0 g)))
  c5 : ∃ v5, Fl.levelIn P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
      (orderRange P.rd.muH) G3 ((ksOf P hp).tc5 (t0.drop (k0 g))) = some (o.hd, G3', v5)
  lM : (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).length =
    P.y.h.ll - 1
  c6 : Fl.levelIn P.rd.muH2
      ((drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray ++
        downFrom o.K.rs P.y.lfe ++ tT.r)
      (Road.Rows.start2 P.y.LamM o.K.sH1
        (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray)
      (orderRange P.rd.muH2) G3' ((ksOf P hp).tc6 (t0.drop (k0 g))) =
    some (hd2, G4, (ksOf P hp).tcW (t0.drop (k0 g)))
  front : mergeFront g o G4 ((ksOf P hp).tcW (t0.drop (k0 g))) G5 u5
  c7 : ∃ cl, flatForkEnd P.wsLay cl (mergeSlots hp g o) G5 u5 = some (o.wo, G, u)
  u5d : u5.drop 1 = ((ksOf P hp).tcW (t0.drop (k0 g))).drop 1
  u5e : tapeEps u5 = tapeEps ((ksOf P hp).tcW (t0.drop (k0 g)))
  emb : (g == 0) = true → o.sVE = G4.next ∧ ∀ Hl : Fork, Fo.Later G5 Hl →
    Hl.vp.getD o.sVE zeroE = (sentOf ((ksOf P hp).tcW (t0.drop (k0 g)))).getD 0 zeroE
  s4 : PscRun.Sized F4
  s7 : PscRun.Sized F7
  s8 : PscRun.Sized F8
  s1 : PscRun.Sized G1
  s1' : PscRun.Sized G1'
  s2 : PscRun.Sized G2
  s3 : PscRun.Sized G3
  s3' : PscRun.Sized G3'
  sG4 : PscRun.Sized G4
  sG5 : PscRun.Sized G5
  l1 : Fo.Later G1' G2
  l2 : Fo.Later F G2
  l3 : Fo.Later G3 G3'
  l4 : Fo.Later G3' G4
  l5 : Fo.Later G4 G5
  g7 : Fo.Later F7 G
  g1 : Fo.Later G1 G
  g1' : Fo.Later G1' G
  g2 : Fo.Later G2 G
  g3 : Fo.Later G3 G
  g3' : Fo.Later G3' G
  g4 : Fo.Later G4 G
  g5 : Fo.Later G5 G
  kWpl : o.H.wpl = H1.wpl
  kTV : o.H.tV = H1.tV
  kSW : o.H.sW = H1.sW
  kSPv : o.H.sPv = H1.sPv
  kGp : o.H.gp = H1.gp
  kOmV : o.H.omV = H1.omV
  kPV : o.H.PV = H1.PV
  kTT : o.H.tT = some { tT with p := { tT.p with rowMade := true } }
  sPv : H1.sPv = F7.next
  runP : ∃ vP : Array E, vP.toList = sentOf ((ksOf P hp).tcP (t0.drop (k0 g))) ∧
    vP.size = ledNP P.y.h.xl * P.y.NI ∧
    ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork).hideRun F7.next vP oneE =
      some F8
  omV : H1.omV = powers (tapeEps ((ksOf P hp).tcP (t0.drop (k0 g)))) (ledNP P.y.h.xl * P.y.NI)

/-- **Where the hearing returns**, in whichever group, from a ledger with arrays of the right
sizes. -/
theorem own_ledG {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} (hF : PscRun.Sized F)
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) :
    ∃ (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork) (u5 : Tape),
      LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5 := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, h1, h2, h3, h4, e5, e6,
    e7, e8, e9⟩ := hear_parts h
  obtain ⟨F4, F7, F8, rhoI, vW, vP, gam, om, w0, wI, d0, dI, _, _, _, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := hearNorms_tape h1
  obtain ⟨tT, G1', u1', row, p', b1, b2, b3, b4⟩ := hearTerms_calls h2
  obtain ⟨tT', G3', c1, c2, c3, c4⟩ := hearGated_tape h4
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
  -- the ledgers
  have hF' : PscRun.Sized ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork) := hF
  obtain ⟨_, S4, _, _⟩ := hideRun_ok _ F4 F.next vW oneE hF' a7
  have S7 : PscRun.Sized F7 := (Grows.later a12).sized S4
  have hF7' : PscRun.Sized ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork) := S7
  obtain ⟨_, S8, _, _⟩ := hideRun_ok _ F8 F7.next vP oneE hF7' a16
  have SG1 : PscRun.Sized G1 := (Grows.later a18).sized S8
  have SG1' : PscRun.Sized G1' := (Grows.later b1).sized SG1
  have SG2 : PscRun.Sized G2 := (Grows.later b3).sized SG1'
  have SG3 : PscRun.Sized G3 := (Grows.later h3).sized SG2
  have SG3' : PscRun.Sized G3' := (Grows.later c2).sized SG3
  have SG4 : PscRun.Sized G4 := (Grows.later c4).sized SG3'
  have p45 : OnBytes.PscRun.Later G4 G5 := by
    unfold mergeFront at e6
    by_cases hg : (g == 0) = true
    · rw [if_pos hg] at e6
      exact Grows.later e6
    · rw [if_neg hg] at e6
      rw [e6.2.1]
      exact OnBytes.PscRun.Later.refl G4
  have SG5 : PscRun.Sized G5 := p45.sized SG4
  -- each ledger that a call returns, against the last
  have p5G : OnBytes.PscRun.Later G5 G := Grows.later e9
  have p4G := p45.trans p5G
  have p3'G := (Grows.later c4).trans p4G
  have p3G := (Grows.later c2).trans p3'G
  have p2G := (Grows.later h3).trans p3G
  have p1'G := (Grows.later b3).trans p2G
  have p1G := (Grows.later b1).trans p1'G
  have p8G := (Grows.later a18).trans p1G
  have p7G : OnBytes.PscRun.Later F7 G :=
    ((OnBytes.Desc.First.Grow.later_next F7 _).trans
      (OnBytes.PscRun.hideRun_later hF7' a16)).trans p8G
  have hp' : p' = { tT.p with rowMade := true } := (pscRow_some b3).2
  -- the embedding's hidden value
  have hemb : (g == 0) = true → o.sVE = G4.next ∧ ∀ Hl : Fork, Fo.Later G5 Hl →
      Hl.vp.getD o.sVE zeroE = (sentOf u4).getD 0 zeroE := by
    intro hg
    have e6' := e6
    unfold mergeFront at e6'
    rw [if_pos hg] at e6'
    obtain ⟨hj, v, hs, et, hne, hrun⟩ := claimsIn_spec e6'
    refine ⟨hj, fun Hl hL => ?_⟩
    have hG4' : PscRun.Sized ({ G4 with next := G4.next + 1 } : Fork) := SG4
    have q := hideRun_shown hG4' hrun rfl hL 0 (by omega)
    rw [Nat.add_zero] at q
    rw [hj, q, et]
    cases u5 with
    | nil => exact absurd rfl (hne Nat.one_ne_zero)
    | cons r rest =>
      show v.toList.getD 0 zeroE = (v.toList ++ r.sent).getD 0 zeroE
      rw [List.getD_append _ _ _ _ (by rw [Array.length_toList]; omega)]
  refine ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, ?_⟩
  exact
    { eHd2 := e5
      ztF := hz
      eps := b2
      sW := a6
      runW := ⟨vW, by rw [a4]; rfl, a5, a7⟩
      gp := by rw [a8, a4]; rfl
      lI := by rw [T0, a9]; exact a10
      c1 := ⟨_, by rw [T1, hI]; exact a12⟩
      c2 := ⟨_, by rw [T2]; exact a18⟩
      c3 := by rw [← hu1, ← hu2, (pscRow_spec b3).2.1]; exact b1
      nt := ⟨u1, h1, by rw [← hu2]; exact h2⟩
      c4 := by rw [← hu2, ← hu3]; exact h3
      c5 := ⟨_, by rw [← hu3]; exact c2⟩
      lM := by rw [hM]; exact c3
      c6 := by rw [← hu4, T6, hM, ← hr]; exact c4
      front := by rw [← hu4]; exact e6
      c7 := ⟨cl, e9⟩
      u5d := by rw [h5.1, hu4]
      u5e := by rw [h5.2, hu4]
      emb := by rw [← hu4]; exact hemb
      s4 := S4
      s7 := S7
      s8 := S8
      s1 := SG1
      s1' := SG1'
      s2 := SG2
      s3 := SG3
      s3' := SG3'
      sG4 := SG4
      sG5 := SG5
      l1 := later_fo (Grows.later b3)
      l2 := later_terms h1 h2
      l3 := later_fo (Grows.later c2)
      l4 := later_fo (Grows.later c4)
      l5 := later_fo p45
      g7 := later_fo p7G
      g1 := later_fo p1G
      g1' := later_fo p1'G
      g2 := later_fo p2G
      g3 := later_fo p3G
      g3' := later_fo p3'G
      g4 := later_fo p4G
      g5 := later_fo p5G
      kWpl := by rw [b4]
      kTV := by rw [b4]
      kSW := by rw [b4]
      kSPv := by rw [b4]
      kGp := by rw [b4]
      kOmV := by rw [b4]
      kPV := by rw [b4]
      kTT := by rw [b4, hp']
      sPv := a15
      runP := ⟨vP, by rw [TP, a13]; rfl, a14, a16⟩
      omV := by rw [a17, TP, a13]; rfl }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.own_ledG
