-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnLedgers.lean: THE CALLS OF K4's HEARING IN A GROUP THAT IS NOT THE FIRST, EACH ON
ITS NAMED TAPE, WITH WHAT IS KNOWN OF THE LEDGERS BETWEEN THEM. A record and three statements with
their proofs.

`own_calls6` (Johnson/Road/K4/OwnRecs.lean) names six calls on the tapes that the chain's
data read (`ksOf P hp`, `Ks.tc1` … `Ks.tcW`); its ledgers stand under "there are", and its record
`Chain7` ties them to the ledger in front by the runs that lay the sums', the products' and the
terms' row's values. To say what a ledger shows under a slot one needs more: that each ledger
between has arrays of the right sizes, and which ledger is later than which.

  `stack_target`: the batched sumcheck's record's target is the public part of the start form that
    the text made. `tsc_cl_shown`: where a token sumcheck returns from a ledger with arrays of the
    right sizes, every later ledger shows the claimed sum that it was sent.
  `Led7`: the record: the six calls as `own_calls6` has them (the sixth returns on the tape `tcW`);
    the seventh, the merge's, on that tape, its list of claims under "there is"; the norms' and the
    terms' stretches as two calls, the first from the ledger and the tape in front; the equations by
    which the sums' and the products' scalars are laid, each with the list that the tape's round
    sent, and the first slot of each run (sW, sPv); that the norms' two lists of powers are those of
    the elements that these rounds drew; the lengths of the two joins' points; that each of the nine
    ledgers between (F4 F7 F8 G1 G1' G2 G3 G3' G4) has arrays of the right sizes (`Sized`); that G2,
    at which the batched sumcheck begins, is later than the ledger in front and than G1'; G3' later
    than G3, G4 later than G3'; that the ledger which the hearing leaves is later than each ledger
    that a call returns; the eight fields of the norms' record that the later stretches keep (ztF
    among them), and the field in which the terms' record lies, with its mark that the row is made;
    that the second gated layer's record is there, and that the challenge of the terms' sumcheck is
    not the word 0.
  `own_led7`: where `hear` returns over the plain engine in such a group, from a ledger with arrays
    of the right sizes: there are ledgers and records with `Led7`.

The proof's first half is `own_calls6`'s, typed again with more of the parts' facts kept.

Limits. One direction: from a return. The ledgers stand under "there are"; the calls' equations fix
them. A group that is not the first. What the words mean is not said.
-/
import Johnson.Road.K4.OwnRecs
import OnBytes.Desc.First.K4.TermsShown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized hideRun_ok)
open OnBytes.Desc.First.Grow (Grows)
open OnBytes.Desc.First.P1 (drawnOf sentOf Ks tscIn_heard tapeEps tapeCl pscRow_spec)

/-- **The batched sumcheck's target**: where `hearStack` returns, the target of the record behind
its rounds is the public part, at the ledger handed in, of the start form that the text made. -/
theorem stack_target {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {S : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (S, G, u)) :
    F.publicPart (stackStart v H F t) = some (stackRec v H lamS F t).target := by
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, G1, ms, y, p, ht, _, _, hC, hT,
    _⟩ := hearStack_tape h
  have q0 : tapeEps t = x := by
    rw [ht]
    rfl
  have q5 : stackStart v H F t = C := by
    unfold stackStart
    rw [q0, hC, Option.map_some, Option.getD_some]
  rw [(stack_ended h).target, q5, hT, Option.getD_some]

/-- **Every later ledger shows the claimed sum that a token sumcheck was sent**, under the slot of
that sum: where the sumcheck returns from a ledger with arrays of the right sizes. -/
theorem tsc_cl_shown {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (hF : Sized F) (h : Fl.tscIn P lt n dY F t = some (o, G, u)) (Hl : Fork)
    (hL : Fo.Later G Hl) : Hl.vp.getD o.sCl zeroE = tapeCl t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsCl, _, _, v, G0, hG0, _, _, _, _, hG⟩ := tscIn_heard h
  have hF' : Sized ({ F with next := F.next + 1 } : Fork) := hF
  obtain ⟨_, hS0, hin, _⟩ := hideRun_ok _ G0 F.next _ oneE hF' hG0
  have hS0' : Sized ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } :
      Fork) := hS0
  have l2 : Fo.Later G0
      ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork) :=
    ⟨by show G0.next ≤ G0.next + 1 + 2 * (P.toList.take lt).length + dY + n; omega, rfl,
      fun _ hj => ⟨hj, rfl, rfl⟩⟩
  have l3 := Fo.hideRun_later hS0' hG
  have q := hin 0 Nat.zero_lt_one
  rw [Nat.add_zero] at q
  rw [hsCl, (((l2.trans l3).trans hL).keep F.next q.2.2.1).2.1, q.2.2.2.1]
  rfl

/-- The calls on their named tapes, and the ledgers between them. -/
structure Led7 (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (o : Own) (F G : Fork)
    (t0 u : Tape) (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork) :
    Prop where
  eHd2 : o.hd2 = some hd2
  ztF : o.H.ztF = H1.ztF
  eps : isZeroE tT.p.eps = false
  sW : H1.sW = F.next
  runW : ∃ vW : Array E, vW.toList = sentOf (t0.drop 1) ∧ vW.size = ledNS P.y.h.xl * P.y.NI ∧
    ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork).hideRun F.next vW oneE = some F4
  gp : H1.gp = powers (tapeEps (t0.drop 1)) (ledNS P.y.h.xl)
  lI : (drawnOf ((t0.drop 1).drop 1)).length = P.rd.lNI
  c1 : ∃ v1, Fl.levelIn P.rd.muV
      (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
      (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
      (orderDefault P.rd.muV) F4 ((ksOf P hp).tc1 (t0.drop 1)) = some (H1.wpl, F7, v1)
  c2 : ∃ v2, Fl.tscIn H1.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F8
      (((ksOf P hp).tcP (t0.drop 1)).drop 1) = some (H1.tV, G1, v2)
  c3 : Fl.tscIn H1.ztF P.y.h.lt (nEndT P.y) 1 G1
      ((((ksOf P hp).tcP (t0.drop 1)).drop 1).drop (P.y.h.lt + 3)) =
    some (tT, G1', (ksOf P hp).tc4 (t0.drop 1))
  nt : ∃ u1, hearNorms engFl P g fo F t0 = some (H1, G1, u1) ∧
    hearTerms engFl P H1 G1 u1 = some (o.H, G2, (ksOf P hp).tc4 (t0.drop 1))
  c4 : hearStack engFl P o.v o.H hp.lamS (hp.NCL - 0) G2 ((ksOf P hp).tc4 (t0.drop 1)) =
    some (o.K, G3, (ksOf P hp).tc5 (t0.drop 1))
  c5 : ∃ v5, Fl.levelIn P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
      (orderRange P.rd.muH) G3 ((ksOf P hp).tc5 (t0.drop 1)) = some (o.hd, G3', v5)
  lM : (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).length =
    P.y.h.ll - 1
  c6 : Fl.levelIn P.rd.muH2
      ((drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray ++
        downFrom o.K.rs P.y.lfe ++ tT.r)
      (Road.Rows.start2 P.y.LamM o.K.sH1
        (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray)
      (orderRange P.rd.muH2) G3' ((ksOf P hp).tc6 (t0.drop 1)) =
    some (hd2, G4, (ksOf P hp).tcW (t0.drop 1))
  c7 : ∃ cl, flatForkEnd P.wsLay cl ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]) G4
      ((ksOf P hp).tcW (t0.drop 1)) = some (o.wo, G, u)
  s4 : Sized F4
  s8 : Sized F8
  s1 : Sized G1
  s2 : Sized G2
  s3 : Sized G3
  s3' : Sized G3'
  sG4 : Sized G4
  l1 : Fo.Later G1' G2
  l2 : Fo.Later F G2
  l3 : Fo.Later G3 G3'
  l4 : Fo.Later G3' G4
  g7 : Fo.Later F7 G
  g1 : Fo.Later G1 G
  g1' : Fo.Later G1' G
  g2 : Fo.Later G2 G
  g3 : Fo.Later G3 G
  g3' : Fo.Later G3' G
  g4 : Fo.Later G4 G
  kWpl : o.H.wpl = H1.wpl
  kTV : o.H.tV = H1.tV
  kSW : o.H.sW = H1.sW
  kSPv : o.H.sPv = H1.sPv
  kGp : o.H.gp = H1.gp
  kOmV : o.H.omV = H1.omV
  kPV : o.H.PV = H1.PV
  kTT : o.H.tT = some { tT with p := { tT.p with rowMade := true } }
  sPv : H1.sPv = F7.next
  runP : ∃ vP : Array E, vP.toList = sentOf ((ksOf P hp).tcP (t0.drop 1)) ∧
    vP.size = ledNP P.y.h.xl * P.y.NI ∧
    ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork).hideRun F7.next vP oneE =
      some F8
  omV : H1.omV = powers (tapeEps ((ksOf P hp).tcP (t0.drop 1))) (ledNP P.y.h.xl * P.y.NI)
  s7 : Sized F7
  s1' : Sized G1'

/-- **Where the hearing returns in a group that is not the first**, from a ledger with arrays of the
right sizes. -/
theorem own_led7 {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} (hF : Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hg : (g == 0) = false) :
    ∃ (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork),
      Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 := by
  obtain ⟨_, _, _, _, _, H1, hd2, TS, cp, G1, G2, G3, G4, u1, u2, u3, u4, h1, h2, h3, h4, e5, _, _,
    _, h7⟩ := hear_parts_later h hg
  obtain ⟨F4, F7, F8, rhoI, vW, vP, gam, om, w0, wI, d0, dI, _, _, _, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := hearNorms_tape h1
  obtain ⟨tT, G1', u1', row, p', b1, b2, b3, b4⟩ := hearTerms_calls h2
  obtain ⟨tT', G3', c1, c2, c3, c4⟩ := hearGated_tape h4
  have hk0 : k0 g = 1 := by
    unfold k0
    rw [hg]
    rfl
  rw [hk0] at a4 a9 a12 a13 a18 a19
  -- the lengths of the two token points
  have l2 : (H1.PV.toList.take P.y.h.lt).length = P.y.h.lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left (tscIn_heard a18).1
  have l3 : (H1.ztF.toList.take P.y.h.lt).length = P.y.h.lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left (tscIn_heard b1).1
  -- the tapes
  have T0 : (t0.drop 1).drop 1 = t0.drop (1 + 1) := drop_drop' 1 1 t0
  have T1 : (ksOf P hp).tc1 (t0.drop 1) = t0.drop (1 + 2) := by
    unfold Ks.tc1
    rw [T0, drop_drop']
  have TP : (ksOf P hp).tcP (t0.drop 1) = t0.drop (1 + P.rd.muV + 6) := by
    unfold Ks.tcP
    rw [T1, drop_drop', drop_drop']
    congr 1
    show 1 + 2 + (P.rd.muV + 3) + 1 = _
    omega
  have T2 : ((ksOf P hp).tcP (t0.drop 1)).drop 1 = t0.drop (1 + P.rd.muV + 7) := by
    rw [TP, drop_drop']
  have hu1 : u1 = (((ksOf P hp).tcP (t0.drop 1)).drop 1).drop (P.y.h.lt + 3) := by
    rw [a19, l2, T2, drop_drop']
  have hu1' : u1' = u1.drop (P.y.h.lt + 3) := by
    have e := (tscIn_heard b1).2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [l3] at e
    exact e
  have hu2 : u2 = (ksOf P hp).tc4 (t0.drop 1) := by
    rw [(pscRow_spec b3).2.1, hu1', hu1]
    rfl
  have hu3 : u3 = (ksOf P hp).tc5 (t0.drop 1) := by
    rw [stack_rest h3, hu2]
    unfold Ks.tc5
    rw [drop_drop']
    congr 1
    show hp.lamS + 4 = 1 + (hp.lamS + 3)
    omega
  have T5 : (((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1 =
      u3.drop (P.rd.muH + 4) := by
    rw [hu3, drop_drop']
  have T6 : (ksOf P hp).tc6 (t0.drop 1) = u3.drop (P.rd.muH + 4 + 1) := by
    unfold Ks.tc6
    show ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1).drop 1 = _
    rw [T5, drop_drop']
  -- the two joins' points
  have hI : (drawnOf ((t0.drop 1).drop 1)).toArray = rhoI := by
    rw [T0, a9, a11]
    rfl
  have hM : drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1) =
      drawnAt u3 (P.rd.muH + 4) := by
    rw [T5]
    rfl
  -- what the terms' stretch keeps
  have hz : o.H.ztF = H1.ztF := by rw [b4]
  have hr : tT'.r = tT.r := by
    rw [b4] at c1
    rw [← Option.some.inj c1]
  -- the tape behind the second gated layer
  have e4 : P.rd.muH2 + 3 + 1 = P.rd.muH2 + 4 := rfl
  have TW : (ksOf P hp).tcW (t0.drop 1) = u4 := by
    show (((ksOf P hp).tc6 (t0.drop 1)).drop (P.rd.muH2 + 3)).drop 1 = _
    rw [T6, drop_drop', e4]
    exact (levelIn_rest c4).symm
  -- the ledgers
  have hF' : Sized ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork) := hF
  obtain ⟨_, S4, _, _⟩ := hideRun_ok _ F4 F.next vW oneE hF' a7
  have S7 : Sized F7 := (Grows.later a12).sized S4
  have hF7' : Sized ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork) := S7
  obtain ⟨_, S8, _, _⟩ := hideRun_ok _ F8 F7.next vP oneE hF7' a16
  have SG1 : Sized G1 := (Grows.later a18).sized S8
  have SG1' : Sized G1' := (Grows.later b1).sized SG1
  have SG2 : Sized G2 := (Grows.later b3).sized SG1'
  have SG3 : Sized G3 := (Grows.later h3).sized SG2
  have SG3' : Sized G3' := (Grows.later c2).sized SG3
  have SG4 : Sized G4 := (Grows.later c4).sized SG3'
  -- each ledger that a call returns, against the last
  have p4G : OnBytes.PscRun.Later G4 G := Grows.later h7
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
  refine ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, ?_⟩
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
      c6 := by rw [TW, T6, hM, ← hr]; exact c4
      c7 := ⟨_, by rw [TW]; exact h7⟩
      s4 := S4
      s8 := S8
      s1 := SG1
      s2 := SG2
      s3 := SG3
      s3' := SG3'
      sG4 := SG4
      l1 := later_fo (Grows.later b3)
      l2 := later_terms h1 h2
      l3 := later_fo (Grows.later c2)
      l4 := later_fo (Grows.later c4)
      g7 := later_fo p7G
      g1 := later_fo p1G
      g1' := later_fo p1'G
      g2 := later_fo p2G
      g3 := later_fo p3G
      g3' := later_fo p3'G
      g4 := later_fo p4G
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
      omV := by rw [a17, TP, a13]; rfl
      s7 := S7
      s1' := SG1' }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.own_led7
#print axioms OnBytes.Road.K4.stack_target
#print axioms OnBytes.Road.K4.tsc_cl_shown
