-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnRecs.lean: WHERE THE HEARING OF THE LAYERS' OWN ROUNDS RETURNS IN A LATER GROUP,
THE RECORDS OF ITS FIRST SIX SUMCHECKS ARE THE LIBRARY's `RecAt`
(OnBytes/Tie/Pv/Lay/HearTieAll.lean) AT THE WORDS THAT THE CHAIN's DATA READ OFF THE TAPE (`pscT`,
`tailT`, OnBytes/Desc/First/P1/TailTape.lean). Definitions, statements and proofs.

`Recs7` says this of the routine `hearOwn` of the program `verify-on-bytes` in a context, at lists
under "there is". Here it is said of `hear` (OnBytes/Desc/First/K4/Hear.lean) over the plain
engine, at functions of the tape.

  `level_recAt`, `tsc_recAt`, `stack_recAt`: one product layer, one token sumcheck, the batched
    sumcheck: `RecAt` at `pscT`, from a return.
  `level_vals_len`, `tsc_vals_len`, `stack_vals_len`: how many end values the values' round sent (2;
    the call's number n; 2 + (1 + LamM) + the panels' claims). `RecAt`'s own last number is idle in
    this file: it is set to the length of the very list.
  `ksOf P hp`: K4's seven numbers of variables.
  `heardOf H1 tT`, `Chain7`: what ties the letters H1, tT and the ledgers between the calls to the
    hearing's record o, its first ledger F and the tape: o.H = heardOf H1 tT (H1 with the fields tT
    and KT laid by the terms' stretch); H1's PV, sW, gp, sPv, omV as words of the tape or numbers of
    the ledgers; the three runs of hidden values between the calls.
  `own_calls7`, `own_calls6`: from a return of `hear` on a tape t0 in a group that is not the first:
    the seven calls (the seventh: the merge's `flatForkEnd`, on `Ks.tcW`); the first six calls, each
    on its named tape: the cuts `Ks.tc1` … `Ks.tc6` of the tape behind the token point's round; and
    that the three words of the terms' coefficient are not all 0.
  `Recs6`, `own_recs6`: the six records, each with the weights of its rounds: `RecAt`. The four
    records that the text does not hand on are named: `levelRec`, `stackRec` at these tapes.

NO NEW ARGUMENT: `hear_parts_later` (HearParts.lean), `hearNorms_tape` (NormsTape.lean),
`hearTerms_calls` (HearCalls.lean), `stack_ended` (StackEnded.lean), `hearGated_tape`
(GatedTape.lean), `level_pscT`, `tsc_pscT` (HeardPsc.lean), and sums of numbers of rounds.

Limits. One direction: from a return. A group that is not the first. THE SEVENTH RECORD (the
merge's) IS NOT HERE. The rows that the text makes of four of the records are not spoken of
(LevelTieFlat.lean, StackTieFlat.lean). The ledgers stand under "there are"; `Chain7` and the calls
chain them from F to G. Whether anything here reaches a routine of the program `verify-on-bytes`
is for the walk by constants to say. Nothing on soundness.
-/
import OnBytes.Desc.First.P1.HeardPsc
import OnBytes.Desc.First.P1.LevelTieFlat
import OnBytes.Desc.First.P1.TokTieFlat
import OnBytes.Desc.First.K4.StackTieFlat
import OnBytes.Desc.First.K4.HearParts
import OnBytes.Desc.First.K4.NormsTape
import OnBytes.Desc.First.K4.HearCalls
import Johnson.Road.K4.GatedTape
import OnBytes.Tie.Pv.Lay.HearTieAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Tie.Pv.Lay (RecAt)
open OnBytes.Desc.First.P1 (pscT heardPairs pairs_congr drawnOf Ks levelWs levelRec levelRs levelY
  tscWs tscRs tscY plainWs level_pscT tsc_pscT level_sizes tsc_sizes levelIn_heard tscIn_heard
  tapeMu tapeEps tapeMu_eq roundAt pscRow_spec sentOf
  levelIn_tape tscIn_tape drop_second sentOf_cons levelVals tscVals)

/-! ### One sumcheck -/

theorem level_recAt {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    RecAt (pscT 0 mu t) (levelWs mu rho order) mu 2 (pscT 0 mu t).v.length
      (levelRec mu rho C order F t) := by
  have hw : (levelWs mu rho order).length = mu := by
    unfold levelWs
    rw [List.length_map]
    exact (levelIn_heard h).1
  have e3 := pairs_congr (levelWs mu rho order) (t.drop 1)
  rw [hw] at e3
  have e3' : levelRs mu rho order t = heardPairs mu (t.drop 1) := e3
  obtain ⟨z1, z2⟩ := level_sizes h
  refine ⟨⟨C, _, _, level_pscT h⟩, ?_, z2, rfl⟩
  show (heardPairs mu (t.drop 1)).map (·.1.length) = _
  rw [← e3', z1]
  refine List.eq_replicate_iff.2 ⟨by rw [List.length_map, hw], fun b hb => ?_⟩
  obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 hb
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hwm
  rfl

theorem tsc_recAt {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    RecAt (pscT 1 lt t) (tscWs (P.toList.take lt)) lt dY (pscT 1 lt t).v.length o.p := by
  have hl : (P.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left (tscIn_heard h).1
  have hw : (tscWs (P.toList.take lt)).length = lt := by
    unfold tscWs
    rw [List.length_map, hl]
  have e3 := pairs_congr (tscWs (P.toList.take lt)) (t.drop 1)
  rw [hw] at e3
  have e3' : tscRs P lt t = heardPairs lt (t.drop 1) := e3
  obtain ⟨z1, z2⟩ := tsc_sizes h
  have ey : tscY P lt dY t = roundAt (OnBytes.Psc.Weight.atZero (dY + 1)) (t.drop (lt + 1)) := by
    unfold tscY
    rw [hl]
  rw [ey] at z2
  refine ⟨⟨_, _, _, tsc_pscT h⟩, ?_, z2, rfl⟩
  show (heardPairs lt (t.drop 1)).map (·.1.length) = _
  rw [← e3', z1]
  refine List.eq_replicate_iff.2 ⟨by rw [List.length_map, hw], fun b hb => ?_⟩
  obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 hb
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hwm
  rfl

theorem stack_recAt {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {S : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (S, G, u)) :
    RecAt (pscT 0 lamS (t.drop 1)) (plainWs lamS) lamS 2 (pscT 0 lamS (t.drop 1)).v.length
      (stackRec v H lamS F t) := by
  have e := stack_ended h
  obtain ⟨z1, z2⟩ := stack_sizes h
  have d2 : (t.drop 1).drop 1 = t.drop 2 := drop_drop' 1 1 t
  have dy : (t.drop 1).drop (lamS + 1) = t.drop (lamS + 2) := by
    rw [drop_drop' 1 (lamS + 1) t]
    congr 1
    omega
  have e3 : (pscT 0 lamS (t.drop 1)).rs = stackRs lamS t := by
    show heardPairs lamS ((t.drop 1).drop 1) = _
    rw [d2]
    rfl
  have e4 : (pscT 0 lamS (t.drop 1)).sentY = (stackY lamS t).2.1 := by
    show (roundAt (OnBytes.Psc.Weight.atZero 1) ((t.drop 1).drop (lamS + 1))).2.1 = _
    rw [dy]
    rfl
  have e5 : (pscT 0 lamS (t.drop 1)).beta = (stackY lamS t).2.2 := by
    show (roundAt (OnBytes.Psc.Weight.atZero 1) ((t.drop 1).drop (lamS + 1))).2.2 = _
    rw [dy]
    rfl
  have e1 : (pscT 0 lamS (t.drop 1)).mu = tapeMu (t.drop 1) := (tapeMu_eq _).symm
  refine ⟨⟨stackStart v H F t, (F.publicPart (stackStart v H F t)).getD zeroE, F.next, ?_⟩, ?_, ?_,
    rfl⟩
  · rw [e1, e3, e4, e5]
    exact e
  · rw [e3, z1]
    show (List.replicate lamS (OnBytes.Psc.Weight.plain 3)).map _ = _
    rw [List.map_replicate]
    rfl
  · rw [e4]
    exact z2

/-! ### The numbers of end values

`RecAt`'s last number is idle above: it is the length of the very list. How many end values the
values' round sent is said here. -/

theorem level_vals_len {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    (pscT 0 mu t).v.length = 2 := by
  obtain ⟨hom, T, mu0, eps, rs, sentY, beta, tau, w0, wY, wV, wT, ms, y, shL, shR, v, G1, p, ht,
    hrs, _, htest, htau, hms, hyy, hp, hT, a1, hy, hheld, hlens, hvars, hr, hclaim, htar, heps,
    hstart, hfirst, hrow, hLr, hsL, hsR, hv2, hG1, hshL, hshR, hG⟩ := levelIn_tape h
  have hvt : v.toList = levelVals mu t := by
    unfold levelVals
    rw [ht, ← hrs, drop_second, sentOf_cons]
  show (levelVals mu t).length = 2
  rw [← hvt, Array.length_toList, hv2]

theorem tsc_vals_len {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) : (pscT 1 lt t).v.length = n := by
  obtain ⟨hlt, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, G0, ht, hrs, _, hms, hyy,
    hv1c, hsCl, hv1, hG0, hT, a1, hy, hheld, hlens, hvars, hr, hclaim, htar, heps, hstart, hfirst,
    hor, hsEnd, hvn, hG⟩ := tscIn_tape h
  have hvt : v.toList = tscVals P lt t := by
    unfold tscVals
    rw [ht, ← hrs, drop_second, sentOf_cons]
  have hl : (P.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left hlt
  have e : (pscT 1 lt t).v = tscVals P lt t := by
    unfold tscVals
    rw [hl]
    rfl
  rw [e, ← hvt, Array.length_toList, hvn]

theorem stack_vals_len {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {S : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (S, G, u)) :
    (pscT 0 lamS (t.drop 1)).v.length = 2 + (1 + P.y.LamM) + NCLp := by
  obtain ⟨_, _, _, _, _, vals, G1, hv, hn, _⟩ := stack_heard h
  have e : (pscT 0 lamS (t.drop 1)).v = stackVals lamS t := by
    show sentOf ((t.drop 1).drop (lamS + 2)) = sentOf (t.drop (lamS + 3))
    rw [drop_drop' 1 (lamS + 2) t]
    congr 2
    omega
  rw [e, ← hv, Array.length_toList, hn]

/-! ### The six -/

/-- K4's seven numbers of variables. -/
def ksOf (P : Pub) (hp : HPlan2) : Ks :=
  ⟨P.rd.muV, P.y.h.lt, P.y.h.lt, hp.lamS, P.rd.muH, P.rd.muH2, P.wsLay.lk⟩

/-- The first six sumchecks' records, at the words that the chain's data read off the tape t behind
the token point's round. -/
structure Recs6 (P : Pub) (hp : HPlan2) (o : Own) (H1 : Heard) (tT : Tsc) (hd2 : Level) (t : Tape)
    (p1 p4 p5 p6 : Psc) : Prop where
  r1 : RecAt (pscT 0 P.rd.muV ((ksOf P hp).tc1 t))
    (levelWs P.rd.muV (normsStart P.y H1.sW H1.gp (drawnOf (t.drop 1)).toArray H1.PV).2
      (orderDefault P.rd.muV)) P.rd.muV 2 (pscT 0 P.rd.muV ((ksOf P hp).tc1 t)).v.length p1
  r2 : RecAt (pscT 1 P.y.h.lt (((ksOf P hp).tcP t).drop 1)) (tscWs (H1.PV.toList.take P.y.h.lt))
    P.y.h.lt 2 (pscT 1 P.y.h.lt (((ksOf P hp).tcP t).drop 1)).v.length H1.tV.p
  r3 : RecAt (pscT 1 P.y.h.lt ((((ksOf P hp).tcP t).drop 1).drop (P.y.h.lt + 3)))
    (tscWs (H1.ztF.toList.take P.y.h.lt)) P.y.h.lt 1
    (pscT 1 P.y.h.lt ((((ksOf P hp).tcP t).drop 1).drop (P.y.h.lt + 3))).v.length tT.p
  r4 : RecAt (pscT 0 hp.lamS (((ksOf P hp).tc4 t).drop 1)) (plainWs hp.lamS) hp.lamS 2
    (pscT 0 hp.lamS (((ksOf P hp).tc4 t).drop 1)).v.length p4
  r5 : RecAt (pscT 0 P.rd.muH ((ksOf P hp).tc5 t))
    (levelWs P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (orderRange P.rd.muH)) P.rd.muH 2
    (pscT 0 P.rd.muH ((ksOf P hp).tc5 t)).v.length p5
  r6 : RecAt (pscT 0 P.rd.muH2 ((ksOf P hp).tc6 t))
    (levelWs P.rd.muH2
      ((drawnOf ((((ksOf P hp).tc5 t).drop (P.rd.muH + 3)).drop 1)).toArray ++
        downFrom o.K.rs P.y.lfe ++ tT.r) (orderRange P.rd.muH2)) P.rd.muH2 2
    (pscT 0 P.rd.muH2 ((ksOf P hp).tc6 t)).v.length p6

/-- The record behind the making of a row: the mark alone turns. (`pscRow_rec`,
Johnson/Road/K4/HearSlots.lean, says the same; typed again here so that this file does not hang on
that one.) -/
theorem pscRow_made {p p' : Psc} {S0 : E} {kept f : Aff} {F G : Fork} {t u : Tape}
    (h : Fl.pscRow p S0 kept F t = some ((f, p'), G, u)) : p' = { p with rowMade := true } := by
  unfold Fl.pscRow at h
  obtain ⟨_, G1, u1, h1, k20⟩ := OnBytes.Desc.First.P1.bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := OnBytes.Desc.First.P1.must_some.mp h1
  obtain ⟨_, G2, u2, h2, k21⟩ := OnBytes.Desc.First.P1.bind_some.mp k20
  obtain ⟨_, rfl⟩ := OnBytes.Desc.First.P1.change_some.mp h2
  obtain ⟨he, _, _⟩ := OnBytes.Desc.First.P1.pure_some.mp k21
  injection he with e1 e2
  exact e2.symm

/-- **What the hearing's record holds of the norms' and the terms' stretches**: the norms' record H1
with two fields laid by the terms' stretch: the terms' token sumcheck tT, its record marked as one
whose row is made; and the form KT. All other fields are H1's. -/
def heardOf (H1 : Heard) (tT : Tsc) : Heard :=
  { H1 with tT := some { tT with p := { tT.p with rowMade := true } },
            KT := (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps)) }

/-- Behind the batched sumcheck's rounds. -/
theorem stack_rest {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {S : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (S, G, u)) :
    u = t.drop (lamS + 4) := by
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, G1, ms, y, p, ht, hrs, _⟩ :=
    hearStack_tape h
  rw [ht, ← hrs, drop_succ_cons', OnBytes.Desc.First.P1.drop_tsc]

/-- **What ties the letters of the calls to the hearing's record, its first ledger and the tape.**
tb: the tape behind the points in front. So H1 and tT are no free letters: o.H is made of them; H1's
fields that the calls read are words of the tape or numbers of the ledgers; and the ledgers between
the calls come from one another by the runs named here. -/
structure Chain7 (P : Pub) (hp : HPlan2) (F : Fork) (t0 tb : Tape) (o : Own) (H1 : Heard)
    (tT : Tsc) (F4 F7 F8 G1' G2 : Fork) : Prop where
  heard : o.H = heardOf H1 tT
  pv : H1.PV = (drawnOf t0).toArray
  sW : H1.sW = F.next
  runW : ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork).hideRun F.next
    (sentOf tb).toArray oneE = some F4
  gp : H1.gp = powers (tapeEps tb) (ledNS P.y.h.xl)
  sPv : H1.sPv = F7.next
  runP : ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork).hideRun F7.next
    (sentOf ((ksOf P hp).tcP tb)).toArray oneE = some F8
  omV : H1.omV = powers (tapeEps ((ksOf P hp).tcP tb)) (ledNP P.y.h.xl * P.y.NI)
  rowT : G1'.hideRun tT.p.first (Array.replicate tT.p.walk.1.length zeroE) (subE zeroE oneE) =
    some G2

/-- **The seven calls, each on its named tape, where the hearing returns in a group that is not the
first.** The tapes are cuts of the tape behind the token point's round. -/
theorem own_calls7 {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hg : (g == 0) = false) :
    ∃ (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork)
      (v1 v2 v5 u4 : Tape),
      o.hd2 = some hd2 ∧ o.H.ztF = H1.ztF ∧ isZeroE tT.p.eps = false ∧
      Fl.levelIn P.rd.muV
          (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
          (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
          (orderDefault P.rd.muV) F4 ((ksOf P hp).tc1 (t0.drop 1)) = some (H1.wpl, F7, v1) ∧
      Fl.tscIn H1.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F8
          (((ksOf P hp).tcP (t0.drop 1)).drop 1) = some (H1.tV, G1, v2) ∧
      Fl.tscIn H1.ztF P.y.h.lt (nEndT P.y) 1 G1
          ((((ksOf P hp).tcP (t0.drop 1)).drop 1).drop (P.y.h.lt + 3)) =
        some (tT, G1', (ksOf P hp).tc4 (t0.drop 1)) ∧
      hearStack engFl P o.v o.H hp.lamS (hp.NCL - 0) G2 ((ksOf P hp).tc4 (t0.drop 1)) =
        some (o.K, G3, (ksOf P hp).tc5 (t0.drop 1)) ∧
      Fl.levelIn P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
          (orderRange P.rd.muH) G3 ((ksOf P hp).tc5 (t0.drop 1)) = some (o.hd, G3', v5) ∧
      Fl.levelIn P.rd.muH2
          ((drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray ++
            downFrom o.K.rs P.y.lfe ++ tT.r)
          (Road.Rows.start2 P.y.LamM o.K.sH1
            (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray)
          (orderRange P.rd.muH2) G3' ((ksOf P hp).tc6 (t0.drop 1)) = some (hd2, G4, u4) ∧
      Chain7 P hp F t0 (t0.drop 1) o H1 tT F4 F7 F8 G1' G2 ∧ u4 = (ksOf P hp).tcW (t0.drop 1) ∧
      ∃ (TS : List Nat) (claimsP : List WsClaim),
        callsTS P = some TS ∧ (envOf P o).weightClaims TS = some claimsP ∧
        (claimsP ++ []).toArray.size = hp.NCL ∧
        flatForkEnd P.wsLay (claimsP ++ []).toArray
          ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]) G4 u4 = some (o.wo, G, u) := by
  obtain ⟨_, _, _, _, _, H1, hd2, TS, cp, G1, G2, G3, G4, u1, u2, u3, u4, h1, h2, h3, h4, e5, e6,
    e7, e8, e9⟩ := hear_parts_later h hg
  obtain ⟨F4, F7, F8, rhoI, vW, vP, gam, om, w0, wI, d0, dI, a1, _, a3, a4, _, a6, a7, a8, a9, _,
    a11, a12, a13, _, a15, a16, a17, a18, a19⟩ := hearNorms_tape h1
  obtain ⟨tT, G1', u1', row, p', b1, b2, b3, b4⟩ := hearTerms_calls h2
  obtain ⟨tT', G3', c1, c2, _, c4⟩ := hearGated_tape h4
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
  have hH : Chain7 P hp F t0 (t0.drop 1) o H1 tT F4 F7 F8 G1' G2 := by
    have s1 : (sentOf (t0.drop 1)).toArray = vW := by
      rw [a4]
      exact Array.toArray_toList
    have s2 : (sentOf ((ksOf P hp).tcP (t0.drop 1))).toArray = vP := by
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
  refine ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, t0.drop (1 + P.rd.muV + 6), u1,
    u3.drop (P.rd.muH + 4), u4, e5, hz, b2, ?_, ?_, ?_, ?_, ?_, ?_, hH, ?_, TS, cp, e6, e7, e8,
    e9⟩
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
  · rw [levelIn_rest c4]
    unfold Ks.tcW
    rw [T6]
    show (u3.drop (P.rd.muH + 4 + 1)).drop (P.rd.muH2 + 4) =
      ((u3.drop (P.rd.muH + 4 + 1)).drop (P.rd.muH2 + 3)).drop 1
    rw [drop_drop' (P.rd.muH2 + 3) 1]

/-- **The six calls, each on its named tape, where the hearing returns in a group that is not the
first.** t is the tape behind the token point's round. -/
theorem own_calls6 {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hg : (g == 0) = false) :
    ∃ (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork)
      (v1 v2 v5 u4 : Tape),
      o.hd2 = some hd2 ∧ o.H.ztF = H1.ztF ∧ isZeroE tT.p.eps = false ∧
      Fl.levelIn P.rd.muV
          (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
          (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
          (orderDefault P.rd.muV) F4 ((ksOf P hp).tc1 (t0.drop 1)) = some (H1.wpl, F7, v1) ∧
      Fl.tscIn H1.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F8
          (((ksOf P hp).tcP (t0.drop 1)).drop 1) = some (H1.tV, G1, v2) ∧
      Fl.tscIn H1.ztF P.y.h.lt (nEndT P.y) 1 G1
          ((((ksOf P hp).tcP (t0.drop 1)).drop 1).drop (P.y.h.lt + 3)) =
        some (tT, G1', (ksOf P hp).tc4 (t0.drop 1)) ∧
      hearStack engFl P o.v o.H hp.lamS (hp.NCL - 0) G2 ((ksOf P hp).tc4 (t0.drop 1)) =
        some (o.K, G3, (ksOf P hp).tc5 (t0.drop 1)) ∧
      Fl.levelIn P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
          (orderRange P.rd.muH) G3 ((ksOf P hp).tc5 (t0.drop 1)) = some (o.hd, G3', v5) ∧
      Fl.levelIn P.rd.muH2
          ((drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray ++
            downFrom o.K.rs P.y.lfe ++ tT.r)
          (Road.Rows.start2 P.y.LamM o.K.sH1
            (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray)
          (orderRange P.rd.muH2) G3' ((ksOf P hp).tc6 (t0.drop 1)) = some (hd2, G4, u4) ∧
      Chain7 P hp F t0 (t0.drop 1) o H1 tT F4 F7 F8 G1' G2 := by
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, v1, v2, v5, u4, e5, hz, b2, c1, c2, c3,
    c4, c5, c6, hH, _⟩ := own_calls7 h hg
  exact ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, v1, v2, v5, u4, e5, hz, b2, c1, c2, c3,
    c4, c5, c6, hH⟩

/-- **The first six records, where the hearing returns in a group that is not the first.** -/
theorem own_recs6 {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hg : (g == 0) = false) :
    ∃ (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 G2 G3 G3' : Fork),
      o.hd2 = some hd2 ∧
      Recs6 P hp o H1 tT hd2 (t0.drop 1)
        (levelRec P.rd.muV
          (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
          (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
          (orderDefault P.rd.muV) F4 ((ksOf P hp).tc1 (t0.drop 1)))
        (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop 1)))
        (levelRec P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
          (orderRange P.rd.muH) G3 ((ksOf P hp).tc5 (t0.drop 1)))
        (levelRec P.rd.muH2
          ((drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray ++
            downFrom o.K.rs P.y.lfe ++ tT.r)
          (Road.Rows.start2 P.y.LamM o.K.sH1
            (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray)
          (orderRange P.rd.muH2) G3' ((ksOf P hp).tc6 (t0.drop 1))) ∧
      o.H = heardOf H1 tT := by
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, v1, v2, v5, u4, e5, _, _, c1, c2, c3,
    c4, c5, c6, hH⟩ := own_calls6 h hg
  exact ⟨H1, hd2, tT, F4, G2, G3, G3', e5, ⟨level_recAt c1, tsc_recAt c2, tsc_recAt c3,
    stack_recAt c4, level_recAt c5, level_recAt c6⟩, hH.heard⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.level_recAt
#print axioms OnBytes.Road.K4.tsc_recAt
#print axioms OnBytes.Road.K4.stack_recAt
#print axioms OnBytes.Road.K4.level_vals_len
#print axioms OnBytes.Road.K4.tsc_vals_len
#print axioms OnBytes.Road.K4.stack_vals_len
#print axioms OnBytes.Road.K4.own_calls7
#print axioms OnBytes.Road.K4.own_calls6
#print axioms OnBytes.Road.K4.own_recs6
