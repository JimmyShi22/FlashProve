-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/JoinHeard.lean: CONDITIONAL.

What is here. `JoinWorth` AT A HEARING OF K4's OWN TEXT (the verifier's function `hear`,
OnBytes/Desc/First/K4/Hear.lean, for the feed-forward layers' own rounds), IN THE VERY SHAPE IN
WHICH StackWhole.lean's `stack_whole` ASKS IT (its hypothesis hJW): for all marks, factors and
second token sumcheck that the hearing's own functions return. The public structure is one with the
letters that the library's `pub34_of_hear_run` (Johnson/Road/K4/PubOfHearTied.lean) ties to a return
of `hear`; five ties of the honest side to the hearing make its two environments the honest side's;
TokOfPub.lean's `joinWorth_ret` is called.

  `HeardX`   the letters of a public structure at a hearing: eight of the equations that the
     library's maker concludes
  `env_tied`   **its two environments are the honest side's**
  `joinWorth_tied`   **`JoinWorth` in `stack_whole`'s shape**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE (X). NOTHING NEW IS SHOWN: rewritings and
one call. X IS A LETTER: the library's maker is not called here, so its public premises are not
asked; whoever calls it has `HeardX` from its conclusion. FIVE TIES OF THE HONEST SIDE TO THE
HEARING ARE HYPOTHESES: the environment (tv), the calls' weights (te), the token point (tz), what
stands for the shown values (tsh), the end point (trt). The other hypotheses are `joinWorth_ret`'s,
in X's letters, but Xp, Xc and hzt, and but eight that X itself gives and that are drawn from it
here: five of the six facts on the weights' layout (the sixth, on dq, stays), the list of tables,
the token point's size, the family "b-bits-0". SO, ALL: the five ties; on the world W: its entries
are the true ones (hW), THE CLAIM THAT THE LOOKUP READS (hJoin: the library's `Join`), the slot of
the claimed sum holds the honest job's total (hσ): these three bear what is summed; on the honest
input: `CellsAre`, `TensorIs` twice; on X: `HeardX`, its laying and its sub-proof's matrices in the
plan's letters (hl hm), the honest named points are a part of its points (hpp), the table of scales
(hscl), `QKOk`; at the tokens: `TokRet` at every token (Tr) and the end function's return at every
shown array (hstT), both of which TokRetOf.lean shows; public: `GatedNums`, hdq, hTS, the two
tensors are found; two that hold at all sizes by the library's definitions (hnl hne); returns: h,
hJ, hH; hom. No example of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TokOfPub
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MergedAt
import Johnson.Road.K4.NormWordsOfHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff World Tsc Fork)
open OnBytes.Model.Layer (ClaimEnv PanelEnv Own Ten layTables tableAsks funsOf stackEnd stubO)
open OnBytes.Road (sclOf cellsAt cellsOf Mats admitted_of_layout)
open OnBytes.Road.K4 (entryOf env_of_hear)
open OnBytes.Road.K4.C (sidesEnv stack_open stackIs_of tabAt_planes lastOf_size CellsAre PtsPart
  TensorIs GatedNums)
open OnBytes.Desc.First.K4 (engFl hear)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4.Honest

/-- **The letters of a public structure at a hearing**: eight of the equations that the library's
`pub34_of_hear_run` concludes. P: the plan; o: what the hearing returned. This defines a hypothesis;
the definition claims nothing. -/
structure HeardX (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (P : OnBytes.Model.Layer.Pub) (o : Own) :
    Prop where
  ρ : X.ρ = Reading.gl
  H : X.H = o.H
  v : X.p.v = o.v
  alpha : X.alpha = o.H.fo.alpha
  theta : X.theta = o.H.fo.theta
  tT : o.H.tT = some X.tT
  c : X.c = { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := X.tT.r }
  p : X.p = { v := o.v, e := o.H.fo.e, shownT := X.p.shownT, zt := o.H.ztF, stubO := stubO P.y }

variable {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData} {tk : Array ℕ}
  {fo : OnBytes.Model.Forest.Heard} {F G : Fork} {t u : OnBytes.K.Kc.Tape} {o : Own}
  {X : OnBytes.Road.Rows.Pub34 Cb.Gl.E}

/-- **The structure's two environments are the honest side's.** CONDITIONAL: on every hypothesis
named. THE FULL SIZE ALONE (X). -/
theorem env_tied (h : stackData Q w p shownT = some SD)
    (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    (T : HeardX X { Q.P with tokv := tk } o) (tv : SD.S.v = o.v) (te : SD.S.fo.e = o.H.fo.e)
    (tz : SD.S.zt = o.H.ztF) (tsh : X.p.shownT = shownT) (trt : p.rt = X.tT.r) :
    X.p = sidesEnv SD.S shownT ∧ X.c = { SD.S.ce with rs := o.K.rs, rt := p.rt } := by
  have hS := (stack_open h).1
  constructor
  · rw [T.p, tsh]
    unfold sidesEnv
    rw [tv, te, tz, (env_of_hear hH).1]
  · rw [T.c, W.sides_ce hS, tv, trt]

/-- **`JoinWorth` AT A HEARING, IN `stack_whole`'s SHAPE.** CONDITIONAL: on every hypothesis named.
THE FULL SIZE ALONE (X). -/
theorem joinWorth_tied [scl : Scl] (h : stackData Q w p shownT = some SD) {J : Job}
    (hJ : jobTermsOn SD.S = some J)
    (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    (T : HeardX X { Q.P with tokv := tk } o) (tv : SD.S.v = o.v) (te : SD.S.fo.e = o.H.fo.e)
    (tz : SD.S.zt = o.H.ztF) (tsh : X.p.shownT = shownT) (trt : p.rt = X.tT.r)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam)
    (W : World Cb.Gl.E) (Mm : Mats Cb.Gl.E)
    (hW : W.entry = entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some X.r)
    (hpp : PtsPart (namedPts Q p) X.pts)
    (hm : (X.tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hC : CellsAre Q w Mm)
    {ts tu : Ten} (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w (cellsOf X.D (cellsAt SD.S.v.y Mm)) .sl ts)
    (Su : TensorIs Q w (cellsOf X.D (cellsAt SD.S.v.y Mm)) .up tu) (N : GatedNums Q X.D)
    (hnl : X.D.nl ≤ 2 ^ X.D.lL) (hne : 2 * X.D.ne ≤ 2 ^ X.D.lL) (hdq : X.s.dq ≤ SD.S.v.y.dq)
    (hTS : SD.S.TS = [0, 1, 2, 5]) (hom : Reading.gl.val (SD.om.getD 0 zeroE) = 1)
    (hstT : ∀ sh bl places, SD.S.panels sh = some (bl, places) → ∃ rs om H1 V lam sA sB s',
      stackEnd SD.S.v.y bl rs lam om H1 V sA sB = some s')
    (hQK : X.QKOk)
    (Tr : ∀ i, i < 2 ^ X.D.lT → TokRet X SD i) (hJoin : X.Join W Mm (wmOf w.w))
    (hσ : W.slot X.tT.sCl = Reading.gl.val J.cube.total) :
    ∀ (weighed : Array _) (parts : List Aff) (tT' : Tsc),
      o.v.y.calls.mapM o.v.weighedOf = some weighed →
      ((o.v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
        o.v.joinPart o.H.fo.alpha o.H.fo.theta x.2 x.1.1 x.1.2) = some parts →
      o.H.tT = some tT' → JoinWorth o.H tT' parts W SD := by
  intro weighed parts tT' hw hparts hT'
  obtain ⟨Xp, Xc⟩ := env_tied h hH T tv te tz tsh trt
  obtain rfl : X.tT = tT' := Option.some.inj (T.tT.symm.trans hT')
  have ew : X.weighed = weighed := by
    have q := X.hw
    rw [T.v] at q
    exact Option.some.inj (q.symm.trans hw)
  have ep : X.parts = parts := by
    have q := X.hparts
    rw [T.v, T.alpha, T.theta, ew] at q
    exact Option.some.inj (q.symm.trans hparts)
  -- what X itself gives
  have ey : X.p.v.y = SD.S.v.y := by rw [T.v, tv]
  have sh := (admitted_of_layout X.hy X.S.p3).shape
  obtain ⟨_, tbI, I⟩ := stackIs_of h
  have hd : X.s.d = SD.S.v.y.h.d := by
    have q := X.hsd
    rw [← X.env, ey] at q
    exact q
  have hfew : X.s.fe = SD.S.v.y.h.fe := by
    have q := X.hsfe
    rw [← X.env, ey] at q
    exact q
  have hfw : X.s.f = SD.S.v.y.h.f := by rw [X.Zw.f, X.Z.f, ← sh, ey]
  have hNE : X.s.NE = SD.S.v.y.h.NE := by rw [X.Zw.NE, X.Z.nexp, ← sh, ey]
  have hfef : X.s.fe ≤ SD.S.v.y.h.f := by
    have q : X.D.P.f = 2 * X.D.P.fe := X.f2
    rw [← X.Zw.f, ← X.Zw.fe, hfw] at q
    omega
  have hf : funsOf Q.P.y X.H.fo X.pts X.r.2.1 = some X.funs := by
    rw [← I.y, ← ey]
    exact X.hfun
  have hzs : SD.S.zt.size = SD.S.v.y.h.lt := by
    rw [tz, ← T.H, ← ey]
    exact lastOf_size (by rw [X.hzt]; rfl)
  have hv : SD.S.v.tab = X.r.1 := by
    rw [tv, ← T.v]
    exact X.ht
  obtain ⟨tB0, hB⟩ := tabAt_planes hl hv
  rw [← T.H, ← ep]
  exact joinWorth_ret h hJ X T.ρ hscl Xp Xc (by rw [tz, T.H]) W Mm hW hl hf hpp hm hC hB hts htu Ss
    Su N hnl hne hd hfew hdq (le_of_eq hfw) hfef (le_of_eq hNE) hTS hom hstT hzs hQK Tr hJoin hσ

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.env_tied
#print axioms ProofFile.Honest.K4.joinWorth_tied
