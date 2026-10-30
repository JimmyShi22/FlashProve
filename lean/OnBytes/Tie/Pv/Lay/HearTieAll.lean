-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearTieAll.lean: from the success of the routine that hears all own messages of
a layers' sub-proof (hearOwn, OnBytes/Model/Layer.lean) to the typed side of the chain of
Cb/Pv/Lay/Own.lean: each of the seven sumchecks' typed outputs is the routine's record, read.

OnBytes/Tie/Pv/Lay/HearAll.lean says what was heard, stage by stage, with the records.
OnBytes/Tie/Pv/Lay/OwnTieL.lean makes the chain's transcript from typed data and says what the
chain puts out and owes on it. Here the two are joined.

Main names:
  `betasNz_append`, `Nz7`, `own_betas`: none of the seven sumchecks' last elements reads 0.
  `RecAt H ws k dY nv p`: the record p is that of what was heard (H) under the weights ws: k
    rounds of two scalars, dY scalars in the round of the further variable, nv end values.
    `LevelSaid.recAt`, `TokSaid.recAt`, `StackSaid.recAt`, `MergeSaid.recAt`: the four kinds of
    record have this form.
  `rec_out`: one stage: from `RecAt` and the fit of the weights: `OutIs` and `SumSaid`.
  `Recs7`, `own_recs`: the seven records in the chain's order, each with the weights of its
    rounds; the rows that the routines made of four of them; what hearTerms hands on.
  `hear_tieL`: from hearOwn's success and `NzCtx` at its start: the stages heard, `OwnSaidL`,
    `NzCtx` behind, `Nz7`, `Recs7`.
  `StgFits`, `fits_out`: the numbers of a stage's letters and the fit of the weights, as one
    premise.
  `TailOf`: the typed data from the limbs' scalars on (`TailH`) are those of what was heard and of
    the records.
  `tail_outs`: under `TailOf`, `Recs7` and `StgFits` at each stage: all seven `OutIs`.
  `TailAdd`, `OwnH.tail`, `tail_of`: the typed data made from what was heard, the records' targets
    and what the typed side adds (for each sumcheck its end values and its state); they meet
    `TailOf`.
  `hear_outL`: the whole: from hearOwn's success and `NzCtx` at its start, for all letters and
    additions with `StgFits` at each stage: all seven `OutIs` at these data.
  `tail_run`, `tail_runF`: on the chain's transcript made from these data and the points heard, if
    every pick is lawful (`Ch.FixOK`), the chain's verifier puts out `Ch.run` of that transcript
    (`own_out`, OnBytes/Tie/Pv/Lay/OwnTieL.lean; what the chain then owes: `own_last` there).
    These two hold of all data: hearOwn does not occur in them.
  `TailLens`: the letters' numbers are the lengths of the lists heard.

Limits: those of OnBytes/Tie/Pv/Lay/HearAll.lean and HearTieL.lean: a sub-proof with terms, routed
experts and more than one layer bit; one direction; `NzCtx` a premise. `StgFits` is a premise at
each stage: it is shown of no value of the letters here (for variables in the equality form and
for plain ones: OnBytes/Tie/Pv/Lay/SumFits.lean). `TailOf` does not ask that the typed end values
and states are the readings of what was heard, nor that the letters' numbers are the lengths of
the lists heard (`TailLens`, which no theorem here asks or shows): the typed side reads a list of
another length all the same. The number of a stage's end values is not compared with the number of
values heard. Where the norms' join has no coordinate the routine draws no point, and the chain
has a round for it: that case is not shut out by a premise here. The letters' claims
(`TailH.Claims`) are not shown here, and they are the bridge: `OutIs` speaks of `StgH.out`, the
output at the reading of the record's target and at the added state; `Ch.run` has at each sumcheck
the output at the letters' claim; the two are one only under `StgH.Claim`. So that the chain's
verifier puts out these seven outputs is proved only where `TailH.Claims` is shown. The points
drawn before the limbs' scalars are not in `TailH`.
-/
import OnBytes.Tie.Pv.Lay.HearAll
import OnBytes.Tie.Pv.Lay.HearTieL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay OnBytes.Tie.Pv.Lay.Eng
open OnBytes.Psc (Weight hearMany hearOne)
open OnBytes.Tie.Pv.Att (PscH)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-! ### The seven last elements -/

omit [Fintype K] in
theorem betasNz_append : ∀ l l' : List StageL, BetasNz ρ (l ++ l') ↔ BetasNz ρ l ∧ BetasNz ρ l'
  | [], _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | .sum _ _ _ _ :: l, l' => by
    show _ ∧ BetasNz ρ (l ++ l') ↔ (_ ∧ BetasNz ρ l) ∧ _
    rw [betasNz_append l l', and_assoc]
  | .bat _ _ _ :: l, l' => betasNz_append l l'
  | .point _ _ :: l, l' => betasNz_append l l'
  | .line _ :: l, l' => betasNz_append l l'
  | .idle :: l, l' => betasNz_append l l'

/-- None of the seven sumchecks' last elements reads 0. -/
structure Nz7 (D : OwnH) : Prop where
  b1 : ρ.val D.H1.beta ≠ 0
  b2 : ρ.val D.H2.beta ≠ 0
  b3 : ρ.val D.H3.beta ≠ 0
  b4 : ρ.val D.H4.beta ≠ 0
  b5 : ρ.val D.H5.beta ≠ 0
  b6 : ρ.val D.H6.beta ≠ 0
  b7 : ρ.val D.H7.beta ≠ 0

omit [Fintype K] in
theorem own_betas (D : OwnH) (P : Pub) (hp : HPlan2) (g : Nat) (H0 : Heard) (O : Own) (tT : Tsc)
    (hd2 : Level) (rows : Nat) (h : BetasNz ρ (D.stages P hp g H0 O tT hd2 rows)) : Nz7 ρ D := by
  unfold OwnH.stages footStages at h
  simp only [betasNz_append, BetasNz, and_true, true_and] at h
  exact ⟨by tauto, by tauto, by tauto, by tauto, by tauto, by tauto, by tauto⟩

/-! ### The seven records, in one form -/

/-- The record p is that of what was heard (H), under the weights ws: k rounds of two scalars, dY
scalars in the round of the further variable, nv end values. -/
structure RecAt (H : PscH) (ws : List Weight) (k dY nv : Nat) (p : Psc) : Prop where
  psc : ∃ (C : Aff) (τ : E) (first : Nat),
    Ended p C τ H.mu H.eps first ws H.rs dY H.sentY H.beta
  lens : H.rs.map (·.1.length) = List.replicate k 2
  sentY : H.sentY.length = dY
  vals : H.v.length = nv

theorem LevelSaid.recAt {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {o : Level} {H : PscH} (s : LevelSaid mu rho C order F G o H) :
    ∃ p : Psc, RecAt H (levelWeights mu rho order) mu 2 2 p ∧
      o.row = p.rowForm (mulE (H.v.getD 0 zeroE) (H.v.getD 1 zeroE)) {} := by
  obtain ⟨τ, p, _, a2, a3⟩ := s.psc
  refine ⟨p, ⟨⟨C, τ, _, a2⟩, ?_, s.sentY, s.vals⟩, a3⟩
  refine List.eq_replicate_iff.2 ⟨by rw [List.length_map, s.rounds], fun b hb => ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
  exact s.two x hx

theorem TokSaid.recAt {P : Array E} {lt shown dY : Nat} {F G : Fork} {t : Tsc} {x : E} {H : PscH}
    (s : TokSaid P lt shown dY F G t x H) : RecAt H (tokenWeights P lt) lt dY shown t.p := by
  refine ⟨⟨_, _, _, s.psc⟩, ?_, s.sentY, s.vals⟩
  rw [sizes_of _ _ (by rw [s.rounds, tokenWeights_length P lt s.len]) s.sizes,
    tokenWeights_sizes]
  refine List.eq_replicate_iff.2 ⟨?_, fun b hb => ?_⟩
  · rw [List.length_map, List.length_take, Array.length_toList]
    exact Nat.min_eq_left s.len
  · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hb
    rfl

theorem StackSaid.recAt {lamS n : Nat} {C : Aff} {F G : Fork} {Kk : HeardStack} {p : Psc}
    {H : PscH} (s : StackSaid lamS n C F G Kk p H) :
    RecAt H (List.replicate lamS (Weight.plain 3)) lamS 2 n p := by
  obtain ⟨τ, _, a2⟩ := s.psc
  refine ⟨⟨C, τ, _, a2⟩, ?_, s.sentY, s.vals⟩
  rw [sizes_of _ _ (by rw [s.rounds, List.length_replicate]) s.sizes, List.map_replicate]
  rfl

theorem MergeSaid.recAt {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork}
    {wo : WsForkOut} {x : E} {H : PscH} (s : MergeSaid lay cl sv F G wo x H) :
    RecAt H (List.replicate lay.lk (Weight.plain 3)) lay.lk 1 1 wo.p := by
  obtain ⟨τ, _, a2⟩ := s.psc
  exact ⟨⟨_, τ, _, a2⟩, s.rounds, s.sentY, by rw [s.vals]; rfl⟩

/-- One stage: the typed output is the record, read. -/
theorem rec_out {M X : Type} {S : Stg K M X} (D : StgH ρ S) {riders : List E} {H : PscH}
    {p : Psc} {ws : List Weight} {nv : Nat} (o : StgOf ρ D riders H p)
    (r : RecAt H ws S.L.S.k S.L.M.DY nv p) (hn : ∀ i, S.L.M.n i = 2)
    (hfit : Fits ρ (ws ++ [Weight.atZero (S.L.M.DY + 1)]) S.L.T.par.fmt (S.L.T.par.dat D.st)
      (S.F D.st)) :
    OutIs ρ D p ∧
      SumSaid ρ S.L S.F D.st p (ws ++ [Weight.atZero (S.L.M.DY + 1)]) D.H.mu D.H.rs D.H.sentY
        D.H.beta D.b D.v := by
  obtain ⟨C, τ, first, a⟩ := r.psc
  refine stg_out ρ D o a hfit ?_ r.sentY
  rw [r.lens, show S.L.M.n = fun _ => 2 from funext hn, List.ofFn_const]

/-! ### All seven -/

/-- The seven sumchecks' records, in the chain's order, each with the weights of its rounds, and
the rows that the routines made from four of them. -/
structure Recs7 (P : Pub) (hp : HPlan2) (g : Nat) (O : Own) (D : OwnH) (H0 : Heard) (tT : Tsc)
    (hd2 : Level) (p1 p3 p4 p5 p6 : Psc) : Prop where
  r1 : RecAt D.H1 (levelWeights P.rd.muV (normsStart P.y H0.sW H0.gp (D.rhoI P) H0.PV).2
    (orderDefault P.rd.muV)) P.rd.muV 2 2 p1
  row1 : H0.wpl.row = p1.rowForm (mulE (D.H1.v.getD 0 zeroE) (D.H1.v.getD 1 zeroE)) {}
  r2 : RecAt D.H2 (tokenWeights H0.PV P.y.h.lt) P.y.h.lt 2 (ledNO P.y.h.xl * P.y.NI) H0.tV.p
  r3 : RecAt D.H3 (tokenWeights H0.ztF P.y.h.lt) P.y.h.lt 1 (nEndT P.y) p3
  t3 : tT.p = { p3 with rowMade := true }
  kt : O.H.KT = (p3.rowForm zeroE {}).scale (negE (invE p3.eps))
  r4 : RecAt D.H4 (List.replicate hp.lamS (Weight.plain 3)) hp.lamS 2
    (2 + (1 + (if P.y.h.p3 then P.y.LamM else 0)) + nclp hp g) p4
  row4 : O.K.rowS = p4.rowForm (mulE O.K.fin.As O.K.fin.Bs) {}
  r5 : RecAt D.H5 (levelWeights P.rd.muH (downFrom O.K.rs O.K.fin.wD ++ O.H.ztF)
    (orderRange P.rd.muH)) P.rd.muH 2 2 p5
  row5 : O.hd.row = p5.rowForm (mulE (D.H5.v.getD 0 zeroE) (D.H5.v.getD 1 zeroE)) {}
  r6 : RecAt D.H6 (levelWeights P.rd.muH2
    ((D.dM.elems.map E.ofTriple).toArray ++ downFrom O.K.rs P.y.lfe ++ tT.r)
    (orderRange P.rd.muH2)) P.rd.muH2 2 2 p6
  row6 : hd2.row = p6.rowForm (mulE (D.H6.v.getD 0 zeroE) (D.H6.v.getD 1 zeroE)) {}
  r7 : RecAt D.H7 (List.replicate P.wsLay.lk (Weight.plain 3)) P.wsLay.lk 1 1 O.wo.p

theorem own_recs {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {O : Own} {F G : Fork}
    {D : OwnH} {H0 : Heard} {tT : Tsc} {hd2 : Level} {claims : Array WsClaim}
    (s : OwnSaidL P hp g fo O F G D H0 tT hd2 claims) :
    ∃ p1 p3 p4 p5 p6 : Psc, Recs7 P hp g O D H0 tT hd2 p1 p3 p4 p5 p6 := by
  obtain ⟨F4, F7, F8, F1, F1', F2, F3, F3', F5, F6, t3, C, p4, c1, c5, _, a2, _, _, a5, a6, a7, a8,
    _, _, a11, _, _, _, a14, _, _, a17⟩ := s.recs
  obtain ⟨p1, b1, b2⟩ := a2.recAt
  obtain ⟨tT', Fm, e1, g5, g6⟩ := a14.said
  have et : tT' = tT := Option.some.inj (e1.symm.trans s.hasT)
  rw [et] at g6
  obtain ⟨p5, b5, d5⟩ := g5.recAt
  obtain ⟨p6, b6, d6⟩ := g6.recAt
  exact ⟨p1, t3.p, p4, p5, p6, b1, b2, a5.recAt, a6.recAt, by rw [a7], by rw [a8], a11.recAt,
    a11.row, b5, d5, b6, d6, a17.recAt⟩

omit [Fintype K] in
/-- From the success of the routine that hears all own messages of a layers' sub-proof, on a view
whose elements drawn by the rule that never gives 0 do not read 0: the stages heard, in the chain's
order; what the records hold of them; no sumcheck's last element reads 0; the seven records in one
form. -/
theorem hear_tieL (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (O : Own) (F G : Fork)
    (c c' : Ctx) (h : hearOwn P hp g fo F c = .ok ((O, G), c')) (hs : Sized F)
    (hne : P.rd.tscCalls.isEmpty = false) (hp3 : P.y.h.p3 = true) (hl : P.y.h.ll > 1)
    (hc : NzCtx ρ c) :
    ∃ (D : OwnH) (H0 : Heard) (tT : Tsc) (hd2 : Level) (claims : Array WsClaim)
      (p1 p3 p4 p5 p6 : Psc),
      HeardL (D.stages P hp g H0 O tT hd2 (claimSlots g (nclp hp g) O.K.sV O.sVE).size) c c' ∧
      OwnSaidL P hp g fo O F G D H0 tT hd2 claims ∧ NzCtx ρ c' ∧ Nz7 ρ D ∧
      Recs7 P hp g O D H0 tT hd2 p1 p3 p4 p5 p6 := by
  obtain ⟨D, H0, tT, hd2, claims, a1, a2⟩ := own_heardL P hp g fo O F G c c' h hs hne hp3 hl
  obtain ⟨n1, n2⟩ := heardL_nz ρ _ c c' hc a1
  obtain ⟨p1, p3, p4, p5, p6, r⟩ := own_recs a2
  exact ⟨D, H0, tT, hd2, claims, p1, p3, p4, p5, p6, a1, a2, n1, own_betas ρ D _ _ _ _ _ _ _ _ n2,
    r⟩

/-! ### The typed side -/

/-- The letters of a stage have the numbers k and dY, two scalars a round, and the weights ws fit
its variables at the state st under its pick. -/
structure StgFits {M X : Type} (S : Stg K M X) (st : S.L.St) (ws : List Weight) (k dY : Nat) :
    Prop where
  k : S.L.S.k = k
  dY : S.L.M.DY = dY
  two : ∀ i, S.L.M.n i = 2
  fit : Fits ρ (ws ++ [Weight.atZero (S.L.M.DY + 1)]) S.L.T.par.fmt (S.L.T.par.dat st) (S.F st)

theorem fits_out {M X : Type} {S : Stg K M X} (D : StgH ρ S) {riders : List E} {H : PscH}
    {p : Psc} {ws : List Weight} {k dY nv : Nat} (o : StgOf ρ D riders H p)
    (r : RecAt H ws k dY nv p) (f : StgFits ρ S D.st ws k dY) : OutIs ρ D p := by
  obtain ⟨rfl, rfl, h2, h3⟩ := f
  exact (rec_out ρ D o r h2 h3).1

/-- The typed data from the limbs' scalars on are those of what was heard and of the records. -/
structure TailOf {M X : Type} {T : LayTail K M X} (Dt : TailH ρ T) (D : OwnH) (H0 : Heard)
    (O : Own) (hd2 : Level) (p1 p3 p4 p5 p6 : Psc) : Prop where
  sL : Dt.sL = D.vW
  xL : Dt.xL = D.xL
  pN : Dt.pN = D.dI.elems.map E.ofTriple
  d1 : StgOf ρ Dt.d1 [] D.H1 p1
  x1 : Dt.x1 = H0.wpl.tau
  sP : Dt.sP = D.vP
  xP : Dt.xP = D.xP
  d2 : StgOf ρ Dt.d2 [D.cl2] D.H2 H0.tV.p
  d3 : StgOf ρ Dt.d3 [D.cl3] D.H3 p3
  x4 : Dt.x4 = D.x4
  d4 : StgOf ρ Dt.d4 [] D.H4 p4
  d5 : StgOf ρ Dt.d5 [] D.H5 p5
  x5 : Dt.x5 = O.hd.tau
  pR : Dt.pR = D.dM.elems.map E.ofTriple
  d6 : StgOf ρ Dt.d6 [] D.H6 p6
  x6 : Dt.x6 = hd2.tau
  sW : Dt.sW = D.vE
  xW : Dt.xW = D.xW
  d7 : StgOf ρ Dt.d7 [] D.H7 O.wo.p

/-- Each of the seven typed outputs is its record, read. -/
theorem tail_outs {M X : Type} {T : LayTail K M X} (Dt : TailH ρ T) {P : Pub} {hp : HPlan2}
    {g : Nat} {O : Own} {D : OwnH} {H0 : Heard} {tT : Tsc} {hd2 : Level} {p1 p3 p4 p5 p6 : Psc}
    (o : TailOf ρ Dt D H0 O hd2 p1 p3 p4 p5 p6) (r : Recs7 P hp g O D H0 tT hd2 p1 p3 p4 p5 p6)
    (f1 : StgFits ρ T.s1 Dt.d1.st (levelWeights P.rd.muV
      (normsStart P.y H0.sW H0.gp (D.rhoI P) H0.PV).2 (orderDefault P.rd.muV)) P.rd.muV 2)
    (f2 : StgFits ρ T.s2 Dt.d2.st (tokenWeights H0.PV P.y.h.lt) P.y.h.lt 2)
    (f3 : StgFits ρ T.s3 Dt.d3.st (tokenWeights H0.ztF P.y.h.lt) P.y.h.lt 1)
    (f4 : StgFits ρ T.s4 Dt.d4.st (List.replicate hp.lamS (Weight.plain 3)) hp.lamS 2)
    (f5 : StgFits ρ T.s5 Dt.d5.st (levelWeights P.rd.muH
      (downFrom O.K.rs O.K.fin.wD ++ O.H.ztF) (orderRange P.rd.muH)) P.rd.muH 2)
    (f6 : StgFits ρ T.s6 Dt.d6.st (levelWeights P.rd.muH2
      ((D.dM.elems.map E.ofTriple).toArray ++ downFrom O.K.rs P.y.lfe ++ tT.r)
      (orderRange P.rd.muH2)) P.rd.muH2 2)
    (f7 : StgFits ρ T.s7 Dt.d7.st (List.replicate P.wsLay.lk (Weight.plain 3)) P.wsLay.lk 1) :
    OutIs ρ Dt.d1 p1 ∧ OutIs ρ Dt.d2 H0.tV.p ∧ OutIs ρ Dt.d3 p3 ∧ OutIs ρ Dt.d4 p4 ∧
      OutIs ρ Dt.d5 p5 ∧ OutIs ρ Dt.d6 p6 ∧ OutIs ρ Dt.d7 O.wo.p :=
  ⟨fits_out ρ _ o.d1 r.r1 f1, fits_out ρ _ o.d2 r.r2 f2, fits_out ρ _ o.d3 r.r3 f3,
    fits_out ρ _ o.d4 r.r4 f4, fits_out ρ _ o.d5 r.r5 f5, fits_out ρ _ o.d6 r.r6 f6,
    fits_out ρ _ o.d7 r.r7 f7⟩

/-! ### The typed data, made from what was heard -/

/-- What the typed side adds to what was heard: for each sumcheck its end values and its state. -/
structure TailAdd {M X : Type} (T : LayTail K M X) where
  v1 : T.s1.L.S.A → K
  st1 : T.s1.L.St
  v2 : T.s2.L.S.A → K
  st2 : T.s2.L.St
  v3 : T.s3.L.S.A → K
  st3 : T.s3.L.St
  v4 : T.s4.L.S.A → K
  st4 : T.s4.L.St
  v5 : T.s5.L.S.A → K
  st5 : T.s5.L.St
  v6 : T.s6.L.S.A → K
  st6 : T.s6.L.St
  v7 : T.s7.L.S.A → K
  st7 : T.s7.L.St

/-- The typed data from the limbs' scalars on, made from what was heard, the records' targets and
the additions. -/
def OwnH.tail (D : OwnH) (nz : Nz7 ρ D) (H0 : Heard) (O : Own) (hd2 : Level)
    (p1 p3 p4 p5 p6 : Psc) {M X : Type} {T : LayTail K M X} (a : TailAdd T) : TailH ρ T where
  sL := D.vW
  xL := D.xL
  pN := D.dI.elems.map E.ofTriple
  d1 := ⟨[], D.H1, nz.b1, a.v1, a.st1, p1.target⟩
  x1 := H0.wpl.tau
  sP := D.vP
  xP := D.xP
  d2 := ⟨[D.cl2], D.H2, nz.b2, a.v2, a.st2, H0.tV.p.target⟩
  d3 := ⟨[D.cl3], D.H3, nz.b3, a.v3, a.st3, p3.target⟩
  x4 := D.x4
  d4 := ⟨[], D.H4, nz.b4, a.v4, a.st4, p4.target⟩
  d5 := ⟨[], D.H5, nz.b5, a.v5, a.st5, p5.target⟩
  x5 := O.hd.tau
  pR := D.dM.elems.map E.ofTriple
  d6 := ⟨[], D.H6, nz.b6, a.v6, a.st6, p6.target⟩
  x6 := hd2.tau
  sW := D.vE
  xW := D.xW
  d7 := ⟨[], D.H7, nz.b7, a.v7, a.st7, O.wo.p.target⟩

theorem tail_of (D : OwnH) (nz : Nz7 ρ D) (H0 : Heard) (O : Own) (hd2 : Level)
    (p1 p3 p4 p5 p6 : Psc) {M X : Type} {T : LayTail K M X} (a : TailAdd T) :
    TailOf ρ (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a) D H0 O hd2 p1 p3 p4 p5 p6 :=
  ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl,
    ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩

/-- The letters' numbers are the lengths of the lists heard. Where they are not, the typed side
reads a list all the same: it cuts it, or fills it with 0. -/
structure TailLens {M X : Type} (T : LayTail K M X) (D : OwnH) : Prop where
  nL : T.nL = D.vW.length
  gN : T.gN = D.dI.elems.length
  nP : T.nP = D.vP.length
  gR : T.gR = D.dM.elems.length
  nW : T.nW = D.vE.length
  n1 : T.s1.n = 0
  n2 : T.s2.n = 1
  n3 : T.s3.n = 1
  n4 : T.s4.n = 0
  n5 : T.s5.n = 0
  n6 : T.s6.n = 0
  n7 : T.s7.n = 0

/-- The whole: from the success of the routine that hears all own messages of a layers' sub-proof
to the seven typed outputs on the transcript made from what it heard. -/
theorem hear_outL (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (O : Own) (F G : Fork)
    (c c' : Ctx) (h : hearOwn P hp g fo F c = .ok ((O, G), c')) (hs : Sized F)
    (hne : P.rd.tscCalls.isEmpty = false) (hp3 : P.y.h.p3 = true) (hl : P.y.h.ll > 1)
    (hc : NzCtx ρ c) :
    ∃ (D : OwnH) (H0 : Heard) (tT : Tsc) (hd2 : Level) (claims : Array WsClaim)
      (p1 p3 p4 p5 p6 : Psc) (nz : Nz7 ρ D),
      HeardL (D.stages P hp g H0 O tT hd2 (claimSlots g (nclp hp g) O.K.sV O.sVE).size) c c' ∧
      OwnSaidL P hp g fo O F G D H0 tT hd2 claims ∧ NzCtx ρ c' ∧
      Recs7 P hp g O D H0 tT hd2 p1 p3 p4 p5 p6 ∧
      ∀ {M X : Type} (T : LayTail K M X) (a : TailAdd T),
        StgFits ρ T.s1 a.st1 (levelWeights P.rd.muV
          (normsStart P.y H0.sW H0.gp (D.rhoI P) H0.PV).2 (orderDefault P.rd.muV)) P.rd.muV 2 →
        StgFits ρ T.s2 a.st2 (tokenWeights H0.PV P.y.h.lt) P.y.h.lt 2 →
        StgFits ρ T.s3 a.st3 (tokenWeights H0.ztF P.y.h.lt) P.y.h.lt 1 →
        StgFits ρ T.s4 a.st4 (List.replicate hp.lamS (Weight.plain 3)) hp.lamS 2 →
        StgFits ρ T.s5 a.st5 (levelWeights P.rd.muH
          (downFrom O.K.rs O.K.fin.wD ++ O.H.ztF) (orderRange P.rd.muH)) P.rd.muH 2 →
        StgFits ρ T.s6 a.st6 (levelWeights P.rd.muH2
          ((D.dM.elems.map E.ofTriple).toArray ++ downFrom O.K.rs P.y.lfe ++ tT.r)
          (orderRange P.rd.muH2)) P.rd.muH2 2 →
        StgFits ρ T.s7 a.st7 (List.replicate P.wsLay.lk (Weight.plain 3)) P.wsLay.lk 1 →
        OutIs ρ (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a).d1 p1 ∧
        OutIs ρ (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a).d2 H0.tV.p ∧
        OutIs ρ (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a).d3 p3 ∧
        OutIs ρ (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a).d4 p4 ∧
        OutIs ρ (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a).d5 p5 ∧
        OutIs ρ (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a).d6 p6 ∧
        OutIs ρ (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a).d7 O.wo.p := by
  obtain ⟨D, H0, tT, hd2, claims, p1, p3, p4, p5, p6, a1, a2, a3, nz, r⟩ :=
    hear_tieL ρ P hp g fo O F G c c' h hs hne hp3 hl hc
  exact ⟨D, H0, tT, hd2, claims, p1, p3, p4, p5, p6, nz, a1, a2, a3, r,
    fun T a f1 f2 f3 f4 f5 f6 f7 =>
      tail_outs ρ _ (tail_of ρ D nz H0 O hd2 p1 p3 p4 p5 p6 a) r f1 f2 f3 f4 f5 f6 f7⟩

/-- On the transcript made from what was heard the chain's verifier puts out the run's last
statement (a sub-proof that is not the first). -/
theorem tail_run {M X : Type} (A : LayOwn K M X) (D : OwnH) (nz : Nz7 ρ D) (H0 : Heard) (O : Own)
    (hd2 : Level) (p1 p3 p4 p5 p6 : Psc) (a : TailAdd A.tail) (hF : A.ch.FixOK) (Ex : ExtSpec)
    (x : X) (y : Ex.Str) :
    (A.ch.R Ex).red.out (x, y) (A.ch.join Ex (ownTrs A (D.dV.elems.map E.ofTriple)
        (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a))) =
      some (A.ch.run x (ownTrs A (D.dV.elems.map E.ofTriple)
        (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a)), y) :=
  own_out A _ _ hF Ex x y

/-- The same for the first sub-proof. -/
theorem tail_runF {M X : Type} (A : LayOwnFirst K M X) (D : OwnH) (nz : Nz7 ρ D) (H0 : Heard)
    (O : Own) (hd2 : Level) (p1 p3 p4 p5 p6 : Psc) (a : TailAdd A.tail) (hF : A.ch.FixOK)
    (Ex : ExtSpec) (x : X) (y : Ex.Str) :
    (A.ch.R Ex).red.out (x, y) (A.ch.join Ex (ownTrsF A (D.dV.elems.map E.ofTriple)
        (D.dE.elems.map E.ofTriple) (D.dK.elems.map E.ofTriple)
        (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a))) =
      some (A.ch.run x (ownTrsF A (D.dV.elems.map E.ofTriple) (D.dE.elems.map E.ofTriple)
        (D.dK.elems.map E.ofTriple) (D.tail ρ nz H0 O hd2 p1 p3 p4 p5 p6 a)), y) :=
  own_outF A _ _ _ _ hF Ex x y

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.tail_of
#print axioms OnBytes.Tie.Pv.Lay.hear_outL
#print axioms OnBytes.Tie.Pv.Lay.tail_run
#print axioms OnBytes.Tie.Pv.Lay.tail_runF
#print axioms OnBytes.Tie.Pv.Lay.own_recs
#print axioms OnBytes.Tie.Pv.Lay.hear_tieL
#print axioms OnBytes.Tie.Pv.Lay.tail_outs
#print axioms OnBytes.Tie.Pv.Lay.own_betas
#print axioms OnBytes.Tie.Pv.Lay.rec_out
