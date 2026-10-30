-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ClaimsHeard.lean: `TailH.Claims` AT THE DATA THAT ARE READ OFF K4's TAPE,
WHERE K4's HEARING RETURNS, in a group that is not the first, at the library's value
(`FullPar.own`): six of the seven equations on the claimed sums are PAID here; the fourth (the
batched sumcheck) stays a premise. Statements and proofs.

The pieces: `claims_of_firsts` (OnBytes/Desc/First/P1/TailAdds.lean): the states are chosen from the
front on, and only the claimed sums are left; `claim1` `claim5` `claim6` `claim7` and `cl2` `cl3`
(Claims.lean, ClaimsTyped.lean): each claimed sum against the value of K4's start form; `own_led7`
(OwnLedgers.lean): the calls on the tapes that the data read, and the ledgers between;
`hideRun_shown`, `stackVals_shown` (OnBytes/Desc/First/K4/ShownUnder.lean): what a ledger shows
under a slot is the word that the tape's round sent; `public_value`.

  `getD_toArray`, `sent_zero`, `stack_slots4`, `stackVals_at`, `tsc_target_cl`, `svAt`: small tools.
  `wsForkRounds_target`, `target_ended`, `fork_target`: where the merge's text returns, its record's
    target is the public part of its start form, at the powers of the element that the tape's
    first round drew.
  `Nums4`: what is asked of the numbering of the batched sumcheck's end values: the gated products'
    value has number 1, the routed experts' values the numbers from 2 on, the weight claims' values
    the numbers from 2 + (1 + ne) on, in the order of the value's numbering of the claims.
  `first1`, `first2`, `first3`, `first5`, `first6`, `first7`: under `Led7`: the stage's claimed sum,
    at the statement written out in the tape's words, is the reading of the target of K4's record.
  `TgRec g7 …`: the seven targets g7 are those of K4's seven records. `tg_exists`.
  `claims_of_led`: under `Led7` (which `own_led7` gives where `hear` returns on t0 from a ledger
    with arrays of the right sizes, in a group that is not the first): IF the fourth claimed sum
    is the reading of its record's target, the data
    `k4Tail W P hp t0 nz (addsOf …)` meet `TailH.Claims`.
  `k4_claims`: the same from the hearing's return itself: there are `Led7`'s letters and targets
    with `TgRec` and the claims. ("There are additions with the claims" alone would be free:
    OnBytes/Desc/First/P1/ClaimsFree.lean.)

Premises beside the hearing: the ledger in front has arrays of the right sizes; the library's sizes
are the program's (`DimIs`: Johnson/Road/K4/PlanSizes.lean has it under premises of its own);
P.y.LamM = D.ne (Johnson/Road/K4/ClaimsPaid.lean has it at the value of Value.lean alone, under
`Plan4.Meets`); the reading of the program's 1/2 is 1/2 (shown there outright: `gl_half`); `Nums4`
(met by the numbering of Johnson/Road/K4/Num4.lean); `NzT` (the readings of seven challenges on the
tape are not 0), which stands in the type of the data.

Limits. THE FOURTH EQUATION IS A PREMISE. Equations between readings alone: nothing on soundness.
One direction: from a return. A group that is not the first.
-/
import Johnson.Road.K4.OwnLedgers
import Johnson.Road.K4.OwnJoint
import Johnson.Road.K4.Claims
import OnBytes.Desc.First.P1.TailAdds
import OnBytes.Desc.First.K4.ShownUnder
import OnBytes.Tie.Pv.Lay.At.Sizes
import OnBytes.Tie.Pv.Att.HearSaid
import OnBytes.Model.VerifySubproofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Desc.First OnBytes.Desc.First.K4 OnBytes.Slice
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)
open OnBytes.PscRun (hideRun_ok)
open OnBytes.Tie.Pv.Att (shownW public_value)
open OnBytes.Tie.Pv.Lay.At (DimIs)
open OnBytes.Desc.First.P1 (gl drawnOf sentOf tapeEps tapeCl Ks NzT Tg7 TailM TailR aY1 aY2 aZ2 aY4
  aZ4 aY6 aY7 addsOf claims_of_firsts aZ4_vals levelRec levelIn_heard tscIn_heard publicPart_slot
  powers_val)

local notation "rdL" => Johnson.L5.Layers.rd

/-! ### Small tools -/

theorem getD_toArray (l : List E) (j : ℕ) : l.toArray.getD j zeroE = l.getD j zeroE := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- The first word that the tape's first round sent. -/
theorem sent_zero : ∀ t : Tape, (sentOf t).getD 0 zeroE = tapeCl t
  | [] => rfl
  | r :: _ => by
    show r.sent.getD 0 zeroE = r.sent.headD zeroE
    cases r.sent <;> rfl

/-- Two of the batched sumcheck's slots, from the first end value's. -/
theorem stack_slots4 {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {K : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    K.sH1 = K.sA0 + 1 ∧ K.sV = K.sA0 + (2 + (1 + P.y.LamM)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    h1, h2, h3, _⟩ := hearStack_tape h
  exact ⟨h1, by omega⟩

/-- The words of the round of the end values, as the chain's data cut the tape. -/
theorem stackVals_at (lamS : ℕ) (t : Tape) :
    sentOf ((t.drop 1).drop (lamS + 2)) = stackVals lamS t := by
  unfold stackVals
  rw [drop_drop']
  congr 2
  omega

/-- A token sumcheck's target reads as the claimed sum that was sent. -/
theorem tsc_target_cl {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (hF : PscRun.Sized F) (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    gl.val o.p.target = gl.val (tapeCl t) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, v, G0, hG0, hT, _⟩ := tscIn_heard h
  have hF' : PscRun.Sized ({ F with next := F.next + 1 } : Fork) := hF
  obtain ⟨_, _, hin, _⟩ := hideRun_ok _ G0 F.next _ oneE hF' hG0
  have q := (hin 0 Nat.zero_lt_one).2.2.2.1
  rw [Nat.add_zero] at q
  rw [(publicPart_slot gl hT).1, q]
  rfl

/-- The merge's plain rounds keep the record's target. -/
theorem wsForkRounds_target : ∀ {n : Nat} {rm rm' : Array E} {p p' : Psc} {F G : Fork}
    {t u : Tape}, Fl.wsForkRounds n rm p F t = some ((rm', p'), G, u) → p'.target = p.target
  | 0, rm, rm', p, p', F, G, t, u, h => by
    unfold Fl.wsForkRounds at h
    obtain ⟨he, rfl, rfl⟩ := P1.pure_some.mp h
    injection he with e1 e2
    rw [e2]
  | n + 1, rm, rm', p, p', F, G, t, u, h => by
    unfold Fl.wsForkRounds at h
    obtain ⟨x, G1, u1, h1, k1⟩ := P1.bind_some.mp h
    obtain ⟨r, q⟩ := x
    obtain ⟨_, sent, k, _, rfl, rfl, _⟩ := P1.roundIn_sum2_tape h1
    have a := wsForkRounds_target k1
    exact a

/-- The record behind the last round holds the target that it held in front. -/
theorem target_ended (p : Psc) (m : P1.Rnd) :
    ({ P1.stepP p m with ended := true } : Psc).target = p.target := rfl

/-- **The merge's target**: where its text returns, the record's target is the public part, at the
ledger handed in, of the start form at the powers of the element that the tape's first round
drew. -/
theorem fork_target {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    F.publicPart (wsForkStart sv (powers (tapeEps t) sv.size)) = some wo.p.target := by
  unfold flatForkEnd at h
  obtain ⟨_, A1, a1, c1, k1⟩ := P1.bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c1
  obtain ⟨_, A2, a2, c2, k2⟩ := P1.bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c2
  obtain ⟨_, A3, a3, c3, k3⟩ := P1.bind_some.mp k2
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c3
  obtain ⟨x, A4, a4, c4, k4⟩ := P1.bind_some.mp k3
  obtain ⟨m, rho⟩ := x
  obtain ⟨rfl, rfl, rfl⟩ := P1.pure_some.mp k4
  unfold Fl.wsForkMerge at c4
  obtain ⟨rho', B1, b1, d1, j1⟩ := P1.bind_some.mp c4
  obtain ⟨_, rfl, x, ht, rfl⟩ := P1.batch_spec d1
  obtain ⟨p0, B2, b2, d2, j2⟩ := P1.bind_some.mp j1
  obtain ⟨T, mu, eps, hT, rfl, rfl⟩ := P1.pscBegin_spec d2
  obtain ⟨y, B3, b3, d3, j3⟩ := P1.bind_some.mp j2
  obtain ⟨rm, p1⟩ := y
  have f1 := wsForkRounds_target d3
  obtain ⟨y, B4, b4, d4, j4⟩ := P1.bind_some.mp j3
  obtain ⟨sFv, p2⟩ := y
  obtain ⟨_, sentY, beta, v, _, _, rfl, rfl, hG⟩ := P1.pscEnds_spec d4
  obtain ⟨fvp, B5, b5, d5, j5⟩ := P1.bind_some.mp j4
  obtain ⟨_, rfl, rfl⟩ := P1.ask_some.mp d5
  obtain ⟨he, rfl, rfl⟩ := P1.pure_some.mp j5
  injection he with e1 e2
  subst e1
  have ex : tapeEps t = x := by
    rw [ht]
    rfl
  rw [ex, hT]
  exact congrArg some ((target_ended p1 _).trans f1).symm

/-- The slots of the claims' values follow one another. -/
theorem svAt (n s a : ℕ) (ha : a < n) :
    ((Array.range n).map (s + ·) ++ #[]).getD a 0 = s + a := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by simpa using ha)]
  simp [ha]

/-! ### The firsts -/

variable [scl : Scl] {M X0 : Type} (V : FullPar GE M X0)

/-- What is asked of the numbering of the batched sumcheck's end values. -/
structure Nums4 (num : IA V.D ⊕ IB V.D → ℕ) : Prop where
  h1 : num (Sum.inl (aH1 V.D)) = 1
  h2 : ∀ i : Fin V.D.ne, num (Sum.inl (aH2 V.D i)) = 2 + i.val
  h3 : ∀ a : Fin V.nW, num (Sum.inr (Sum.inr (V.num a))) = 2 + (1 + V.D.ne) + a.val

variable {V} {R : TailR} (W : TailM V.own.toOwn.tail R) {P : Pub} {hp : HPlan2} {g : ℕ} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
  {fo : Forest.Heard} (L : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
  (nz : NzT V.own.toOwn.tail (ksOf P hp) (t0.drop 1)) (x : V.XT) (g7 : Tg7)

include L in
/-- **The sums of squares.** -/
theorem first1 (hF : PscRun.Sized F) (hD : DimIs V.D (Verify.layerNumbers P hp g))
    (hhalf : gl.val (invE (ofNat 2)) * 2 = 1) :
    (V.own.toOwn.tail.s1.cl (aY1 V.own.toOwn.tail (t0.drop 1) x)
      (rdL gl V.own.toOwn.tail.s1.n (sentOf ((ksOf P hp).tc1 (t0.drop 1))))).1 =
      gl.val (levelRec P.rd.muV
        (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
        (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
        (orderDefault P.rd.muV) F4 ((ksOf P hp).tc1 (t0.drop 1))).target := by
  obtain ⟨v1, c1⟩ := L.c1
  obtain ⟨vW, hl, hsz, hrun⟩ := L.runW
  have hNS : ledNS P.y.h.xl = 9 := hD.NS.symm
  have hNI : P.y.NI = V.D.nNu := hD.NI.symm
  have hF' : PscRun.Sized ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork) := hF
  refine claim1 gl (shownW gl F4) V _ _
    (public_value gl F4 _ _ (levelIn_heard c1).2.2.1) hNI hNS hD.lPd.symm hhalf ?_ ?_ ?_ ?_
  · rw [List.size_toArray, L.lI]
    exact hD.lNI.symm
  · intro j
    rw [getD_toArray]
    rfl
  · intro s
    rw [L.gp, hNS, powers_val gl _ 9 s.val s.isLt]
    rfl
  · intro i s
    have hk : s.val + 9 * i.val < vW.size := by
      rw [hsz, hNS, hNI]
      have := i.isLt
      have := s.isLt
      omega
    have q := hideRun_shown hF' hrun hl (Fo.Later.refl F4) _ hk
    have e : H1.sW + 9 * i.val + s.val = F.next + (s.val + 9 * i.val) := by
      rw [L.sW]
      omega
    show gl.val ((sentOf (t0.drop 1)).getD (finProdFinEquiv (i, s)).val zeroE) =
      gl.val (F4.vp.getD (H1.sW + 9 * i.val + s.val) zeroE)
    rw [e, q]
    simp only [finProdFinEquiv_apply_val]

include L in
/-- **The products of the rows.** -/
theorem first2 :
    (V.own.toOwn.tail.s2.cl (aY2 W (ksOf P hp) (t0.drop 1) nz x g7)
      (rdL gl V.own.toOwn.tail.s2.n (sentOf (((ksOf P hp).tcP (t0.drop 1)).drop 1)))).1 =
      gl.val H1.tV.p.target := by
  obtain ⟨v2, c2⟩ := L.c2
  refine (cl2 V _ _).trans ?_
  rw [tsc_target_cl L.s8 c2, ← sent_zero]
  rfl

include L in
/-- **The terms.** -/
theorem first3 :
    (V.own.toOwn.tail.s3.cl (aZ2 W (ksOf P hp) (t0.drop 1) nz x g7)
      (rdL gl V.own.toOwn.tail.s3.n
        (sentOf ((((ksOf P hp).tcP (t0.drop 1)).drop 1).drop ((ksOf P hp).k2 + 3))))).1 =
      gl.val tT.p.target := by
  refine (cl3 V _ _).trans ?_
  rw [tsc_target_cl L.s1 L.c3, ← sent_zero]
  rfl

include L in
/-- **The gated products.** -/
theorem first5 (hN : Nums4 V W.w4.num) :
    (V.own.toOwn.tail.s5.cl (aZ4 W (ksOf P hp) (t0.drop 1) nz x g7)
      (rdL gl V.own.toOwn.tail.s5.n (sentOf ((ksOf P hp).tc5 (t0.drop 1))))).1 =
      gl.val (levelRec P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
        (orderRange P.rd.muH) G3 ((ksOf P hp).tc5 (t0.drop 1))).target := by
  obtain ⟨v5, c5⟩ := L.c5
  have q := stackVals_shown L.s2 L.c4 G3 (Fo.Later.refl G3) 1 (by omega)
  have e1 := aZ4_vals W (ksOf P hp) (t0.drop 1) nz x g7
    (Sum.inl (aH1 V.D) : IA V.D ⊕ IB V.D)
  have e2 : sentOf ((((ksOf P hp).tc4 (t0.drop 1)).drop 1).drop ((ksOf P hp).k4 + 2)) =
      stackVals hp.lamS ((ksOf P hp).tc4 (t0.drop 1)) := stackVals_at hp.lamS _
  rw [hN.h1, e2, ← q, ← (stack_slots4 L.c4).1] at e1
  exact claim5 gl (shownW gl G3) V _ _ (public_value gl G3 _ _ (levelIn_heard c5).2.2.1) e1

include L in
/-- **The routed experts' gated products.** -/
theorem first6 (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hLam : P.y.LamM = V.D.ne)
    (hN : Nums4 V W.w4.num) :
    (V.own.toOwn.tail.s6.cl (aY6 W (ksOf P hp) (t0.drop 1) nz x g7)
      (rdL gl V.own.toOwn.tail.s6.n (sentOf ((ksOf P hp).tc6 (t0.drop 1))))).1 =
      gl.val (levelRec P.rd.muH2
        ((drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray ++
          downFrom o.K.rs P.y.lfe ++ tT.r)
        (Road.Rows.start2 P.y.LamM o.K.sH1
          (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray)
        (orderRange P.rd.muH2) G3' ((ksOf P hp).tc6 (t0.drop 1))).target := by
  refine claim6 gl (shownW gl G3') V _ _ (LamM := P.y.LamM) (sH1 := o.K.sH1)
    (rhoM := (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray)
    (public_value gl G3' _ _ (levelIn_heard L.c6).2.2.1) hLam ?_ ?_ ?_
  · rw [List.size_toArray, L.lM]
    exact congrArg (· - 1) hD.ll.symm
  · intro j
    rw [getD_toArray]
    rfl
  · intro i
    have q := stackVals_shown L.s2 L.c4 G3' L.l3 (2 + i.val) (by
      have := i.isLt
      omega)
    have e : o.K.sA0 + (2 + i.val) = o.K.sH1 + 1 + i.val := by
      rw [(stack_slots4 L.c4).1]
      omega
    have e1 := aZ4_vals W (ksOf P hp) (t0.drop 1) nz x g7
      (Sum.inl (aH2 V.D i) : IA V.D ⊕ IB V.D)
    have e2 : sentOf ((((ksOf P hp).tc4 (t0.drop 1)).drop 1).drop ((ksOf P hp).k4 + 2)) =
        stackVals hp.lamS ((ksOf P hp).tc4 (t0.drop 1)) := stackVals_at hp.lamS _
    rw [hN.h2 i, e2, ← q, e] at e1
    exact e1

include L in
/-- **The merge.** -/
theorem first7 (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hg : (g == 0) = false)
    (hLam : P.y.LamM = V.D.ne) (hN : Nums4 V W.w4.num) :
    (V.own.toOwn.tail.s7.cl (aY7 W (ksOf P hp) (t0.drop 1) nz x g7)
      (rdL gl V.own.toOwn.tail.s7.n (sentOf (((ksOf P hp).tcW (t0.drop 1)).drop 1)))).1 =
      gl.val o.wo.p.target := by
  obtain ⟨cl, c7⟩ := L.c7
  have hW : V.nW = hp.NCL - 0 := by
    rw [OnBytes.Tie.Pv.Lay.At.nW_eq V _ hD]
    show hp.NCL - (if (g == 0) = true then 1 else 0) = _
    simp only [hg, Bool.false_eq_true, if_false]
  have hsz : ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]).size = V.nW := by
    rw [hW]
    simp
  refine claim7 gl (shownW gl G4) V _ _
    (public_value gl G4 _ _ (fork_target c7)) hsz ?_ ?_
  · intro a
    rw [powers_val gl _ _ a.val (by rw [hsz]; exact a.isLt)]
    rfl
  · intro a
    have ha : a.val < hp.NCL - 0 := by
      rw [← hW]
      exact a.isLt
    have q := stackVals_shown L.s2 L.c4 G4 (L.l3.trans L.l4) (2 + (1 + P.y.LamM) + a.val) (by omega)
    have e1 := aZ4_vals W (ksOf P hp) (t0.drop 1) nz x g7
      (Sum.inr (Sum.inr (V.num a)) : IA V.D ⊕ IB V.D)
    have e2 : sentOf ((((ksOf P hp).tc4 (t0.drop 1)).drop 1).drop ((ksOf P hp).k4 + 2)) =
        stackVals hp.lamS ((ksOf P hp).tc4 (t0.drop 1)) := stackVals_at hp.lamS _
    have e : o.K.sA0 + (2 + (1 + P.y.LamM) + a.val) = o.K.sV + a.val := by
      rw [(stack_slots4 L.c4).2]
      omega
    rw [hN.h3 a, ← hLam, e2, ← q, e, ← svAt (hp.NCL - 0) o.K.sV a.val ha] at e1
    exact e1

/-! ### All seven -/

/-- The seven targets g7 are those of K4's seven records. -/
structure TgRec (g7 : Tg7) (P : Pub) (hp : HPlan2) (o : Own) (t0 : Tape) (H1 : Heard) (tT : Tsc)
    (F4 G2 G3 G3' : Fork) : Prop where
  t1 : g7.t1 = (levelRec P.rd.muV
    (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
    (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
    (orderDefault P.rd.muV) F4 ((ksOf P hp).tc1 (t0.drop 1))).target
  t2 : g7.t2 = H1.tV.p.target
  t3 : g7.t3 = tT.p.target
  t4 : g7.t4 = (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop 1))).target
  t5 : g7.t5 = (levelRec P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
    (orderRange P.rd.muH) G3 ((ksOf P hp).tc5 (t0.drop 1))).target
  t6 : g7.t6 = (levelRec P.rd.muH2
    ((drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray ++
      downFrom o.K.rs P.y.lfe ++ tT.r)
    (Road.Rows.start2 P.y.LamM o.K.sH1
      (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray)
    (orderRange P.rd.muH2) G3' ((ksOf P hp).tc6 (t0.drop 1))).target
  t7 : g7.t7 = o.wo.p.target

omit scl in
/-- There are such targets. -/
theorem tg_exists (P : Pub) (hp : HPlan2) (o : Own) (t0 : Tape) (H1 : Heard) (tT : Tsc)
    (F4 G2 G3 G3' : Fork) : ∃ g7, TgRec g7 P hp o t0 H1 tT F4 G2 G3 G3' :=
  ⟨⟨_, _, _, _, _, _, _⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

include L in
/-- **The claims at K4's tape, under `Led7`**, at targets that are the records' (`TgRec`), from a
ledger with arrays of the right sizes, in a group that is not the first, under `DimIs`,
P.y.LamM = D.ne, the reading of 1/2, `Nums4` and `NzT`: if the fourth claimed sum is the reading of
its target. -/
theorem claims_of_led (hF : PscRun.Sized F) (hD : DimIs V.D (Verify.layerNumbers P hp g))
    (hg : (g == 0) = false) (hLam : P.y.LamM = V.D.ne) (hhalf : gl.val (invE (ofNat 2)) * 2 = 1)
    (hN : Nums4 V W.w4.num) (I : TgRec g7 P hp o t0 H1 tT F4 G2 G3 G3')
    (h4 : (V.own.toOwn.tail.s4.cl (aY4 W (ksOf P hp) (t0.drop 1) nz x g7)
      (rdL gl V.own.toOwn.tail.s4.n (sentOf (((ksOf P hp).tc4 (t0.drop 1)).drop 1)))).1 =
      gl.val g7.t4) :
    (k4Tail W P hp t0 nz (addsOf W (ksOf P hp) (t0.drop 1) nz x g7)).Claims x := by
  have h1 := (first1 L x hF hD hhalf).trans (congrArg gl.val I.t1.symm)
  have h2 := (first2 W L nz x g7).trans (congrArg gl.val I.t2.symm)
  have h3 := (first3 W L nz x g7).trans (congrArg gl.val I.t3.symm)
  have h5 := (first5 W L nz x g7 hN).trans (congrArg gl.val I.t5.symm)
  have h6 := (first6 W L nz x g7 hD hLam hN).trans (congrArg gl.val I.t6.symm)
  have h7 := (first7 W L nz x g7 hD hg hLam hN).trans (congrArg gl.val I.t7.symm)
  exact claims_of_firsts W (ksOf P hp) (t0.drop 1) nz x g7 h1 h2 h3 h4 h5 h6 h7

omit L in
/-- **The claims at K4's tape, where the hearing returns** on t0, from a ledger with arrays of the
right sizes, in a group that is not the first, under `DimIs`, P.y.LamM = D.ne, the reading of 1/2,
`Nums4` and `NzT`: there are K4's records and ledgers (`Led7`) and seven targets THAT ARE THE
RECORDS' (`TgRec`) such that the data read off the tape, with these targets and the states that the
claims name, meet `TailH.Claims`; IF at all such records, ledgers and targets the fourth claimed sum
is the reading of its target. (Without `TgRec` the conclusion would be free:
OnBytes/Desc/First/P1/ClaimsFree.lean.) -/
theorem k4_claims (hF : PscRun.Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hg : (g == 0) = false) (hD : DimIs V.D (Verify.layerNumbers P hp g))
    (hLam : P.y.LamM = V.D.ne) (hhalf : gl.val (invE (ofNat 2)) * 2 = 1)
    (hN : Nums4 V W.w4.num)
    (H4 : ∀ (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork) (g7 : Tg7),
      Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 →
      TgRec g7 P hp o t0 H1 tT F4 G2 G3 G3' →
      (V.own.toOwn.tail.s4.cl (aY4 W (ksOf P hp) (t0.drop 1) nz x g7)
        (rdL gl V.own.toOwn.tail.s4.n (sentOf (((ksOf P hp).tc4 (t0.drop 1)).drop 1)))).1 =
        gl.val g7.t4) :
    ∃ (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork) (g7 : Tg7),
      Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 ∧
      TgRec g7 P hp o t0 H1 tT F4 G2 G3 G3' ∧
      (k4Tail W P hp t0 nz (addsOf W (ksOf P hp) (t0.drop 1) nz x g7)).Claims x := by
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, Ld⟩ := own_led7 hF h hg
  obtain ⟨g7, I⟩ := tg_exists P hp o t0 H1 tT F4 G2 G3 G3'
  exact ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, g7, Ld, I,
    claims_of_led W Ld nz x g7 hF hD hg hLam hhalf hN I
      (H4 H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 g7 Ld I)⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4_claims
#print axioms OnBytes.Road.K4.claims_of_led
#print axioms OnBytes.Road.K4.first1
#print axioms OnBytes.Road.K4.first2
#print axioms OnBytes.Road.K4.first3
#print axioms OnBytes.Road.K4.first5
#print axioms OnBytes.Road.K4.first6
#print axioms OnBytes.Road.K4.first7
#print axioms OnBytes.Road.K4.fork_target
