-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ClaimsHeardFirst.lean: `TailH.Claims` AT THE DATA THAT ARE READ OFF K4's
TAPE, WHERE K4's HEARING RETURNS IN THE FIRST GROUP, at the library's value (`FullFPar.ownF`): six
of the seven equations on the claimed sums are PAID here; the fourth (the batched sumcheck) stays a
premise. Statements and proofs. The twin of Johnson/Road/K4/ClaimsHeard.lean, whose head names the
pieces and whose small tools are used here.

What is other in the first group. The tape is cut behind three points, `t0.drop (k0 g)`; the record
of calls and ledgers is `LedG` (Johnson/Road/K4/OwnLedgersG.lean); the batched sumcheck hears one
end value fewer; the merge's start form names one slot more, the embedding's, and the typed claimed
sum has one term more, the scalar that was sent in the weights' round (`claim7F`,
Johnson/Road/K4/ClaimsFirst.lean).

  `svAtE`, `svLast`: the merge's list of slots in the first group.
  `first1F`, `first2F`, `first3F`, `first5F`, `first6F`: under `LedG`, in whichever group the letter
    g names; `first7F`: in the first group.
  `TgRecF`, `tg_existsF`, `claims_of_ledF`, `k4_claimsF`: as in ClaimsHeard.lean.

Premises beside the hearing: the ledger in front has arrays of the right sizes; the library's sizes
are the program's (`DimIs`); P.y.LamM = D.ne; the reading of the program's 1/2 is 1/2; `Nums4` at
the value's letters that it shares with a later group's; `NzT`, which stands in the type of the
data.

Limits. THE FOURTH EQUATION IS A PREMISE. The data are `tailT` at the tape `t0.drop (k0 g)`: that
this is the tape behind three single drops is not said here. Nothing on the two further points in
front or on the embedding's claim itself. Equations between readings alone: nothing on soundness.
One direction: from a return.
-/
import Johnson.Road.K4.OwnLedgersG
import Johnson.Road.K4.ClaimsHeard
import Johnson.Road.K4.ClaimsFirst

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
open OnBytes.Desc.First.P1 (gl drawnOf sentOf tapeEps tapeCl Ks NzT Tg7 TailM TailR tailT aY1 aY2
  aZ2 aY4 aZ4 aY6 aY7 addsOf claims_of_firsts aZ4_vals levelRec levelIn_heard tscIn_heard
  publicPart_slot powers_val)

local notation "rdL" => Johnson.L5.Layers.rd

/-! ### The merge's slots in the first group -/

/-- The slots of the weight claims' values follow one another. -/
theorem svAtE (n s a e : ℕ) (ha : a < n) :
    ((Array.range n).map (s + ·) ++ #[e]).getD a 0 = s + a := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by simpa using ha)]
  simp [ha]

/-- The last slot is the embedding's. -/
theorem svLast (n s e : ℕ) : ((Array.range n).map (s + ·) ++ #[e]).getD n 0 = e := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right (by simp)]
  simp

/-! ### The firsts -/

variable [scl : Scl] {M X0 : Type} {V : FullFPar GE M X0}

variable {R : TailR} (W : TailM V.ownF.toOwn.tail R) {P : Pub} {hp : HPlan2} {g : ℕ} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
  {fo : Forest.Heard} (L : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
  (nz : NzT V.ownF.toOwn.tail (ksOf P hp) (t0.drop (k0 g))) (x : V.ofp.fs.X3) (g7 : Tg7)

include L in
/-- **The sums of squares.** -/
theorem first1F (hF : PscRun.Sized F) (hD : DimIs V.D (Verify.layerNumbers P hp g))
    (hhalf : gl.val (invE (ofNat 2)) * 2 = 1) :
    (V.ownF.toOwn.tail.s1.cl (aY1 V.ownF.toOwn.tail (t0.drop (k0 g)) x)
      (rdL gl V.ownF.toOwn.tail.s1.n (sentOf ((ksOf P hp).tc1 (t0.drop (k0 g)))))).1 =
      gl.val (levelRec P.rd.muV
        (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
        (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
        (orderDefault P.rd.muV) F4 ((ksOf P hp).tc1 (t0.drop (k0 g)))).target := by
  obtain ⟨v1, c1⟩ := L.c1
  obtain ⟨vW, hl, hsz, hrun⟩ := L.runW
  have hNS : ledNS P.y.h.xl = 9 := hD.NS.symm
  have hNI : P.y.NI = V.D.nNu := hD.NI.symm
  have hF' : PscRun.Sized ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork) := hF
  refine claim1F gl (shownW gl F4) V _ _
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
    show gl.val ((sentOf (t0.drop (k0 g))).getD (finProdFinEquiv (i, s)).val zeroE) =
      gl.val (F4.vp.getD (H1.sW + 9 * i.val + s.val) zeroE)
    rw [e, q]
    simp only [finProdFinEquiv_apply_val]

include L in
/-- **The products of the rows.** -/
theorem first2F :
    (V.ownF.toOwn.tail.s2.cl (aY2 W (ksOf P hp) (t0.drop (k0 g)) nz x g7)
      (rdL gl V.ownF.toOwn.tail.s2.n (sentOf (((ksOf P hp).tcP (t0.drop (k0 g))).drop 1)))).1 =
      gl.val H1.tV.p.target := by
  obtain ⟨v2, c2⟩ := L.c2
  refine (cl2F V _ _).trans ?_
  rw [tsc_target_cl L.s8 c2, ← sent_zero]
  rfl

include L in
/-- **The terms.** -/
theorem first3F :
    (V.ownF.toOwn.tail.s3.cl (aZ2 W (ksOf P hp) (t0.drop (k0 g)) nz x g7)
      (rdL gl V.ownF.toOwn.tail.s3.n
        (sentOf ((((ksOf P hp).tcP (t0.drop (k0 g))).drop 1).drop ((ksOf P hp).k2 + 3))))).1 =
      gl.val tT.p.target := by
  refine (cl3F V _ _).trans ?_
  rw [tsc_target_cl L.s1 L.c3, ← sent_zero]
  rfl

include L in
/-- **The gated products.** -/
theorem first5F (hN : Nums4 V.toFullPar W.w4.num) :
    (V.ownF.toOwn.tail.s5.cl (aZ4 W (ksOf P hp) (t0.drop (k0 g)) nz x g7)
      (rdL gl V.ownF.toOwn.tail.s5.n (sentOf ((ksOf P hp).tc5 (t0.drop (k0 g)))))).1 =
      gl.val (levelRec P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
        (orderRange P.rd.muH) G3 ((ksOf P hp).tc5 (t0.drop (k0 g)))).target := by
  obtain ⟨v5, c5⟩ := L.c5
  have q := stackVals_shown L.s2 L.c4 G3 (Fo.Later.refl G3) 1 (by omega)
  have e1 := aZ4_vals W (ksOf P hp) (t0.drop (k0 g)) nz x g7
    (Sum.inl (aH1 V.D) : IA V.D ⊕ IB V.D)
  have e2 : sentOf ((((ksOf P hp).tc4 (t0.drop (k0 g))).drop 1).drop ((ksOf P hp).k4 + 2)) =
      stackVals hp.lamS ((ksOf P hp).tc4 (t0.drop (k0 g))) := stackVals_at hp.lamS _
  rw [hN.h1, e2, ← q, ← (stack_slots4 L.c4).1] at e1
  exact claim5F gl (shownW gl G3) V _ _ (public_value gl G3 _ _ (levelIn_heard c5).2.2.1) e1

include L in
/-- **The routed experts' gated products.** -/
theorem first6F (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hLam : P.y.LamM = V.D.ne)
    (hN : Nums4 V.toFullPar W.w4.num) :
    (V.ownF.toOwn.tail.s6.cl (aY6 W (ksOf P hp) (t0.drop (k0 g)) nz x g7)
      (rdL gl V.ownF.toOwn.tail.s6.n (sentOf ((ksOf P hp).tc6 (t0.drop (k0 g)))))).1 =
      gl.val (levelRec P.rd.muH2
        ((drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray ++
          downFrom o.K.rs P.y.lfe ++ tT.r)
        (Road.Rows.start2 P.y.LamM o.K.sH1
          (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray)
        (orderRange P.rd.muH2) G3' ((ksOf P hp).tc6 (t0.drop (k0 g)))).target := by
  refine claim6F gl (shownW gl G3') V _ _ (LamM := P.y.LamM) (sH1 := o.K.sH1)
    (rhoM := (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray)
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
    have e1 := aZ4_vals W (ksOf P hp) (t0.drop (k0 g)) nz x g7
      (Sum.inl (aH2 V.D i) : IA V.D ⊕ IB V.D)
    have e2 : sentOf ((((ksOf P hp).tc4 (t0.drop (k0 g))).drop 1).drop ((ksOf P hp).k4 + 2)) =
        stackVals hp.lamS ((ksOf P hp).tc4 (t0.drop (k0 g))) := stackVals_at hp.lamS _
    rw [hN.h2 i, e2, ← q, e] at e1
    exact e1

include L in
/-- **The merge, with the embedding's claim.** -/
theorem first7F (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hg : (g == 0) = true)
    (hLam : P.y.LamM = V.D.ne) (hN : Nums4 V.toFullPar W.w4.num) :
    (V.ownF.toOwn.tail.s7.cl (aY7 W (ksOf P hp) (t0.drop (k0 g)) nz x g7)
      (rdL gl V.ownF.toOwn.tail.s7.n (sentOf (((ksOf P hp).tcW (t0.drop (k0 g))).drop 1)))).1 =
      gl.val o.wo.p.target := by
  obtain ⟨cl, c7⟩ := L.c7
  have hW : V.nW = hp.NCL - 1 := by
    rw [OnBytes.Tie.Pv.Lay.At.nW_eq V.toFullPar _ hD]
    show hp.NCL - (if (g == 0) = true then 1 else 0) = _
    simp only [hg, if_true]
  have hsl : mergeSlots hp g o = (Array.range (hp.NCL - 1)).map (o.K.sV + ·) ++ #[o.sVE] := by
    unfold mergeSlots
    simp only [hg, if_true]
  have c4 := L.c4
  simp only [hg, if_true] at c4
  rw [hsl] at c7
  have hsz : ((Array.range (hp.NCL - 1)).map (o.K.sV + ·) ++ #[o.sVE]).size = V.nW + 1 := by
    rw [hW]
    simp
  refine claim7F gl (shownW gl G5) V _ _
    (public_value gl G5 _ _ (fork_target c7)) hsz ?_ ?_ ?_
  · intro a ha
    rw [powers_val gl _ _ a (by rw [hsz]; exact ha), L.u5e]
    rfl
  · intro a
    have ha : a.val < hp.NCL - 1 := by
      rw [← hW]
      exact a.isLt
    have q := stackVals_shown L.s2 c4 G5 ((L.l3.trans L.l4).trans L.l5)
      (2 + (1 + P.y.LamM) + a.val) (by omega)
    have e1 := aZ4_vals W (ksOf P hp) (t0.drop (k0 g)) nz x g7
      (Sum.inr (Sum.inr (V.num a)) : IA V.D ⊕ IB V.D)
    have e2 : sentOf ((((ksOf P hp).tc4 (t0.drop (k0 g))).drop 1).drop ((ksOf P hp).k4 + 2)) =
        stackVals hp.lamS ((ksOf P hp).tc4 (t0.drop (k0 g))) := stackVals_at hp.lamS _
    have e : o.K.sA0 + (2 + (1 + P.y.LamM) + a.val) = o.K.sV + a.val := by
      rw [(stack_slots4 c4).2]
      omega
    rw [hN.h3 a, ← hLam, e2, ← q, e, ← svAtE (hp.NCL - 1) o.K.sV a.val o.sVE ha] at e1
    exact e1
  · have q := (L.emb hg).2 G5 (Fo.Later.refl G5)
    show gl.val ((sentOf ((ksOf P hp).tcW (t0.drop (k0 g)))).getD 0 zeroE) =
      gl.val (G5.vp.getD (((Array.range (hp.NCL - 1)).map (o.K.sV + ·) ++ #[o.sVE]).getD V.nW 0)
        zeroE)
    rw [hW, svLast, q]

/-! ### All seven -/

/-- The seven targets g7 are those of K4's seven records. -/
structure TgRecF (g7 : Tg7) (P : Pub) (hp : HPlan2) (g : ℕ) (o : Own) (t0 : Tape) (H1 : Heard)
    (tT : Tsc) (F4 G2 G3 G3' : Fork) : Prop where
  t1 : g7.t1 = (levelRec P.rd.muV
    (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
    (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
    (orderDefault P.rd.muV) F4 ((ksOf P hp).tc1 (t0.drop (k0 g)))).target
  t2 : g7.t2 = H1.tV.p.target
  t3 : g7.t3 = tT.p.target
  t4 : g7.t4 = (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop (k0 g)))).target
  t5 : g7.t5 = (levelRec P.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
    (orderRange P.rd.muH) G3 ((ksOf P hp).tc5 (t0.drop (k0 g)))).target
  t6 : g7.t6 = (levelRec P.rd.muH2
    ((drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray ++
      downFrom o.K.rs P.y.lfe ++ tT.r)
    (Road.Rows.start2 P.y.LamM o.K.sH1
      (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray)
    (orderRange P.rd.muH2) G3' ((ksOf P hp).tc6 (t0.drop (k0 g)))).target
  t7 : g7.t7 = o.wo.p.target

omit scl in
/-- There are such targets. -/
theorem tg_existsF (P : Pub) (hp : HPlan2) (g : ℕ) (o : Own) (t0 : Tape) (H1 : Heard) (tT : Tsc)
    (F4 G2 G3 G3' : Fork) : ∃ g7, TgRecF g7 P hp g o t0 H1 tT F4 G2 G3 G3' :=
  ⟨⟨_, _, _, _, _, _, _⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

include L in
/-- **The claims at K4's tape in the first group, under `LedG`**, at targets that are the records'
(`TgRecF`), from a ledger with arrays of the right sizes, under `DimIs`, P.y.LamM = D.ne, the
reading of 1/2, `Nums4` and `NzT`: if the fourth claimed sum is the reading of its target. -/
theorem claims_of_ledF (hF : PscRun.Sized F) (hD : DimIs V.D (Verify.layerNumbers P hp g))
    (hg : (g == 0) = true) (hLam : P.y.LamM = V.D.ne) (hhalf : gl.val (invE (ofNat 2)) * 2 = 1)
    (hN : Nums4 V.toFullPar W.w4.num) (I : TgRecF g7 P hp g o t0 H1 tT F4 G2 G3 G3')
    (h4 : (V.ownF.toOwn.tail.s4.cl (aY4 W (ksOf P hp) (t0.drop (k0 g)) nz x g7)
      (rdL gl V.ownF.toOwn.tail.s4.n (sentOf (((ksOf P hp).tc4 (t0.drop (k0 g))).drop 1)))).1 =
      gl.val g7.t4) :
    (tailT W (ksOf P hp) (t0.drop (k0 g)) nz
      (addsOf W (ksOf P hp) (t0.drop (k0 g)) nz x g7)).Claims x := by
  have h1 := (first1F L x hF hD hhalf).trans (congrArg gl.val I.t1.symm)
  have h2 := (first2F W L nz x g7).trans (congrArg gl.val I.t2.symm)
  have h3 := (first3F W L nz x g7).trans (congrArg gl.val I.t3.symm)
  have h5 := (first5F W L nz x g7 hN).trans (congrArg gl.val I.t5.symm)
  have h6 := (first6F W L nz x g7 hD hLam hN).trans (congrArg gl.val I.t6.symm)
  have h7 := (first7F W L nz x g7 hD hg hLam hN).trans (congrArg gl.val I.t7.symm)
  exact claims_of_firsts W (ksOf P hp) (t0.drop (k0 g)) nz x g7 h1 h2 h3 h4 h5 h6 h7

omit L in
/-- **The claims at K4's tape, where the hearing returns in the first group** on t0, from a ledger
with arrays of the right sizes, under `DimIs`, P.y.LamM = D.ne, the reading of 1/2, `Nums4` and
`NzT`: there are K4's records and ledgers (`LedG`) and seven targets THAT ARE THE RECORDS'
(`TgRecF`) such that the data read off the tape behind the three points, with these targets and the
states that the claims name, meet `TailH.Claims`; IF at all such records, ledgers and targets the
fourth claimed sum is the reading of its target. -/
theorem k4_claimsF (hF : PscRun.Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hg : (g == 0) = true) (hD : DimIs V.D (Verify.layerNumbers P hp g))
    (hLam : P.y.LamM = V.D.ne) (hhalf : gl.val (invE (ofNat 2)) * 2 = 1)
    (hN : Nums4 V.toFullPar W.w4.num)
    (H4 : ∀ (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork)
        (u5 : Tape) (g7 : Tg7),
      LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5 →
      TgRecF g7 P hp g o t0 H1 tT F4 G2 G3 G3' →
      (V.ownF.toOwn.tail.s4.cl (aY4 W (ksOf P hp) (t0.drop (k0 g)) nz x g7)
        (rdL gl V.ownF.toOwn.tail.s4.n (sentOf (((ksOf P hp).tc4 (t0.drop (k0 g))).drop 1)))).1 =
        gl.val g7.t4) :
    ∃ (H1 : Heard) (hd2 : Level) (tT : Tsc) (F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork) (u5 : Tape)
        (g7 : Tg7),
      LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5 ∧
      TgRecF g7 P hp g o t0 H1 tT F4 G2 G3 G3' ∧
      (tailT W (ksOf P hp) (t0.drop (k0 g)) nz
        (addsOf W (ksOf P hp) (t0.drop (k0 g)) nz x g7)).Claims x := by
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, Ld⟩ := own_ledG hF h
  obtain ⟨g7, I⟩ := tg_existsF P hp g o t0 H1 tT F4 G2 G3 G3'
  exact ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, g7, Ld, I,
    claims_of_ledF W Ld nz x g7 hF hD hg hLam hhalf hN I
      (H4 H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5 g7 Ld I)⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4_claimsF
#print axioms OnBytes.Road.K4.claims_of_ledF
#print axioms OnBytes.Road.K4.first1F
#print axioms OnBytes.Road.K4.first2F
#print axioms OnBytes.Road.K4.first3F
#print axioms OnBytes.Road.K4.first5F
#print axioms OnBytes.Road.K4.first6F
#print axioms OnBytes.Road.K4.first7F
