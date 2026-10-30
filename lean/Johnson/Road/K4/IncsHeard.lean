-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/IncsHeard.lean: THE TYPED HALF OF THE CONDITION (D2), AT THE STATES THAT ARE READ
OFF K4's TAPE, WHERE K4's HEARING RETURNS, in a group that is not the first, at the library's value
(`FullPar.own`), for six of the seven sumchecks. Statements and proofs. The twin, for the masks, of
Johnson/Road/K4/ClaimsHeard.lean.

Each says: `Y.inc st m = maskSum Hl C mask - entSum C entry` (Johnson/Road/K4/OwnD2.lean's hinc), at
Y the stage's parameters, st the state that Johnson/Road/K4's data choose for the stage (`aS1` …
`aS7`, OnBytes/Desc/First/P1/TailAdds.lean), C the start form of K4's text, and Hl ANY ledger that
is later than the one which the hearing leaves.

PAID HERE, from `Led7` (Johnson/Road/K4/OwnLedgers.lean): of the premises of `hinc1` … `hinc7`
(Johnson/Road/K4/Incs.lean): the points, the powers, the sizes; and the ledger's side of the factors
(OnBytes/Desc/First/K4/FactorUnder.lean): 1 under the slots of the sums and of the two claimed sums,
the challenge of the batched sumcheck's round in the further variable under its end values'.

  `hincH1`, `hincH2`, `hincH3`, `hincH5`, `hincH6`, `hincH7`.

STILL PREMISES: (hm) the entry of m under the value's name of a mask entry is the mask's entry at
K4's slot; (hbe) in the fifth, sixth and seventh: the typed factor in the state is the reading of
that challenge. Beside them `DimIs`, P.y.LamM = D.ne, the reading of 1/2.

Limits. The fourth form is not here. Equations alone: nothing on soundness or on what a mask hides.
One direction: from a return. A group that is not the first.
-/
import Johnson.Road.K4.ClaimsHeard
import Johnson.Road.K4.Incs
import OnBytes.Desc.First.K4.FactorUnder

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
open OnBytes.Desc.First.Grow (Grows)
open OnBytes.Tie.Pv.Lay.At (DimIs)
open OnBytes.Desc.First.P1 (gl drawnOf sentOf tapeEps Ks NzT Tg7 TailM TailR aS1 aS2 aS3 aS5 aS6 aS7
  aZ4 powers_val)

variable [scl : Scl] {M X0 : Type} {V : FullPar GE M X0}
  {R : TailR} (W : TailM V.own.toOwn.tail R) {P : Pub} {hp : HPlan2} {g : ℕ} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
  {fo : Forest.Heard} (L : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
  (nz : NzT V.own.toOwn.tail (ksOf P hp) (t0.drop 1)) (x : V.XT) (g7 : Tg7)
  (Hl : Fork) (hHl : Fo.Later G Hl) (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) (m : V.J → GE)

include L hHl in
/-- **The sums of squares.** -/
theorem hincH1 (hF : PscRun.Sized F) (hD : DimIs V.D (Verify.layerNumbers P hp g))
    (hhalf : gl.val (invE (ofNat 2)) * 2 = 1)
    (hm : ∀ (i : Fin V.D.nNu) (s : Fin 9),
      m (V.nr.sq.mkS i s) = mask (H1.sW + 9 * i.val + s.val)) :
    V.own.toOwn.tail.s1.L.T.par.inc (aS1 V.own.toOwn.tail (ksOf P hp) (t0.drop 1) x) m =
      maskSum Hl (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1 mask -
      entSum (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1 entry := by
  obtain ⟨v1, c1⟩ := L.c1
  obtain ⟨vW, _, hsz, hrun⟩ := L.runW
  have hNS : ledNS P.y.h.xl = 9 := hD.NS.symm
  have hNI : P.y.NI = V.D.nNu := hD.NI.symm
  have hF' : PscRun.Sized ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork) := hF
  have lH : Fo.Later F4 Hl := ((later_fo (Grows.later c1)).trans L.g7).trans hHl
  refine hinc1 V Hl mask entry _ m hNI hNS hD.lPd.symm hhalf ?_ ?_ ?_ ?_
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
    have q := hideRun_factor hF' hrun lH _ hk
    have e : H1.sW + 9 * i.val + s.val = F.next + (s.val + 9 * i.val) := by
      rw [L.sW]
      omega
    rw [hm i s, e, q, gl.one, one_mul]

include L hHl in
/-- **The products of the rows.** -/
theorem hincH2 (hm : m V.nr.rows.rJ = mask H1.tV.sCl) :
    V.own.toOwn.tail.s2.L.T.par.inc (aS2 W (ksOf P hp) (t0.drop 1) nz x g7) m =
      maskSum Hl (Aff.slot H1.tV.sCl) mask - entSum (Aff.slot H1.tV.sCl) entry := by
  obtain ⟨v2, c2⟩ := L.c2
  exact hinc2 V Hl mask entry _ m
    (by rw [hm, tsc_cl_factor L.s8 c2 Hl (L.g1.trans hHl), gl.one, one_mul])

include L hHl in
/-- **The terms.** -/
theorem hincH3 (hm : m V.rT = mask tT.sCl) :
    V.own.toOwn.tail.s3.L.T.par.inc (aS3 W (ksOf P hp) (t0.drop 1) nz x g7) m =
      maskSum Hl (Aff.slot tT.sCl) mask - entSum (Aff.slot tT.sCl) entry :=
  hinc3 V Hl mask entry _ m
    (by rw [hm, tsc_cl_factor L.s1 L.c3 Hl (L.g1'.trans hHl), gl.one, one_mul])

include L hHl in
/-- **The gated products.** -/
theorem hincH5
    (hbe : (V.st5 (aZ4 W (ksOf P hp) (t0.drop 1) nz x g7).2).be =
      gl.val (stackY hp.lamS ((ksOf P hp).tc4 (t0.drop 1))).2.2)
    (hm : m (V.cI (.inl (aH1 V.D))) = mask o.K.sH1) :
    V.own.toOwn.tail.s5.L.T.par.inc (aS5 W (ksOf P hp) (t0.drop 1) nz x g7) m =
      maskSum Hl (Aff.slot o.K.sH1) mask - entSum (Aff.slot o.K.sH1) entry := by
  have q := stack_factor L.s2 L.c4 Hl (L.g3.trans hHl) 1 (by omega)
  rw [← (stack_slots4 L.c4).1] at q
  exact hinc5 V Hl mask entry (V.st5 (aZ4 W (ksOf P hp) (t0.drop 1) nz x g7).2) m
    (by rw [hbe, q]) hm

include L hHl in
/-- **The routed experts' gated products.** -/
theorem hincH6 (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hLam : P.y.LamM = V.D.ne)
    (hbe : (V.st6 (aZ4 W (ksOf P hp) (t0.drop 1) nz x g7).2).be =
      gl.val (stackY hp.lamS ((ksOf P hp).tc4 (t0.drop 1))).2.2)
    (hm : ∀ i : Fin V.D.ne, m (V.cI (.inl (aH2 V.D i))) = mask (o.K.sH1 + 1 + i.val)) :
    V.own.toOwn.tail.s6.L.T.par.inc (aS6 W (ksOf P hp) (t0.drop 1) nz x g7) m =
      maskSum Hl (Road.Rows.start2 P.y.LamM o.K.sH1
        (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray) mask -
      entSum (Road.Rows.start2 P.y.LamM o.K.sH1
        (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray) entry := by
  refine hinc6 V Hl mask entry
    (V.st6 (aZ4 W (ksOf P hp) (t0.drop 1) nz x g7).2, Johnson.L5.Layers.rd gl (V.D.lL - 1)
      (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1))) m
    (LamM := P.y.LamM) (sH1 := o.K.sH1)
    (rhoM := (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray)
    hLam ?_ ?_ ?_ hm
  · rw [List.size_toArray, L.lM]
    exact congrArg (· - 1) hD.ll.symm
  · intro j
    rw [getD_toArray]
    rfl
  · intro i
    have q := stack_factor L.s2 L.c4 Hl (L.g3.trans hHl) (2 + i.val) (by
      have := i.isLt
      omega)
    have e : o.K.sA0 + (2 + i.val) = o.K.sH1 + 1 + i.val := by
      rw [(stack_slots4 L.c4).1]
      omega
    rw [e] at q
    rw [hbe, q]

include L hHl in
/-- **The merge.** -/
theorem hincH7 (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hg : (g == 0) = false)
    (hbe : ∀ a : Fin V.nW,
      V.wp0.wt.be a (V.ip.st7 V.num (aZ4 W (ksOf P hp) (t0.drop 1) nz x g7).2) =
      gl.val (stackY hp.lamS ((ksOf P hp).tc4 (t0.drop 1))).2.2)
    (hm : ∀ a : Fin V.nW, m (V.wp0.wt.nm a) = mask (o.K.sV + a.val)) :
    V.own.toOwn.tail.s7.L.T.par.inc (aS7 W (ksOf P hp) (t0.drop 1) nz x g7) m =
      maskSum Hl (wsForkStart ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[])
        (powers (tapeEps ((ksOf P hp).tcW (t0.drop 1)))
          ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]).size)) mask -
      entSum (wsForkStart ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[])
        (powers (tapeEps ((ksOf P hp).tcW (t0.drop 1)))
          ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]).size)) entry := by
  have hW : V.nW = hp.NCL - 0 := by
    rw [OnBytes.Tie.Pv.Lay.At.nW_eq V _ hD]
    show hp.NCL - (if (g == 0) = true then 1 else 0) = _
    simp only [hg, Bool.false_eq_true, if_false]
  have hsz : ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]).size = V.nW := by
    rw [hW]
    simp
  refine hinc7 V Hl mask entry
    (V.ip.st7 V.num (aZ4 W (ksOf P hp) (t0.drop 1) nz x g7).2,
      gl.val (tapeEps ((ksOf P hp).tcW (t0.drop 1)))) m hsz ?_ ?_ ?_
  · intro a
    rw [powers_val gl _ _ a.val (by rw [hsz]; exact a.isLt)]
  · intro a
    have ha : a.val < hp.NCL - 0 := by
      rw [← hW]
      exact a.isLt
    have q := stack_factor L.s2 L.c4 Hl (L.g3.trans hHl) (2 + (1 + P.y.LamM) + a.val) (by omega)
    have e : o.K.sA0 + (2 + (1 + P.y.LamM) + a.val) = o.K.sV + a.val := by
      rw [(stack_slots4 L.c4).2]
      omega
    rw [e] at q
    rw [hbe a, svAt (hp.NCL - 0) o.K.sV a.val ha, q]
  · intro a
    have ha : a.val < hp.NCL - 0 := by
      rw [← hW]
      exact a.isLt
    rw [hm a, svAt (hp.NCL - 0) o.K.sV a.val ha]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hincH1
#print axioms OnBytes.Road.K4.hincH2
#print axioms OnBytes.Road.K4.hincH3
#print axioms OnBytes.Road.K4.hincH5
#print axioms OnBytes.Road.K4.hincH6
#print axioms OnBytes.Road.K4.hincH7
