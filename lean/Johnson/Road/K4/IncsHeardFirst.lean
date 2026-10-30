-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/IncsHeardFirst.lean: THE FIRST GROUP's TWIN OF Johnson/Road/K4/IncsHeard.lean: THE
TYPED HALF OF THE CONDITION (D2), AT THE STATES THAT ARE READ OFF K4's TAPE, WHERE K4's HEARING
RETURNS, at the library's value of the first sub-proof (`FullFPar.ownF`), for six of the seven
sumchecks. Statements and proofs. That file's head says how each is stated.

  `inc7F`: the merge's incoming masks' form in the first group, written out: the formula of `inc7`
    (Johnson/Road/K4/IncTyped.lean) and the next power of the drawn element times the entry under
    the name mkE (by `WFirstL.inc_sum`, Cb/Pv/Lay/WeightsFirst.lean).
  `hinc7F`: the twin of `hinc7` (Johnson/Road/K4/Incs.lean): the list of slots has one member more;
    the ledger's factor under it reads 1.
  `hincH1F`, `hincH2F`, `hincH3F`, `hincH5F`, `hincH6F`: under `LedG`
    (Johnson/Road/K4/OwnLedgersG.lean), in whichever group the letter g names: IncsHeard.lean's
    statements and proofs turned to these letters by a program (FullFPar for FullPar; the chain
    V.ownF.toOwn.tail; `LedG`; the tape t0.drop (k0 g); the statement in front with three points);
    `hinc1` … `hinc6` are taken as they stand, at V.toFullPar.
  `hincH7F`: in the first group, by hand: the start form runs over `mergeSlots hp g o`
    (OnBytes/Desc/First/K4/MergeClaims.lean); the embedding's value was laid with the factor 1.

STILL PREMISES: (hm) the entry of m under the value's name of a mask entry is the mask's entry at
K4's slot, in the seventh also (hmE) at the embedding's slot; (hbe) in the fifth, sixth and seventh:
the typed factor in the state is the reading of the batched sumcheck's further challenge. Beside
them `DimIs`, P.y.LamM = D.ne, the reading of 1/2.

Limits. The fourth form is not here. Equations alone: nothing on soundness or on what a mask hides.
One direction: from a return.
-/
import Johnson.Road.K4.IncsHeard
import Johnson.Road.K4.ClaimsHeardFirst

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
  aZ4 powers_val claimsIn_spec)

/-! ### The merge's form in the first group -/

/-- The merge, with the entry under the name of the sent scalar's mask entry. -/
theorem inc7F {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullFPar E M X)
    (st : P.wf.St1) (m : P.J → E) :
    P.ownF.toOwn.tail.s7.L.T.par.inc st m =
      ∑ a : Fin P.nW, st.2 ^ (a : ℕ) * (m (P.wp0.wt.nm a) * P.wp0.wt.be a st.1.1) +
        st.2 ^ P.nW * m P.mkE :=
  P.wf.inc_sum st m

/-- **The merge, with the embedding's slot.** -/
theorem hinc7F [scl : Scl] {M X : Type} (P : FullFPar GE M X) (H : Fork) (mask : ℕ → GE)
    (entry : ℕ → ℕ → ℕ → GE) (st : P.wf.St1) (m : P.J → GE) {sv : Array Nat} {rho : Array E}
    (hn : sv.size = P.nW + 1)
    (hr : ∀ a, a < P.nW + 1 → gl.val (rho.getD a zeroE) = st.2 ^ a)
    (hb : ∀ a : Fin P.nW, P.wp0.wt.be a st.1.1 = gl.val (H.mf.getD (sv.getD a.val 0) zeroE))
    (hbE : gl.val (H.mf.getD (sv.getD P.nW 0) zeroE) = 1)
    (hm : ∀ a : Fin P.nW, m (P.wp0.wt.nm a) = mask (sv.getD a.val 0))
    (hmE : m P.mkE = mask (sv.getD P.nW 0)) :
    P.ownF.toOwn.tail.s7.L.T.par.inc st m =
      maskSum H (wsForkStart sv rho) mask - entSum (wsForkStart sv rho) entry := by
  have z0 : (wsForkStart sv rho).value gl zeroWorld = 0 := by
    rw [forkStart_value]
    simp [zeroWorld]
  rw [inc7F, mask_less, z0, sub_zero, forkStart_value, hn, Finset.sum_range_succ,
    Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [hr a.val (Nat.lt_succ_of_lt a.isLt), hb a, hm a]
    show _ = _ * (gl.val (H.mf.getD (sv.getD a.val 0) zeroE) * mask (sv.getD a.val 0))
    ring
  · rw [hr P.nW (Nat.lt_succ_self _), hmE]
    show _ = _ * (gl.val (H.mf.getD (sv.getD P.nW 0) zeroE) * mask (sv.getD P.nW 0))
    rw [hbE, one_mul]

/-! ### At a hearing -/

variable [scl : Scl] {M X0 : Type} {V : FullFPar GE M X0}
  {R : TailR} (W : TailM V.ownF.toOwn.tail R) {P : Pub} {hp : HPlan2} {g : ℕ} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
  {fo : Forest.Heard} (L : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
  (nz : NzT V.ownF.toOwn.tail (ksOf P hp) (t0.drop (k0 g))) (x : V.ofp.fs.X3) (g7 : Tg7)
  (Hl : Fork) (hHl : Fo.Later G Hl) (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) (m : V.J → GE)

include L hHl in
/-- **The sums of squares.** -/
theorem hincH1F (hF : PscRun.Sized F) (hD : DimIs V.D (Verify.layerNumbers P hp g))
    (hhalf : gl.val (invE (ofNat 2)) * 2 = 1)
    (hm : ∀ (i : Fin V.D.nNu) (s : Fin 9),
      m (V.nr.sq.mkS i s) = mask (H1.sW + 9 * i.val + s.val)) :
    V.ownF.toOwn.tail.s1.L.T.par.inc (aS1 V.ownF.toOwn.tail (ksOf P hp) (t0.drop (k0 g)) x) m =
      maskSum Hl (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
          mask -
        entSum (normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
          entry := by
  obtain ⟨v1, c1⟩ := L.c1
  obtain ⟨vW, _, hsz, hrun⟩ := L.runW
  have hNS : ledNS P.y.h.xl = 9 := hD.NS.symm
  have hNI : P.y.NI = V.D.nNu := hD.NI.symm
  have hF' : PscRun.Sized ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork) := hF
  have lH : Fo.Later F4 Hl := ((later_fo (Grows.later c1)).trans L.g7).trans hHl
  refine hinc1 V.toFullPar Hl mask entry _ m hNI hNS hD.lPd.symm hhalf ?_ ?_ ?_ ?_
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
theorem hincH2F (hm : m V.nr.rows.rJ = mask H1.tV.sCl) :
    V.ownF.toOwn.tail.s2.L.T.par.inc (aS2 W (ksOf P hp) (t0.drop (k0 g)) nz x g7) m =
      maskSum Hl (Aff.slot H1.tV.sCl) mask - entSum (Aff.slot H1.tV.sCl) entry := by
  obtain ⟨v2, c2⟩ := L.c2
  exact hinc2 V.toFullPar Hl mask entry _ m
    (by rw [hm, tsc_cl_factor L.s8 c2 Hl (L.g1.trans hHl), gl.one, one_mul])

include L hHl in
/-- **The terms.** -/
theorem hincH3F (hm : m V.rT = mask tT.sCl) :
    V.ownF.toOwn.tail.s3.L.T.par.inc (aS3 W (ksOf P hp) (t0.drop (k0 g)) nz x g7) m =
      maskSum Hl (Aff.slot tT.sCl) mask - entSum (Aff.slot tT.sCl) entry :=
  hinc3 V.toFullPar Hl mask entry _ m
    (by rw [hm, tsc_cl_factor L.s1 L.c3 Hl (L.g1'.trans hHl), gl.one, one_mul])

include L hHl in
/-- **The gated products.** -/
theorem hincH5F
    (hbe : (V.st5 (aZ4 W (ksOf P hp) (t0.drop (k0 g)) nz x g7).2).be =
      gl.val (stackY hp.lamS ((ksOf P hp).tc4 (t0.drop (k0 g)))).2.2)
    (hm : m (V.cI (.inl (aH1 V.D))) = mask o.K.sH1) :
    V.ownF.toOwn.tail.s5.L.T.par.inc (aS5 W (ksOf P hp) (t0.drop (k0 g)) nz x g7) m =
      maskSum Hl (Aff.slot o.K.sH1) mask - entSum (Aff.slot o.K.sH1) entry := by
  have q := stack_factor L.s2 L.c4 Hl (L.g3.trans hHl) 1 (by omega)
  rw [← (stack_slots4 L.c4).1] at q
  exact hinc5 V.toFullPar Hl mask entry (V.st5 (aZ4 W (ksOf P hp) (t0.drop (k0 g)) nz x g7).2) m
    (by rw [hbe, q]) hm

include L hHl in
/-- **The routed experts' gated products.** -/
theorem hincH6F (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hLam : P.y.LamM = V.D.ne)
    (hbe : (V.st6 (aZ4 W (ksOf P hp) (t0.drop (k0 g)) nz x g7).2).be =
      gl.val (stackY hp.lamS ((ksOf P hp).tc4 (t0.drop (k0 g)))).2.2)
    (hm : ∀ i : Fin V.D.ne, m (V.cI (.inl (aH2 V.D i))) = mask (o.K.sH1 + 1 + i.val)) :
    V.ownF.toOwn.tail.s6.L.T.par.inc (aS6 W (ksOf P hp) (t0.drop (k0 g)) nz x g7) m =
      maskSum Hl (Road.Rows.start2 P.y.LamM o.K.sH1
        (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray) mask -
      entSum (Road.Rows.start2 P.y.LamM o.K.sH1
        (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray)
        entry := by
  refine hinc6 V.toFullPar Hl mask entry
    (V.st6 (aZ4 W (ksOf P hp) (t0.drop (k0 g)) nz x g7).2, Johnson.L5.Layers.rd gl (V.D.lL - 1)
      (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1))) m
    (LamM := P.y.LamM) (sH1 := o.K.sH1)
    (rhoM := (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray)
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
/-- **The merge, with the embedding's mask entry.** -/
theorem hincH7F (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hg : (g == 0) = true)
    (hbe : ∀ a : Fin V.nW,
      V.wp0.wt.be a (V.ip.st7 V.num (aZ4 W (ksOf P hp) (t0.drop (k0 g)) nz x g7).2) =
      gl.val (stackY hp.lamS ((ksOf P hp).tc4 (t0.drop (k0 g)))).2.2)
    (hm : ∀ a : Fin V.nW, m (V.wp0.wt.nm a) = mask (o.K.sV + a.val))
    (hmE : m V.mkE = mask o.sVE) :
    V.ownF.toOwn.tail.s7.L.T.par.inc (aS7 W (ksOf P hp) (t0.drop (k0 g)) nz x g7) m =
      maskSum Hl (wsForkStart (mergeSlots hp g o)
        (powers (tapeEps ((ksOf P hp).tcW (t0.drop (k0 g)))) (mergeSlots hp g o).size)) mask -
      entSum (wsForkStart (mergeSlots hp g o)
        (powers (tapeEps ((ksOf P hp).tcW (t0.drop (k0 g)))) (mergeSlots hp g o).size)) entry := by
  have hW : V.nW = hp.NCL - 1 := by
    rw [OnBytes.Tie.Pv.Lay.At.nW_eq V.toFullPar _ hD]
    show hp.NCL - (if (g == 0) = true then 1 else 0) = _
    simp only [hg, if_true]
  have hsl : mergeSlots hp g o = (Array.range (hp.NCL - 1)).map (o.K.sV + ·) ++ #[o.sVE] := by
    unfold mergeSlots
    simp only [hg, if_true]
  have c4 := L.c4
  simp only [hg, if_true] at c4
  have hsz : ((Array.range (hp.NCL - 1)).map (o.K.sV + ·) ++ #[o.sVE]).size = V.nW + 1 := by
    rw [hW]
    simp
  have fr : Fl.claimsIn 1 G4 ((ksOf P hp).tcW (t0.drop (k0 g))) = some (o.sVE, G5, u5) := by
    have q := L.front
    unfold mergeFront at q
    rw [if_pos hg] at q
    exact q
  obtain ⟨eE, vE, hvE, _, _, hrE⟩ := claimsIn_spec fr
  have hS4 : PscRun.Sized ({ G4 with next := G4.next + 1 } : Fork) := L.sG4
  rw [hsl]
  refine hinc7F V Hl mask entry _ m hsz ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact (powers_val gl _ _ a (by rw [hsz]; exact ha)).trans rfl
  · intro a
    have ha : a.val < hp.NCL - 1 := by
      rw [← hW]
      exact a.isLt
    have q := stack_factor L.s2 c4 Hl (L.g3.trans hHl) (2 + (1 + P.y.LamM) + a.val) (by omega)
    have e : o.K.sA0 + (2 + (1 + P.y.LamM) + a.val) = o.K.sV + a.val := by
      rw [(stack_slots4 c4).2]
      omega
    rw [e] at q
    rw [svAtE (hp.NCL - 1) o.K.sV a.val o.sVE ha, q]
    exact hbe a
  · have q := hideRun_factor hS4 hrE (L.g5.trans hHl) 0 (by rw [hvE]; exact Nat.one_pos)
    rw [Nat.add_zero, ← eE] at q
    rw [hW, svLast, q, gl.one]
  · intro a
    have ha : a.val < hp.NCL - 1 := by
      rw [← hW]
      exact a.isLt
    rw [hm a, svAtE (hp.NCL - 1) o.K.sV a.val o.sVE ha]
  · rw [hmE, hW, svLast]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.inc7F
#print axioms OnBytes.Road.K4.hinc7F
#print axioms OnBytes.Road.K4.hincH1F
#print axioms OnBytes.Road.K4.hincH2F
#print axioms OnBytes.Road.K4.hincH3F
#print axioms OnBytes.Road.K4.hincH5F
#print axioms OnBytes.Road.K4.hincH6F
#print axioms OnBytes.Road.K4.hincH7F
