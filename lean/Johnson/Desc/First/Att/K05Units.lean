-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Units.lean: K05_law at the library's letters: RowPrem of the two
softmax-table units
(P.uM: below the diagonal; P.uD: on it), at the rows that leftP makes.

Main names:
  `unitM_prem`, `unitD_prem`: under (D1), the place of the last rider's mask entry, UnitPtsM or
    UnitPtsD, the
    library's numbering, the place's two numbers: (D2) is proved in the ledger's world; (D4) by
      unitM_hW,
    unitD_hW.
  `closed_unitM_prem`, `closed_unitD_prem`: at the closed parameters: no place left.

Sources: what Att/K05Weights3.lean, K05Places.lean and K05ClosedAt.lean name;
Cb/Pv/Att/OwnSteps.lean (uM, uD).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Weights3
import Johnson.Desc.First.Att.K05ClosedSeam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH SameRead sc3Num sc3Vals)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M X : Type}

/-- **The unit below the diagonal.** j: where its seven scalars begin. -/
theorem unitM_prem (P : OwnPar K M X) (d : SumH ρ P.uM) {j nv : ℕ} {riders v7 : List E} {H : PscH}
    {hh : MaskedSum.Heard} {G : Fork} (hs : SizeP P.uM (products nv P.D.nb)) (hD : OfP d riders H hh)
    (hsum : SumAt (.slot (j + 6)) (products nv P.D.nb) riders H hh G) (h7 : v7.length = 7) (hp : PutRun G j v7)
    (ht : SameRead hh.target (v7.getD 6 zeroE)) (hv : ∀ a, d.v a = ρ.val (H.v.getD (sc3Num a) zeroE))
    {g : Geo} {u : UnitG} {zk Wt : Array E} (hbl : u.below = true) (hw : scoreW g u zk (chal hh) = some Wt)
    (lp : UnitPtsM ρ P.D P.C d.st.z u zk) (g2 : g.lgk = P.D.lg) (g3 : g.lnT = P.D.lP + 1)
    (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M) {f : Aff} (hf : left G hh Wt = some f)
    (hk : P.msg m (P.kM (Fin.last _)) = mask (j + 6))
    (D1 : (P.st3 .s6b fun _ => inc1 (P.kM (Fin.last _))).plain.our.par.W d.st (P.msg m) =
      OnBytes.Road.Hd.place (G.worldOf ρ mask entry).slot
        ((P.st3 .s6b fun _ => inc1 (P.kM (Fin.last _))).plain.our.par.vars d.st) hh.first) :
    RowPrem P.uM d (.slot (j + 6)) hh f (G.worldOf ρ mask entry) m :=
  left3_prem (P.st3 .s6b fun _ => inc1 (P.kM (Fin.last _))) _ _ P.msg _ d hsum _ m hf
    (by rw [(scoreW_below hbl hw).2, Array.size_map]; exact lp.nPw) (funext hv)
    (unitM_hW P.D P.C P.rd _ (P.wAt .s6b) (P.cAt .s6b) _ _ P.msg _ d hs hD hsum hbl hw lp g2 g3) D1 (by
      show ∑ i, inc1 (P.kM (Fin.last _)) i * P.msg m i = _
      rw [inc1_sum, d2_slot (hp 6 (by rw [h7]; omega)) (ht K ρ), hk])

/-- **The unit on the diagonal.** -/
theorem unitD_prem (P : OwnPar K M X) (d : SumH ρ P.uD) {j nv : ℕ} {riders v7 : List E} {H : PscH}
    {hh : MaskedSum.Heard} {G : Fork} (hs : SizeP P.uD (products nv P.D.nb)) (hD : OfP d riders H hh)
    (hsum : SumAt (.slot (j + 6)) (products nv P.D.nb) riders H hh G) (h7 : v7.length = 7) (hp : PutRun G j v7)
    (ht : SameRead hh.target (v7.getD 6 zeroE)) (hv : ∀ a, d.v a = ρ.val (H.v.getD (sc3Num a) zeroE))
    {g : Geo} {u : UnitG} {zk Wt : Array E} (hbl : u.below = false) (hw : scoreW g u zk (chal hh) = some Wt)
    (lp : UnitPtsD ρ P.D P.C d.st.z u zk) (g2 : g.lgk = P.D.lg) (g3 : g.lnT = P.D.lP + 1)
    (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M) {f : Aff} (hf : left G hh Wt = some f)
    (hk : P.msg m (P.kD (Fin.last _)) = mask (j + 6))
    (D1 : (P.st3 .s6d fun _ => inc1 (P.kD (Fin.last _))).plain.our.par.W d.st (P.msg m) =
      OnBytes.Road.Hd.place (G.worldOf ρ mask entry).slot
        ((P.st3 .s6d fun _ => inc1 (P.kD (Fin.last _))).plain.our.par.vars d.st) hh.first) :
    RowPrem P.uD d (.slot (j + 6)) hh f (G.worldOf ρ mask entry) m :=
  left3_prem (P.st3 .s6d fun _ => inc1 (P.kD (Fin.last _))) _ _ P.msg _ d hsum _ m hf
    (by rw [(scoreW_on hbl hw).2, Array.size_map]; exact lp.nPw) (funext hv)
    (unitD_hW P.D P.C P.rd _ (P.wAt .s6d) (P.cAt .s6d) _ _ P.msg _ d hs hD hsum hbl hw lp g2 g3) D1 (by
      show ∑ i, inc1 (P.kD (Fin.last _)) i * P.msg m i = _
      rw [inc1_sum, d2_slot (hp 6 (by rw [h7]; omega)) (ht K ρ), hk])

/-- **The unit below the diagonal at the closed parameters: no place left.** -/
theorem closed_unitM_prem {M0 : Type} (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork} {o1 o2 : ℕ × MaskedSum.Heard}
    (hsc : h.scores.toList = [o1, o2]) (hz : Sized G) (d : SumH ρ (closedOf P0 Λ G.ns (numsOf h)).uM) {nv : ℕ}
    {riders v7 : List E} {H : PscH} (hs : SizeP (closedOf P0 Λ G.ns (numsOf h)).uM (products nv P0.D.nb))
    (hD : OfP d riders H o1.2) (hsum : SumAt (.slot (o1.1 + 6)) (products nv P0.D.nb) riders H o1.2 G)
    (h7 : v7.length = 7) (hp : PutRun G o1.1 v7) (ht : SameRead o1.2.target (v7.getD 6 zeroE))
    (hv : ∀ a, d.v a = ρ.val (H.v.getD (sc3Num a) zeroE)) {g : Geo} {u : UnitG} {zk Wt : Array E}
    (hbl : u.below = true) (hw : scoreW g u zk (chal o1.2) = some Wt) (lp : UnitPtsM ρ P0.D P0.C d.st.z u zk)
    (g2 : g.lgk = P0.D.lg) (g3 : g.lnT = P0.D.lP + 1) (entry : ℕ → ℕ → ℕ → K) (m : Mg) {f : Aff}
    (hf : left G o1.2 Wt = some f) :
    RowPrem (closedOf P0 Λ G.ns (numsOf h)).uM d (.slot (o1.1 + 6)) o1.2 f (G.worldOf ρ (Λ.maskOf m) entry) m := by
  have e7 : (numsOf h).seven 0 = o1.1 := by
    unfold Nums.seven numsOf
    simp [hsc]
  have eF : (numsOf h).firstOf .s6b = o1.2.first := by
    unfold Nums.firstOf Nums.uFirst numsOf
    simp [hsc]
  refine unitM_prem (closedOf P0 Λ G.ns (numsOf h)) d hs hD hsum h7 hp ht hv hbl hw lp g2 g3 (Λ.maskOf m) entry m hf ?_
    (D1_at (closedOf P0 Λ G.ns (numsOf h)).uM d hs hsum (Λ.maskOf m) entry m fun i => ?_)
  · have := closed_kM P0 Λ G.ns (numsOf h) m (by
      rw [e7]
      exact le_of_lt (put_lt hz (hp 6 (by rw [h7]; omega))))
    rw [e7] at this
    exact this
  · have := closed_w P0 Λ G.ns (numsOf h) m .s6b i (by
      rw [eF]
      exact le_of_lt (put_lt hz (coef_put (closedOf P0 Λ G.ns (numsOf h)).uM hs hsum i)))
    rw [eF] at this
    exact this

/-- **The unit on the diagonal at the closed parameters: no place left.** -/
theorem closed_unitD_prem {M0 : Type} (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork} {o1 o2 : ℕ × MaskedSum.Heard}
    (hsc : h.scores.toList = [o1, o2]) (hz : Sized G) (d : SumH ρ (closedOf P0 Λ G.ns (numsOf h)).uD) {nv : ℕ}
    {riders v7 : List E} {H : PscH} (hs : SizeP (closedOf P0 Λ G.ns (numsOf h)).uD (products nv P0.D.nb))
    (hD : OfP d riders H o2.2) (hsum : SumAt (.slot (o2.1 + 6)) (products nv P0.D.nb) riders H o2.2 G)
    (h7 : v7.length = 7) (hp : PutRun G o2.1 v7) (ht : SameRead o2.2.target (v7.getD 6 zeroE))
    (hv : ∀ a, d.v a = ρ.val (H.v.getD (sc3Num a) zeroE)) {g : Geo} {u : UnitG} {zk Wt : Array E}
    (hbl : u.below = false) (hw : scoreW g u zk (chal o2.2) = some Wt) (lp : UnitPtsD ρ P0.D P0.C d.st.z u zk)
    (g2 : g.lgk = P0.D.lg) (g3 : g.lnT = P0.D.lP + 1) (entry : ℕ → ℕ → ℕ → K) (m : Mg) {f : Aff}
    (hf : left G o2.2 Wt = some f) :
    RowPrem (closedOf P0 Λ G.ns (numsOf h)).uD d (.slot (o2.1 + 6)) o2.2 f (G.worldOf ρ (Λ.maskOf m) entry) m := by
  have e7 : (numsOf h).seven 1 = o2.1 := by
    unfold Nums.seven numsOf
    simp [hsc]
  have eF : (numsOf h).firstOf .s6d = o2.2.first := by
    unfold Nums.firstOf Nums.uFirst numsOf
    simp [hsc]
  refine unitD_prem (closedOf P0 Λ G.ns (numsOf h)) d hs hD hsum h7 hp ht hv hbl hw lp g2 g3 (Λ.maskOf m) entry m hf ?_
    (D1_at (closedOf P0 Λ G.ns (numsOf h)).uD d hs hsum (Λ.maskOf m) entry m fun i => ?_)
  · have := closed_kD P0 Λ G.ns (numsOf h) m (by
      rw [e7]
      exact le_of_lt (put_lt hz (hp 6 (by rw [h7]; omega))))
    rw [e7] at this
    exact this
  · have := closed_w P0 Λ G.ns (numsOf h) m .s6d i (by
      rw [eF]
      exact le_of_lt (put_lt hz (coef_put (closedOf P0 Λ G.ns (numsOf h)).uD hs hsum i)))
    rw [eF] at this
    exact this

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.closed_unitM_prem
#print axioms VerifiableInference.Desc.First.Att.P.closed_unitD_prem
#print axioms VerifiableInference.Desc.First.Att.P.unitM_prem
#print axioms VerifiableInference.Desc.First.Att.P.unitD_prem
