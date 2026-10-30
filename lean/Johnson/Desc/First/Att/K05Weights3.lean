-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Weights3.lean: the law of kind K5 at the library's letters: the weights of
the two
softmax-table units (Att/LeftP.lean: scoreW), read as the library's weight polynomials Wb … .s6b
(below the
diagonal) and .s6d (on it) at the output's point.

Main names:
  `scoreW_on`, `scoreW_below`: where scoreW returns: its weights, written out.
  `UnitPtsD`, `UnitPtsM`: the lookup's points' premises for the two units.
  `unitD_weight`, `unitM_weight`, `unitD_hW`, `unitM_hW`.

Limit: UnitPtsD and UnitPtsM tie the key points that the lookup's kind hands on to the typed first
statement's
lookup point; they are not shown in this file or in what it imports.
Sources: Johnson/Road/Rows/AttRows14.lean (eqPts_head, onesOf_value, ones_agree; the proofs follow
the steps of
its weightFd and weightFm, which speak of OnBytes/Model's shape record, at the kind's own numbers);
AttRows58.lean
(eqPts_cut); AttWb14.lean (wbExt6d, wbExt6b); Inst/Model/Att.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Weights2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- Where scoreW returns, on the diagonal. -/
theorem scoreW_on {g : Geo} {u : UnitG} {zk r Wt : Array E} (hb : u.below = false)
    (h : scoreW g u zk r = some Wt) :
    (inner u zk).size = g.lgk + g.lnT + 2 * g.lB ∧
    Wt = (weights u zk).map (mulE · (mulE (eqPts ((inner u zk).extract 0 g.lgk) (r.extract 0 g.lgk))
      (eqPts ((inner u zk).extract g.lgk (g.lgk + g.lnT)) (r.extract g.lgk (g.lgk + g.lnT))))) := by
  unfold scoreW at h
  simp only [hb, Bool.false_eq_true, if_false, Option.bind_eq_bind] at h
  obtain ⟨_, g1, h⟩ := Option.bind_eq_some_iff.1 h
  simp only [Option.pure_def, Option.some.injEq] at h
  exact ⟨by simpa using guard_some g1, h.symm⟩

/-- Where scoreW returns, below the diagonal. -/
theorem scoreW_below {g : Geo} {u : UnitG} {zk r Wt : Array E} (hb : u.below = true)
    (h : scoreW g u zk r = some Wt) :
    (inner u zk).size = g.lgk + (g.lnT - 1) + g.lnT + 2 * g.lB ∧
    Wt = (weights u zk).map (mulE · (mulE (mulE (eqPts ((inner u zk).extract 0 g.lgk) (r.extract 0 g.lgk))
        (eqPts ((inner u zk).extract g.lgk (g.lgk + (g.lnT - 1))) (r.extract g.lgk (g.lgk + (g.lnT - 1)))))
      (subE (eqPts ((inner u zk).extract (g.lgk + (g.lnT - 1)) (g.lgk + (g.lnT - 1) + g.lnT))
          (r.extract (g.lgk + (g.lnT - 1)) (g.lgk + (g.lnT - 1) + g.lnT)))
        (mulE (ones ((inner u zk).extract (g.lgk + (g.lnT - 1)) (g.lgk + (g.lnT - 1) + g.lnT)))
          (ones (r.extract (g.lgk + (g.lnT - 1)) (g.lgk + (g.lnT - 1) + g.lnT))))))) := by
  unfold scoreW at h
  simp only [hb, if_true, Option.bind_eq_bind] at h
  obtain ⟨_, g1, h⟩ := Option.bind_eq_some_iff.1 h
  simp only [Option.pure_def, Option.some.injEq] at h
  exact ⟨by simpa using guard_some g1, h.symm⟩

/-- The lookup's points' premises for the unit on the diagonal. -/
structure UnitPtsD (ρ : Reading K) (D : AttSeg.Dim) (C : AttSeg.Calls) (z : ℕ → K) (u : UnitG) (zk : Array E) :
    Prop where
  nPw : (weights u zk).size = D.nb
  hw : ∀ b < D.nb, ρ.val ((weights u zk).getD b zeroE) = AttSeg.wp D C z .d1 b
  hg : ∀ k < D.lg, ρ.val ((inner u zk).getD k zeroE) = AttSeg.zgD D C z k
  hI : ∀ k < D.lP + 1, ρ.val ((inner u zk).getD (D.lg + k) zeroE) = AttSeg.zID D C z k

omit [Fintype K] in
/-- K5's weights of the unit on the diagonal read as the library's weight. -/
theorem unitD_weight (D : AttSeg.Dim) (C : AttSeg.Calls) (p : AttSeg.Pub K) {g : Geo} {u : UnitG} {zk r Wt : Array E}
    (hbl : u.below = false) (h : scoreW g u zk r = some Wt) (lp : UnitPtsD ρ D C p.z u zk) (g2 : g.lgk = D.lg)
    (g3 : g.lnT = D.lP + 1) (hr : D.lg + (D.lP + 1) ≤ r.size) {b : ℕ} (hb : b < D.nb) :
    ρ.val (Wt.getD b zeroE) = AttSeg.Wb D C p .s6d b fun j => ρ.val (r.getD j zeroE) := by
  obtain ⟨hsz, e⟩ := scoreW_on hbl h
  rw [g2, g3] at hsz e
  rw [e]
  have hbs : b < (weights u zk).size := by rw [lp.nPw]; exact hb
  have e1 : ((weights u zk).map (mulE · (mulE (eqPts ((inner u zk).extract 0 D.lg) (r.extract 0 D.lg))
      (eqPts ((inner u zk).extract D.lg (D.lg + (D.lP + 1))) (r.extract D.lg (D.lg + (D.lP + 1))))))).getD b zeroE =
      mulE ((weights u zk).getD b zeroE) (mulE (eqPts ((inner u zk).extract 0 D.lg) (r.extract 0 D.lg))
        (eqPts ((inner u zk).extract D.lg (D.lg + (D.lP + 1))) (r.extract D.lg (D.lg + (D.lP + 1))))) := by
    simp [Array.getD_eq_getD_getElem?, hbs]
  rw [e1, ρ.mul, ρ.mul, lp.hw b hb]
  have a1 := OnBytes.Road.Rows.eqPts_head ρ (x := (inner u zk).extract 0 D.lg) (r := r) (n := D.lg)
    (u := AttSeg.zgD D C p.z) (by simp; omega) (by omega) (fun k hk => by
      show ρ.val (((inner u zk).extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega), Nat.zero_add]
      exact lp.hg k hk)
  have a2 := OnBytes.Road.Rows.eqPts_cut ρ (x := (inner u zk).extract D.lg (D.lg + (D.lP + 1))) (r := r) (a := D.lg)
    (n := D.lP + 1) (u := AttSeg.zID D C p.z) (by simp; omega) hr (fun k hk => by
      show ρ.val (((inner u zk).extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega)]
      exact lp.hI k hk)
  have a1' : ρ.val (eqPts ((inner u zk).extract 0 D.lg) (r.extract 0 D.lg)) = _ := a1
  have a2' : ρ.val (eqPts ((inner u zk).extract D.lg (D.lg + (D.lP + 1))) (r.extract D.lg (D.lg + (D.lP + 1)))) = _ := a2
  rw [a1', a2']
  show _ = AttSeg.wp D C p.z .d1 b * AttSeg.eqPt D.lg (AttSeg.zgD D C p.z) (fun j => ρ.val (r.getD j zeroE)) *
    AttSeg.eqPt (D.lP + 1) (AttSeg.zID D C p.z) (AttSeg.sh (fun j => ρ.val (r.getD j zeroE)) D.lg)
  show _ * (AttSeg.eqPt D.lg _ (OnBytes.Road.pt ρ r) * AttSeg.eqPt (D.lP + 1) _ (AttSeg.sh (OnBytes.Road.pt ρ r) D.lg)) = _
  unfold OnBytes.Road.pt
  ring

/-- The lookup's points' premises for the unit below the diagonal. -/
structure UnitPtsM (ρ : Reading K) (D : AttSeg.Dim) (C : AttSeg.Calls) (z : ℕ → K) (u : UnitG) (zk : Array E) :
    Prop where
  nPw : (weights u zk).size = D.nb
  hw : ∀ b < D.nb, ρ.val ((weights u zk).getD b zeroE) = AttSeg.wp D C z .m1 b
  hg : ∀ k < D.lg, ρ.val ((inner u zk).getD k zeroE) = AttSeg.zg D C z k
  hP : ∀ k < D.lP, ρ.val ((inner u zk).getD (D.lg + k) zeroE) = AttSeg.zP D C z k
  hs : ∀ k < D.lP + 1, ρ.val ((inner u zk).getD (D.lg + D.lP + k) zeroE) = AttSeg.zs D C z k

omit [Fintype K] in
/-- K5's weights of the unit below the diagonal read as the library's weight. -/
theorem unitM_weight (D : AttSeg.Dim) (C : AttSeg.Calls) (p : AttSeg.Pub K) {g : Geo} {u : UnitG} {zk r Wt : Array E}
    (hbl : u.below = true) (h : scoreW g u zk r = some Wt) (lp : UnitPtsM ρ D C p.z u zk) (g2 : g.lgk = D.lg)
    (g3 : g.lnT = D.lP + 1) (hr : D.lg + D.lP + (D.lP + 1) ≤ r.size) {b : ℕ} (hb : b < D.nb) :
    ρ.val (Wt.getD b zeroE) = AttSeg.Wb D C p .s6b b fun j => ρ.val (r.getD j zeroE) := by
  obtain ⟨hsz, e⟩ := scoreW_below hbl h
  rw [g2, g3, show D.lP + 1 - 1 = D.lP by omega] at hsz e
  rw [e]
  have hbs : b < (weights u zk).size := by rw [lp.nPw]; exact hb
  rw [show ∀ f : E, ((weights u zk).map (mulE · f)).getD b zeroE = mulE ((weights u zk).getD b zeroE) f from
    fun f => by simp [Array.getD_eq_getD_getElem?, hbs]]
  rw [ρ.mul, ρ.mul, ρ.mul, ρ.sub, ρ.mul, lp.hw b hb]
  have a1 : ρ.val (eqPts ((inner u zk).extract 0 D.lg) (r.extract 0 D.lg)) = _ :=
    OnBytes.Road.Rows.eqPts_head ρ (n := D.lg) (u := AttSeg.zg D C p.z) (by simp; omega) (by omega) (fun k hk => by
      show ρ.val (((inner u zk).extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega), Nat.zero_add]
      exact lp.hg k hk)
  have a2 : ρ.val (eqPts ((inner u zk).extract D.lg (D.lg + D.lP)) (r.extract D.lg (D.lg + D.lP))) = _ :=
    OnBytes.Road.Rows.eqPts_cut ρ (a := D.lg) (n := D.lP) (u := AttSeg.zP D C p.z) (by simp; omega) (by omega)
      (fun k hk => by
        show ρ.val (((inner u zk).extract _ _).getD k zeroE) = _
        rw [extract_getD _ _ _ _ (by omega)]
        exact lp.hP k hk)
  have hzs : ∀ k < D.lP + 1, OnBytes.Road.pt ρ ((inner u zk).extract (D.lg + D.lP) (D.lg + D.lP + (D.lP + 1))) k =
      AttSeg.zs D C p.z k := fun k hk => by
    show ρ.val (((inner u zk).extract _ _).getD k zeroE) = _
    rw [extract_getD _ _ _ _ (by omega)]
    exact lp.hs k hk
  have a3 : ρ.val (eqPts ((inner u zk).extract (D.lg + D.lP) (D.lg + D.lP + (D.lP + 1)))
      (r.extract (D.lg + D.lP) (D.lg + D.lP + (D.lP + 1)))) = _ :=
    OnBytes.Road.Rows.eqPts_cut ρ (a := D.lg + D.lP) (n := D.lP + 1) (u := AttSeg.zs D C p.z) (by simp; omega) hr hzs
  have a4 : ρ.val (ones ((inner u zk).extract (D.lg + D.lP) (D.lg + D.lP + (D.lP + 1)))) =
      AttSeg.ones (D.lP + 1) (AttSeg.zs D C p.z) := by
    refine (OnBytes.Road.Rows.onesOf_value ρ _).trans ?_
    rw [show ((inner u zk).extract (D.lg + D.lP) (D.lg + D.lP + (D.lP + 1))).size = D.lP + 1 by simp; omega]
    exact OnBytes.Road.Rows.ones_agree hzs
  have a5 : ρ.val (ones (r.extract (D.lg + D.lP) (D.lg + D.lP + (D.lP + 1)))) =
      AttSeg.ones (D.lP + 1) (AttSeg.sh (OnBytes.Road.pt ρ r) (D.lg + D.lP)) := by
    refine (OnBytes.Road.Rows.onesOf_value ρ _).trans ?_
    rw [show (r.extract (D.lg + D.lP) (D.lg + D.lP + (D.lP + 1))).size = D.lP + 1 by simp; omega]
    exact OnBytes.Road.Rows.ones_agree fun k hk => by
      show ρ.val ((r.extract _ _).getD k zeroE) = ρ.val (r.getD (D.lg + D.lP + k) zeroE)
      rw [extract_getD _ _ _ _ (by omega)]
  rw [a1, a2, a3, a4, a5]
  show _ = AttSeg.wp D C p.z .m1 b * AttSeg.eqPt D.lg (AttSeg.zg D C p.z) (OnBytes.Road.pt ρ r) *
    AttSeg.eqPt D.lP (AttSeg.zP D C p.z) (AttSeg.sh (OnBytes.Road.pt ρ r) D.lg) *
    (AttSeg.eqPt (D.lP + 1) (AttSeg.zs D C p.z) (AttSeg.sh (OnBytes.Road.pt ρ r) (D.lg + D.lP)) -
      AttSeg.ones (D.lP + 1) (AttSeg.zs D C p.z) * AttSeg.ones (D.lP + 1) (AttSeg.sh (OnBytes.Road.pt ρ r) (D.lg + D.lP)))
  ring

/-- **The unit on the diagonal: the typed weight at the output's point is the reading of K5's
weight.** -/
theorem unitD_hW {X J : Type} [Fintype J] (D : AttSeg.Dim) (Cc : AttSeg.Calls)
    (rdc : (J → K) → AttSeg.Raw → K) (inc : AttSeg.Pub K → J → K)
    (wAt : PIdx (ldPartFmt K (AttSeg.Step.s6d.g D) (fun _ => 3) ++ [pDummy K 2]) → J) (cAt : Fin D.nb × Bool → J)
    (n : ℕ) (cl : X → (Fin n → K) → K × AttSeg.Pub K) (msg : M → J → K) (Lc : X → (Fin n → K) → M → Prop)
    (Dd : SumH ρ (SumL.of3 (stepSc3 D Cc rdc .s6d inc wAt cAt) n cl msg Lc)) {C : Aff} {st : Stage}
    {riders : List E} {H : PscH} {hh : MaskedSum.Heard} {Gf : Fork} {g : Geo} {u : UnitG} {zk Wt : Array E}
    (hs : SizeP (SumL.of3 (stepSc3 D Cc rdc .s6d inc wAt cAt) n cl msg Lc) st) (hD : OfP Dd riders H hh)
    (hsum : SumAt C st riders H hh Gf) (hbl : u.below = false) (hw : scoreW g u zk (chal hh) = some Wt)
    (lp : UnitPtsD ρ D Cc Dd.st.z u zk) (g2 : g.lgk = D.lg) (g3 : g.lnT = D.lP + 1) (b : Fin D.nb) :
    (stepSc3 D Cc rdc .s6d inc wAt cAt).W Dd.st b
      (ldPartIni (AttSeg.Step.s6d.g D) (fun _ => 3) (pDummy K 2) Dd.out.pt) = ρ.val (Wt.getD b.1 zeroE) := by
  have hsz : (chal hh).size = AttSeg.Step.s6d.g D := chal_size _ Dd hs hD hsum
  have hn := nat_ini _ Dd hs hD hsum
  show Blocks.ext (AttSeg.Step.s6d.g D)
    (fun Y => AttSeg.Wb D Cc Dd.st .s6d b.1 (Blocks.cubePt (AttSeg.Step.s6d.g D) Y))
    (Blocks.nat (ldPartIni (AttSeg.Step.s6d.g D) (fun _ => 3) (pDummy K 2) Dd.out.pt)) = _
  rw [OnBytes.Road.Rows.wbExt6d, unitD_weight D Cc Dd.st hbl hw lp g2 g3 (by
    rw [hsz]
    show D.lg + (D.lP + 1) ≤ D.lg + (D.lP + 1) + D.ln
    omega) b.2]
  exact congrArg _ hn

/-- **The unit below the diagonal: the typed weight at the output's point is the reading of K5's
weight.** -/
theorem unitM_hW {X J : Type} [Fintype J] (D : AttSeg.Dim) (Cc : AttSeg.Calls)
    (rdc : (J → K) → AttSeg.Raw → K) (inc : AttSeg.Pub K → J → K)
    (wAt : PIdx (ldPartFmt K (AttSeg.Step.s6b.g D) (fun _ => 3) ++ [pDummy K 2]) → J) (cAt : Fin D.nb × Bool → J)
    (n : ℕ) (cl : X → (Fin n → K) → K × AttSeg.Pub K) (msg : M → J → K) (Lc : X → (Fin n → K) → M → Prop)
    (Dd : SumH ρ (SumL.of3 (stepSc3 D Cc rdc .s6b inc wAt cAt) n cl msg Lc)) {C : Aff} {st : Stage}
    {riders : List E} {H : PscH} {hh : MaskedSum.Heard} {Gf : Fork} {g : Geo} {u : UnitG} {zk Wt : Array E}
    (hs : SizeP (SumL.of3 (stepSc3 D Cc rdc .s6b inc wAt cAt) n cl msg Lc) st) (hD : OfP Dd riders H hh)
    (hsum : SumAt C st riders H hh Gf) (hbl : u.below = true) (hw : scoreW g u zk (chal hh) = some Wt)
    (lp : UnitPtsM ρ D Cc Dd.st.z u zk) (g2 : g.lgk = D.lg) (g3 : g.lnT = D.lP + 1) (b : Fin D.nb) :
    (stepSc3 D Cc rdc .s6b inc wAt cAt).W Dd.st b
      (ldPartIni (AttSeg.Step.s6b.g D) (fun _ => 3) (pDummy K 2) Dd.out.pt) = ρ.val (Wt.getD b.1 zeroE) := by
  have hsz : (chal hh).size = AttSeg.Step.s6b.g D := chal_size _ Dd hs hD hsum
  have hn := nat_ini _ Dd hs hD hsum
  show Blocks.ext (AttSeg.Step.s6b.g D)
    (fun Y => AttSeg.Wb D Cc Dd.st .s6b b.1 (Blocks.cubePt (AttSeg.Step.s6b.g D) Y))
    (Blocks.nat (ldPartIni (AttSeg.Step.s6b.g D) (fun _ => 3) (pDummy K 2) Dd.out.pt)) = _
  rw [OnBytes.Road.Rows.wbExt6b, unitM_weight D Cc Dd.st hbl hw lp g2 g3 (by
    rw [hsz]
    show D.lg + D.lP + (D.lP + 1) ≤ D.lg + D.lP + (D.lP + 1) + D.ln
    omega) b.2]
  exact congrArg _ hn

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.unitD_hW
#print axioms VerifiableInference.Desc.First.Att.P.unitM_hW
#print axioms VerifiableInference.Desc.First.Att.P.unitM_weight
#print axioms VerifiableInference.Desc.First.Att.P.unitD_weight
