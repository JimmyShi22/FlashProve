-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskPscProofs.lean: proofs for Cb/Ld/LdLkpMaskPsc.lean.
-/
import Cb.Ld.LdLkpMaskPsc
import Cb.Ld.LdLkpMaskChainProofs
import Cb.Ld.LdZeroProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Prob Hiop

theorem mj_blind_of : Spec.mj_blind_of := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hW hd =>
  ⟨fun M k x ρ => hR.msg _ _ x ρ fun j hj => hW M k j (hd j hj),
    fun x k M h => hR.cl k _ x (fun j hj => (hW M k j (hd j hj)).symm) h⟩

theorem mj_narrow : Spec.mj_narrow := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ f hcl hst =>
  ⟨⟨f.mm.noOrc, f.mm.free, f.mm.run, hst, fun k xp ρ h => f.mm.law k xp ρ (hcl xp k h)⟩,
    f.same, f.hand⟩

theorem mj_reJ : Spec.mj_reJ := by
  intro E J J' Xi Xo Ei Eo R Wi Wo H D e rdi rdo f
  have e1 : ∀ (M : D.Mk) (k : J → E), (fun j' => (D.reJ e).put M k (e j')) =
      D.put M fun j' => k (e j') := fun M k => funext fun j' => by
    show D.put M (fun j' => k (e j')) (e.symm (e j')) = _
    rw [e.symm_apply_apply]
  refine ⟨⟨f.mm.noOrc, f.mm.free, f.mm.run, fun xp k M h => ?_, fun k xp ρ h => ?_⟩,
    fun w x c ρ => ?_, f.hand⟩
  · show D.Cl xp fun j' => (D.reJ e).put M k (e j')
    rw [e1]
    exact f.mm.stable xp _ M h
  · show (unif D.Mk).map (fun M => D.msg (fun j' => (D.reJ e).put M k (e j')) xp ρ) = D.sim xp ρ
    simp only [e1]
    exact f.mm.law _ xp ρ h
  · funext j
    have h := congrFun (f.same w x c ρ) (e.symm j)
    simpa using h

section
variable {E : Type} [Field E]

theorem pQ_pPl :
    ∀ (l : List (PFmt E)) (d : PDats l) (q : RIdx (pVars l d) → E), pQ l d (pPl l d q) = q
  | [], _, _ => funext fun i => i.elim
  | _ :: l, d, q => funext fun i => match i with
    | .inl _ => rfl
    | .inr i => congrFun (pQ_pPl l d.2 fun i => q (.inr i)) i

theorem hFin_ne :
    ∀ (l : List (PFmt E)) (d : PDats l) (σ σ' : E) (q : RIdx (pVars l d) → E) (γ : HPt (pVars l d)),
      l ≠ [] → hFin (pVars l d) σ q γ = hFin (pVars l d) σ' q γ
  | [], _, _, _, _, _, h => absurd rfl h
  | _ :: _, _, _, _, _, _, _ => rfl

end

section
variable (E : Type) [Field E] [Fintype E]

theorem PscPar.nxt_sent (Y : PscPar E) (Ex : ExtSpec) (hV : Y.VarsOK) (hD : Y.DegOK)
    (hne : Y.fmt ≠ []) (x : E × Y.St) (m : Y.J → E) (ρ : Rho (Y.psc Ex).shape) :
    Y.nxtOf Ex x (Y.pack Ex x.2 (Y.sent x.2 m (Y.zEps Ex ρ) (Y.zPt Ex ρ))) ρ =
      Y.honOut (Y.honMid x.2 m (Y.zEps Ex ρ) (Y.zPt Ex ρ)) m := by
  have h :=
    (hRounds_cons _ _ _ _ (Y.whole_rounds hV hD x.2 m (Y.zEps Ex ρ) (Y.hp x.2 (Y.zPt Ex ρ)))).2
  unfold PscPar.nxtOf PscPar.pack
  rw [Plains.fst_app, Plains.snd_app]
  show (⟨x.2, Y.zEps Ex ρ, Y.zPt Ex ρ,
      hFin (Y.vars x.2) _
        (pQ Y.fmt (Y.dat x.2)
          (pPl Y.fmt (Y.dat x.2) (Y.honQ x.2 m (Y.zEps Ex ρ) (Y.hp x.2 (Y.zPt Ex ρ)))))
        (Y.hp x.2 (Y.zPt Ex ρ)),
      _⟩ : Y.Out) = _
  rw [pQ_pPl,
    hFin_ne Y.fmt (Y.dat x.2) _ (hSumAll (Y.vars x.2) (Y.whole x.2 m (Y.zEps Ex ρ))) _ _ hne, h]
  rfl

theorem mjPsc_fits : Spec.mjPsc_fits E := by
  intro Y Ex Wt msg O hV hD hO hne
  refine ⟨psc_mm E Y Ex Wt msg O hV hD hO, fun w x c ρ => ?_, fun w x c ρ => ?_⟩
  · rw [psc_hands E Y Ex Wt msg O hO w x c ρ]
  · rw [psc_hands E Y Ex Wt msg O hO w x c ρ]
    exact (Y.nxt_sent E Ex hV hD hne x (O.cut (msg w)) ρ).symm

omit [Fintype E] in
theorem PscPar.cut_congr {Y : PscPar E} (O : Y.Own)
    {k k' : Y.J → E} (h : ∀ j, O.Rd j → k j = k' j) : O.cut k = O.cut k' := by
  classical
  funext j
  unfold PscPar.Own.cut
  by_cases hj : O.Rd j
  · rw [if_pos hj, if_pos hj, h j hj]
  · rw [if_neg hj, if_neg hj]

theorem mjPsc_reads : Spec.mjPsc_reads E := by
  intro Y Ex O O' hO'
  refine ⟨fun k k' x ρ h => ?_, fun k k' x h hc => ?_⟩
  · show Y.pack Ex x.2 (Y.sent x.2 k (Y.zEps Ex ρ) (Y.zPt Ex ρ)) =
      Y.pack Ex x.2 (Y.sent x.2 k' (Y.zEps Ex ρ) (Y.zPt Ex ρ))
    rw [← PscPar.sent_cut hO' x.2 k, ← PscPar.sent_cut hO' x.2 k', PscPar.cut_congr E O' h]
  · have h1 := PscPar.sumHolds_cut hO' x k hc
    rw [PscPar.cut_congr E O' h] at h1
    show hSumAll (Y.vars x.2) (Y.sum x.2 k') + Y.inc x.2 k' = x.1
    rw [← PscPar.sum_congr (PscPar.G_cut hO' x.2 k') (PscPar.Gb_cut hO' x.2 k'),
      ← PscPar.inc_cut hO' x.2 k']
    exact h1

theorem mjPsc_writes : Spec.mjPsc_writes E := fun _ _ _ M k j h =>
  PscPar.put_off M k j fun i hi => h ⟨i, hi⟩

theorem mjPsc_out : Spec.mjPsc_out E := by
  intro Y Ex O hV hD hne k x ρ
  have e : (Y.mj Ex O).nxt x ((Y.mj Ex O).msg k x ρ) ρ =
      Y.honOut (Y.honMid x.2 k (Y.zEps Ex ρ) (Y.zPt Ex ρ)) k :=
    Y.nxt_sent E Ex hV hD hne x k ρ
  rw [e]
  exact ⟨(psc_out_iff E Y _ k).2 ⟨rfl, fun _ => rfl⟩, rfl⟩

theorem mjOur_mono : Spec.mjOur_mono E := fun _ _ _ hs h =>
  ⟨h.inj, fun i => hs _ (h.own i), fun st m m' hm => h.rdF st m m' fun j hj => hm j (hs j hj),
    fun st m m' hm => h.rdFb st m m' fun j hj => hm j (hs j hj),
    fun st j hj => h.rdS st j fun hj' => hj (hs j hj'), h.oF, h.oFb, h.oS⟩

theorem mjOur_ne : Spec.mjOur_ne E := fun T =>
  List.append_ne_nil_of_right_ne_nil T.fmt (List.cons_ne_nil _ _)

theorem mjIn_fits : Spec.mjIn_fits E := fun Z Ex W rd =>
  mj_draw E Z.T.J _ _ Z.ev.D Z.nxX Ex W Z.AllHold rd

theorem mjIn_step : Spec.mjIn_step E := fun Z _ _ hL k x ρ h =>
  (psc_our_sum E Z.T _ k).2 (pscIn_fwd E Z hL x ρ.1 k h)

end
end Cb
