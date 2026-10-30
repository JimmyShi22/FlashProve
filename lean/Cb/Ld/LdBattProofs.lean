-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBattProofs.lean: the proofs of the statements of Cb/Ld/LdBatt.lean.
The proofs for a batching step of an interactive oracle proof: a random linear combination of linear
claims on one matrix, then a sumcheck.

The main theorems are `batt_goodAt`, `batt_mm` and `batt_goodM_sig`. What they state, under which
hypotheses, and the limits: the head of Cb/Ld/LdBatt.lean.
  `batt_goodAt`: the block at the base, for each fixed tuple of messages (`GoodAt`,
    Cb/Ld/LdSigLift.lean).
  `batt_mm`, `batt_goodM_sig`: see their statements.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
-/
import Cb.Ld.LdBatt
import Cb.Ld.LdBattKit
import Cb.Ld.LdPscVarsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

namespace BattPar
variable {E : Type} [Field E] [Fintype E] (B : BattPar E)

/-- the summand as a function of the point -/
def sumFn (st : B.par.St) (m : B.J → E) (z : Fin B.k → E) : E :=
  0 + ∑ q, B.Z.ze st.2 q * Alg.eqPt (B.pt st.1 q) z * Alg.mle (B.col m (B.g st.1 q)) z

theorem sum_eq (st : B.par.St) (m : B.J → E) (X : HPt (B.par.vars st)) :
    B.par.sum st m X = B.sumFn st m (B.fn X) := rfl

theorem inc_eq (st : B.par.St) (m : B.J → E) :
    B.par.inc st m = ∑ q, B.Z.ze st.2 q * ∑ j, B.slM q st.1 j * m j := by
  show ∑ j, (∑ q, B.Z.ze st.2 q * B.slM q st.1 j) * m j = _
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ => by ring

theorem sumAll_eq (st : B.par.St) (m : B.J → E) :
    hSumAll (B.par.vars st) (B.par.sum st m) =
      ∑ q, B.Z.ze st.2 q * B.ten (B.g st.1 q) (B.pt st.1 q) m := by
  have h := psv_plains_sum E B.n B.k (B.par.sum st m)
  refine h.trans ?_
  have e : ∀ b : Fin B.k → Bool,
      B.par.sum st m (pH _ (pdPlains E B.n B.k) (ppOf (pfCube E B.n) B.k (Alg.corner b))) =
        ∑ q, B.Z.ze st.2 q * (Alg.eqk (B.pt st.1 q) b * B.col m (B.g st.1 q) b) := by
    intro b
    rw [sum_eq]
    have hb : B.fn (pH _ (pdPlains E B.n B.k) (ppOf (pfCube E B.n) B.k (Alg.corner b))) =
        Alg.corner b :=
      psv_fn_pt E _ _ _ _
    rw [hb]
    unfold sumFn
    rw [zero_add]
    exact Finset.sum_congr rfl fun q _ => by rw [Alg.eqPt_corner, Alg.mle_corner, mul_assoc]
  rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => by rw [← Finset.mul_sum]; rfl

theorem sumHolds_iff (x : (B.Q → E) × B.St) (ρ : B.Z.D) (m : B.J → E) :
    B.par.SumHolds (B.nx x ρ) m ↔ ∑ q, B.Z.ze ρ q * B.lhs x.2 q m = ∑ q, B.Z.ze ρ q * x.1 q := by
  show hSumAll (B.par.vars (x.2, ρ)) (B.par.sum (x.2, ρ) m) + B.par.inc (x.2, ρ) m = _ ↔ _
  rw [sumAll_eq, inc_eq, ← Finset.sum_add_distrib]
  have e : ∀ q, B.Z.ze ρ q * B.ten (B.g x.2 q) (B.pt x.2 q) m +
        B.Z.ze ρ q * ∑ j, B.slM q x.2 j * m j =
      B.Z.ze ρ q * B.lhs x.2 q m := fun q => by
    unfold lhs
    ring
  rw [Finset.sum_congr rfl fun q _ => e q]
  exact Iff.rfl

/-- the left sides read the matrix and what the incoming forms read -/
theorem lhs_congr {st : B.St} {q : B.Q} {m m' : B.J → E} (h1 : ∀ a, m (B.mAt a) = m' (B.mAt a))
    (h2 : ∀ j, B.slM q st j ≠ 0 → m j = m' j) :
    B.lhs st q m = B.lhs st q m' := by
  unfold lhs ten
  have hc : B.col m (B.g st q) = B.col m' (B.g st q) :=
    funext fun c => Finset.sum_congr rfl fun r _ => by rw [h1]
  rw [hc]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : B.slM q st j = 0
  · rw [hj, zero_mul, zero_mul]
  · rw [h2 j hj]

theorem col_comb (m : B.J → E) (c : B.Q → E) (g : B.Q → B.Rw → E) :
    B.col m (fun r => ∑ q, c q * g q r) = fun b => ∑ q, c q * B.col m (g q) b := by
  funext b
  unfold col
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by ring

theorem ten_comb (m : B.J → E) (c : B.Q → E) (g : B.Q → B.Rw → E) (z : Fin B.k → E) :
    B.ten (fun r => ∑ q, c q * g q r) z m = ∑ q, c q * B.ten (g q) z m := by
  unfold ten
  rw [col_comb]
  unfold Alg.mle
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun b _ => by ring

end BattPar

section Main
open IOR
variable (E : Type) [Field E] [Fintype E]

theorem batt_sum : Spec.batt_sum E := fun B x ρ m => B.sumHolds_iff x ρ m

theorem batt_fwd : Spec.batt_fwd E := fun B x ρ m h =>
  (B.sumHolds_iff x ρ m).2 (Finset.sum_congr rfl fun q _ => by rw [h q])

theorem batt_cnt : Spec.batt_cnt E := by
  intro B hZ x m hx
  have hv : (fun q => B.lhs x.2 q m - x.1 q) ≠ 0 := fun h =>
    hx fun q => sub_eq_zero.1 (congrFun h q)
  refine le_trans (le_of_eq (cnt_congr fun ρ => ?_)) (hZ _ hv)
  rw [B.sumHolds_iff, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact Eq.congr (Finset.sum_congr rfl fun q _ => by ring) rfl

theorem batt_ok : Spec.batt_ok E := by
  intro B hn
  refine ⟨fun _ => psv_plains_ok E B.n B.k (by omega), fun st m => ?_, fun f hf => ?_⟩
  · refine kit_deg E (pfCube E B.n) B.k (pdPlains E B.n B.k) (B.sumFn st m) ?_
    refine Alg.DegLE.add (Alg.DegLE.const _ 0) (Alg.DegLE.sum _ fun q _ => ?_)
    refine Alg.DegLE.mono
      (Alg.DegLE.mul (Alg.DegLE.const_mul _ (Alg.DegLE.eqPt (B.pt st.1 q)))
        (Alg.DegLE.mle (B.col m (B.g st.1 q)))) fun _ => hn
  · rw [List.eq_of_mem_replicate hf]
    exact fun _ _ h => h

theorem batt_row : Spec.batt_row E := by
  intro B hn z m
  show hU (B.par.vars z.st) (B.par.W z.st m) (B.par.hp z.st z.pt) +
        z.eps * (hPsi (B.par.vars z.st) (B.par.hp z.st z.pt) * B.par.inc z.st m +
            B.par.sum z.st m (B.par.hp z.st z.pt)) = z.fin ↔
    _
  unfold BattPar.RowHolds
  have h1 : hU (B.par.vars z.st) (B.par.W z.st m) (B.par.hp z.st z.pt) =
      ∑ i, hSl (B.par.vars z.st) (B.par.hp z.st z.pt) i *
        m (B.wAt (pIx B.fmt (pdPlains E B.n B.k) i)) :=
    hide_form E E _ _ _
  have h2 : hPsi (B.par.vars z.st) (B.par.hp z.st z.pt) = ∏ i, B.outPt z i :=
    kit_psi_plains E B.n B.k hn _
  have h3 : B.par.sum z.st m (B.par.hp z.st z.pt) =
      B.ten (fun r => ∑ q, B.chi z q * Alg.eqPt (B.pt z.st.1 q) (B.outPt z) * B.g z.st.1 q r)
        (B.outPt z) m := by
    rw [B.ten_comb, B.sum_eq]
    unfold BattPar.sumFn
    rw [zero_add]
    rfl
  rw [h1, h2, h3, B.inc_eq]
  exact Eq.congr (by unfold BattPar.chi; ring) rfl

theorem batt_own : Spec.batt_own E := by
  intro B Rd h
  have hGb : ∀ (st : B.par.St) (m m' : B.J → E),
      (∀ a, m (B.mAt a) = m' (B.mAt a)) → B.par.Gb st m = B.par.Gb st m' := by
    intro st m m' hm
    funext q X
    show Alg.mle (B.col m (B.g st.1 q)) _ = Alg.mle (B.col m' (B.g st.1 q)) _
    have hc : B.col m (B.g st.1 q) = B.col m' (B.g st.1 q) :=
      funext fun c => Finset.sum_congr rfl fun r _ => by rw [hm]
    rw [hc]
  exact
    { inj := h.inj
      own := h.own
      rdG := fun _ _ _ _ => funext fun a => a.elim
      rdGb := fun st m m' hm => hGb st m m' fun a => hm _ (h.rdM a)
      rdS := fun st j hj => Finset.sum_eq_zero fun q _ => by rw [h.rdS q st.1 j hj, mul_zero]
      wG := fun _ _ _ _ => funext fun a => a.elim
      wGb := fun st m m' hm => hGb st m m' fun a => hm _ fun i e => h.wM i a e.symm
      wS := fun st i => Finset.sum_eq_zero fun q _ => by
        show B.Z.ze st.2 q * B.slM q st.1 (B.wAt i) = 0
        rw [h.wS q st.1 i, mul_zero] }

theorem batt_goodAt : Spec.batt_goodAt E := by
  intro B Ex M Wp Kc A0 msg hn hZ
  obtain ⟨hV, hD, hI⟩ := batt_ok E B hn
  refine goodAt_seq_ext Kc M _ _ _ Ex Ex Ex Wp Wp Wp (IOR.draw B.Z.D B.nx Ex) (B.par.core Ex) _ _ _
    (B.par.baseIn (A0.keepX B.Z.D) fun w => msg w.1) _ (fun _ _ _ wp => wp) (fun _ _ _ wp => wp) _ _
    _ (goodAt_draw Kc M _ _ Ex Wp B.Z.D B.nx _ _ B.Z.err ?_ ?_ ?_ ?_)
    (psc_core_goodAt E B.par Ex M Wp Kc (A0.keepX B.Z.D) msg hV hD hI) fun _ _ _ _ _ _ _ => rfl
  · exact fun x y w β h => ⟨h.1, batt_fwd E B x β _ h.2⟩
  · exact fun x y β h => h
  · exact fun _ => rfl
  · intro x y m _
    by_cases hx : B.InHolds x (msg m)
    · refine le_trans (le_of_eq (cnt_false fun β hβ => ?_)) (Nat.zero_le _)
      obtain ⟨wp, h1, h2⟩ := hβ
      exact h2 ⟨h1.1, hx⟩
    · refine le_trans (cnt_mono fun β hβ => ?_) (batt_cnt E B hZ x (msg m) hx)
      obtain ⟨wp, h1, -⟩ := hβ
      exact h1.2

open Classical in
theorem batt_mm : Spec.batt_mm E := by
  intro B Ex Wt msg Rd hn hO
  obtain ⟨hV, hD, -⟩ := batt_ok E B hn
  refine mm_draw_seq _ _ _ Ex Ex Wt Wt (B.par.core Ex) (B.par.honC Ex msg)
    (B.par.maskDataC Ex msg Rd) B.Z.D B.nx B.InHolds
    (psc_core_mm E B.par Ex Wt msg Rd hV hD (batt_own E B Rd hO)) ?_ ?_
  · exact fun x k β h => batt_fwd E B x β k h
  · intro x k Mv h q
    rw [← h q]
    refine B.lhs_congr (fun a => Function.extend_apply' _ _ _ (by rintro ⟨i, e⟩; exact hO.wM i a e))
      fun j hj => Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact hj (hO.wS q x.2 i))

open Classical in
theorem batt_goodM_sig : Spec.batt_goodM_sig E := fun S B E₀ Wp Kc A0 msg Rd hn hZ hO =>
  { base := sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ (B.batt E₀) _ _ _ _ _
      (batt_goodAt E B E₀ S.Msg Wp Kc A0 msg hn hZ)
    mm := mm_mapW _ _ _ _ _ _ _ _ _ _ _ _ _
      (mm_keep _ _ _ _ _ _ _ _ _ S.Smp S.ext
        (batt_mm E B E₀ (S.Msg × Wp) (fun w => msg w.1) Rd hn hO))
    claim := fun x _ w h q => by
      show B.lhs x.1.2 q (fun j => if Rd j then msg (S.msgs w.1) j else 0) = x.1.1 q
      rw [← h.2.2.2 q]
      exact B.lhs_congr (fun a => if_pos (hO.rdM a)) fun j hj =>
        if_pos (by by_contra hr; exact hj (hO.rdS q x.1.2 j hr)) }

theorem batt_len : Spec.batt_len E := fun B Ex => by
  show ([IOR.drawRound B.Z.D] ++ (pRound0 E :: pRounds B.fmt)).length = _
  simp [pRounds]

theorem batt_own_card : Spec.batt_own_card E := fun B => by
  rw [psc_own_card E B.fmt, List.map_replicate, List.sum_replicate, smul_eq_mul, add_comm]

end Main
end Cb
