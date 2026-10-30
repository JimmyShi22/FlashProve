-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpBitProofs.lean: the proofs of the statements of Cb/Ld/LdLkpBit.lean (the bit test of the
lookup).
-/
import Cb.Ld.LdLkpBit
import Cb.Ld.LdPscProofsIor

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

/-- a row that reads a table at its places, with weights, and one further entry -/
theorem lk_row_sum {E J K : Type} [Field E] [Fintype J] [Fintype K] [DecidableEq J] (tAt : K → J)
    (e : K → E) (cAt : J) (l : E) (m : J → E) :
    ∑ j, ((∑ b, if tAt b = j then e b else 0) + if j = cAt then l else 0) * m j =
      ∑ b, e b * m (tAt b) + m cAt * l := by
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_comm l]

section
variable (E : Type) [Field E] [Fintype E]

theorem LkBit.G_corner (B : LkBit E) (st : B.St) (m : B.J → E) (b : Fin B.k → Bool) :
    B.zc.G st m () (Alg.corner b) = m (B.tAt b) * (m (B.tAt b) - 1) := by
  show B.Y m (Alg.corner b) * (B.Y m (Alg.corner b) - 1) + ∑ b' : Empty, _ = _
  unfold LkBit.Y
  rw [Alg.mle_corner]
  simp

theorem ldLkpBit_zero : Spec.ldLkpBit_zero E := fun B st m =>
  ⟨fun h b => (B.G_corner E st m b).symm.trans (h () b),
    fun h _ b => (B.G_corner E st m b).trans (h b)⟩

theorem ldLkpBit_degX : Spec.ldLkpBit_degX E := by
  intro B st (m : B.J → E) (u : Unit → E)
  have hg : Alg.DegLE (fun _ : Fin B.k => (pfCube E 2).n) fun z =>
      (Alg.mle (fun b : Fin B.k → Bool => m (B.tAt fun v => b (B.sg.symm v))) z + u ()) *
        (Alg.mle (fun b : Fin B.k → Bool => m (B.tAt fun v => b (B.sg.symm v))) z + u () - 1) :=
    (((Alg.DegLE.mle _).add (Alg.DegLE.const _ (u ()))).mul
        (((Alg.DegLE.mle _).add (Alg.DegLE.const _ (u ()))).sub (Alg.DegLE.const _ 1))).mono
      fun _ => le_refl _
  have h := hdeg_of_degLE (pfCube E 2) B.k (pdEqs E 2 B.k (B.zc.zS st.2.2)) _ hg
  have e : (fun X =>
        B.zc.next.S0 st X (fun a => B.zc.next.F st m a X + u a) +
          ∑ b, B.zc.next.S1 st X (fun a => B.zc.next.F st m a X + u a) b * B.zc.next.Fb st m b X) =
      fun X =>
        (Alg.mle (fun b : Fin B.k → Bool => m (B.tAt fun v => b (B.sg.symm v)))
              (hFnOf (pfCube E 2) B.k (pdEqs E 2 B.k (B.zc.zS st.2.2)) X) + u ()) *
            (Alg.mle (fun b : Fin B.k → Bool => m (B.tAt fun v => b (B.sg.symm v)))
              (hFnOf (pfCube E 2) B.k (pdEqs E 2 B.k (B.zc.zS st.2.2)) X) + u () - 1) := by
    funext X
    rw [← mle_perm B.sg (fun b => m (B.tAt b))
      (hFnOf (pfCube E 2) B.k (pdEqs E 2 B.k (B.zc.zS st.2.2)) X)]
    show (∑ _t : Unit, (1 : E) *
          ((B.Y m (fun i =>
                hFnOf (pfCube E 2) B.k (pdEqs E 2 B.k (B.zc.zS st.2.2)) X (B.sg.symm i)) + u ()) *
            (B.Y m (fun i =>
                hFnOf (pfCube E 2) B.k (pdEqs E 2 B.k (B.zc.zS st.2.2)) X (B.sg.symm i)) + u () -
              1))) +
        ∑ b : Empty, _ = _
    simp [LkBit.Y]
  rw [e]
  exact h

theorem ldLkpBit_degY : Spec.ldLkpBit_degY E := by
  intro B st X (v : Unit → E) (u : Unit → E) r
  obtain ⟨c, hc⟩ := degY_prod 2 ![v (), v () - 1] ![u (), u ()]
  refine ⟨c, fun y => ?_⟩
  have h := hc y
  rw [Fin.prod_univ_two] at h
  refine Eq.trans ?_ h
  show (∑ _t : Unit, (1 : E) * ((v () + u () * y) * (v () + u () * y - 1))) + ∑ b : Empty, _ = _
  simp
  ring_nf
  tauto

theorem LkBit.zero_eq (B : LkBit E) : B.zc.ZeroHolds = fun _ m => B.AllBits m :=
  funext fun st => funext fun m => propext (ldLkpBit_zero E B st m)

theorem ldLkpBit_goodAt : Spec.ldLkpBit_goodAt E := by
  intro B Ex M Wp Kc R0 msg
  have h := ldZero_psc_goodAt
    E B.zc Ex M Wp Kc R0 msg (ldZero_ok_one E) (ldLkpBit_degX E B) (ldLkpBit_degY E B)
  rw [B.zero_eq E] at h
  exact h

theorem ldLkpBit_good : Spec.ldLkpBit_good E := by
  intro B S E₀ Wp Kc R0 msg
  have h :=
    ldZero_psc E B.zc S E₀ Wp Kc R0 msg (ldZero_ok_one E) (ldLkpBit_degX E B) (ldLkpBit_degY E B)
  rw [B.zero_eq E] at h
  exact h

theorem ldLkpBit_row : Spec.ldLkpBit_row E := fun _ _ _ => Iff.rfl

theorem ldLkpBit_lin : Spec.ldLkpBit_lin E := by
  intro B
  refine ⟨fun s m a X => ?_, fun _ _ b _ => b.elim⟩
  classical
  have h :=
    lk_row_sum B.tAt (Alg.eqk (B.zc.fn s.2.2 (B.zc.next.ini s X))) B.cAt (B.zc.next.lst s X) m
  refine Eq.trans ?_ (Eq.trans h.symm ?_)
  · rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    unfold LkBit.rowA
    congr 2

theorem ldLkpBit_rows : Spec.ldLkpBit_rows E := fun B o m =>
  ⟨fun h =>
      ⟨(psc_row_U E _ _ (ldLkpBit_lin E B).2 o m).1 h.1,
        (psc_row_E E _ _ (ldLkpBit_lin E B).1 o m ()).1 (h.2 ())⟩,
    fun h =>
      ⟨(psc_row_U E _ _ (ldLkpBit_lin E B).2 o m).2 h.1,
        fun _ => (psc_row_E E _ _ (ldLkpBit_lin E B).1 o m ()).2 h.2⟩⟩

theorem ldLkpBit_err : Spec.ldLkpBit_err E := fun B => by
  show 0 * Fintype.card (Fin B.k → E) +
      Fintype.card Unit * (Fintype.card (Fin B.k) * Fintype.card E ^ (Fintype.card (Fin B.k) - 1)) =
    _
  simp

theorem ldLkpBit_len : Spec.ldLkpBit_len E := fun B S E₀ => by
  rw [pscIn_psc_len E]
  show 1 + ((List.replicate B.k (pfCube E 2)).length + 3) = _
  rw [List.length_replicate]

theorem ldLkpBit_num : Spec.ldLkpBit_num E := by
  intro B T w num M m hm
  constructor
  · intro h u hu j hj
    have h1 := h (num.symm (⟨u, hu⟩, ⟨j, hj⟩))
    rw [hm, Equiv.apply_symm_apply] at h1
    exact h1
  · intro h b
    rw [hm]
    exact h _ (num b).1.2 _ (num b).2.2

end
end Cb
