-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdZeroSkipProofs.lean: proofs for Cb/Ld/LdZero.lean: the Lagrange weights of a domain of
distinct points are a zero-evader; the zerocheck with the first variable over a domain.

An evader (`Cb.Evader`, Cb/Gen/BatEvader.lean): the seeds, the coefficients that a seed gives, and a
number err; its property (`Evader.OK`): a vector other than 0 is annihilated by at most err seeds.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (statements and hypotheses: Cb/Ld/LdZero.lean):
  `ldZero_ok_lag`: the Lagrange weights of a domain of distinct points: `Evader.OK`.
  `ldZeroS_link`, `ldZeroS_back`, `ldZeroS_ok`: the conditions of the step at the zerocheck with the
    first variable over a domain (`ev.OK` for distinct points, under `Z.co.OK`).
  `ldZeroS_all`: "all claims hold" as that zerocheck's claim.
  `ldZeroS_vars`: for distinct points and a domain that is not empty: the conditions on the
    variables of the sumcheck that follows.
  `ldZeroS_err`: the number of bad messages, as a count of the |co.D| |E|^(k+1) messages: co.err
    |E|^(k+1) + |co.D| ((|domain| - 1) |E|^k + |E| k |E|^(k-1)); for one function (Tt = Unit, co =
    `Evader.one`), by reading: (|domain| - 1 + k) |E|^k of |E|^(k+1).
  `ldZeroS_piece`: for distinct points, under `Z.co.OK`: the zerocheck with the first variable over
    a domain, over a signature: `pscIn_piece` (Cb/Ld/LdZeroProofs.lean) at `Z.toIn`, by the four on
    link, back, ok, all; its error: `ldZeroS_err`.

Notation:
  `Z`: the parameters of the zerocheck on (domain × cube) (`ZeroSkip`);
  `Z.dom`: of type `Z.D → E`: the domain's points;
  `Z.toIn`: of type `PscIn E`, the parameters of the step;
  `co`: the evader `Z.co`;
  `S`: a signature, the oracle messages of a statement (`Sig`, Cb/Ld/LdSig.lean).
  (`ZeroSkip`, `PscIn`: Cb/Ld/LdZero.lean; `Evader`: Cb/Gen/BatEvader.lean.)

Limits: see the head of Cb/Ld/LdZero.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdZeroProofs
import Cb.Ld.LdPscVarsMixProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Polynomial

section
variable (E : Type) [Field E] [Fintype E]

/-- for distinct points, the interpolant of a vector other than 0 has at most
(size of the domain) - 1 roots -/
theorem ldZero_ok_lag : Spec.ldZero_ok_lag E := by
  intro D _ _ dom hd v hv
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hv
  have hp0 : Lagrange.interpolate Finset.univ dom v ≠ 0 := fun h0 => hx₀ (by
    have h := Lagrange.eval_interpolate_at_node v hd.injOn (Finset.mem_univ x₀)
    rw [h0, eval_zero] at h
    exact h.symm)
  have hdeg : (Lagrange.interpolate Finset.univ dom v).natDegree ≤ Fintype.card D - 1 := by
    have h := Lagrange.degree_interpolate_lt v (s := Finset.univ) hd.injOn
    rw [Finset.card_univ] at h
    have h2 := (natDegree_lt_iff_degree_lt hp0).2 h
    omega
  have he : ∀ z : E, ∑ x, (Lagrange.basis Finset.univ dom x).eval z * v x =
      (Lagrange.interpolate Finset.univ dom v).eval z := fun z => by
    rw [Lagrange.interpolate_apply, eval_finset_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [eval_mul, eval_C, mul_comm]
  show cnt (fun z : E => ∑ x, (Lagrange.basis Finset.univ dom x).eval z * v x = 0) ≤
    Fintype.card D - 1
  simp only [he]
  refine le_trans ?_ hdeg
  classical
  rw [cnt_eq_card_filter]
  refine le_trans (Finset.card_le_card fun z hz => ?_)
    (card_roots' (Lagrange.interpolate Finset.univ dom v)
      |> fun h => (Multiset.toFinset_card_le _).trans h)
  rw [Multiset.mem_toFinset, mem_roots hp0]
  exact (Finset.mem_filter.1 hz).2

theorem ldZeroS_link : Spec.ldZeroS_link E := by
  intro Z st β m
  show hSumAll (pVars (pfSkip E Z.n₁ Z.n Z.D Z.k) (pdSkipW E Z.n₁ Z.n Z.dom β.2.1 Z.k β.2.2))
        (Z.next.sum (st, β) m) +
      ∑ j : Z.J, (0 : E) * m j =
    ∑ i : Z.Tt × (Z.D × (Fin Z.k → Bool)),
      (Z.co.ze β.1 i.1 *
          ((Lagrange.basis Finset.univ Z.dom i.2.1).eval β.2.1 * Alg.eqk β.2.2 i.2.2)) *
        Z.G st m i.1 (Z.dom i.2.1) (Alg.corner i.2.2)
  rw [psm_sumW E]
  simp only [zero_mul, Finset.sum_const_zero, add_zero, Fintype.sum_prod_type]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hx : hFnOf (pfCube E Z.n) Z.k (pdEqs E Z.n Z.k β.2.2)
        (pH _ (pdEqs E Z.n Z.k β.2.2) (ppOf (pfCube E Z.n) Z.k (Alg.corner b))) = Alg.corner b :=
    psv_fn_pt E (pfCube E Z.n) Z.k (pdEqs E Z.n Z.k β.2.2) (Alg.corner b)
  have hs : Z.next.sum (st, β) m
        (Z.dom d, pH _ (pdEqs E Z.n Z.k β.2.2) (ppOf (pfCube E Z.n) Z.k (Alg.corner b))) =
      ∑ t, Z.co.ze β.1 t * Z.G st m t (Z.dom d) (Alg.corner b) := by
    show (∑ t, Z.co.ze β.1 t *
          Z.S0 st t (Z.dom d) (hFnOf (pfCube E Z.n) Z.k (pdEqs E Z.n Z.k β.2.2) _)
            fun a => Z.F st m a (Z.dom d) (hFnOf (pfCube E Z.n) Z.k (pdEqs E Z.n Z.k β.2.2) _)) +
        ∑ b', (∑ t, Z.co.ze β.1 t *
            Z.S1 st t (Z.dom d) (hFnOf (pfCube E Z.n) Z.k (pdEqs E Z.n Z.k β.2.2) _)
              (fun a => Z.F st m a (Z.dom d) (hFnOf (pfCube E Z.n) Z.k (pdEqs E Z.n Z.k β.2.2) _))
              b') *
          Z.Fb st m b' (Z.dom d) (hFnOf (pfCube E Z.n) Z.k (pdEqs E Z.n Z.k β.2.2) _) = _
    rw [hx]
    unfold ZeroSkip.G
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  calc
    _ = eval β.2.1 (Lagrange.basis Finset.univ Z.dom d) *
          (Alg.eqk β.2.2 b * ∑ t, Z.co.ze β.1 t * Z.G st m t (Z.dom d) (Alg.corner b)) :=
        congrArg (fun s =>
          eval β.2.1 (Lagrange.basis Finset.univ Z.dom d) * (Alg.eqk β.2.2 b * s)) hs
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring

theorem ldZeroS_back : Spec.ldZeroS_back E := fun _ _ _ => rfl

theorem ldZeroS_ok : Spec.ldZeroS_ok E := fun Z hd h =>
  ldZero_ok_prod E _ _ Z.co _ h
    (ldZero_ok_prod E _ _ (Evader.lag E Z.dom) (Evader.eqPt E (Fin Z.k))
      (ldZero_ok_lag E Z.D Z.dom hd) (ok_eqPt E (Fin Z.k)))

theorem ldZeroS_all : Spec.ldZeroS_all E := fun _ _ _ =>
  ⟨fun h t d b => h (t, (d, b)), fun h i => h i.1 i.2.1 i.2.2⟩

theorem ldZeroS_vars : Spec.ldZeroS_vars E := fun Z hd hne =>
  ⟨fun s => haveI := hne; psm_okW E Z.n₁ Z.n Z.k Z.D Z.dom s.2.2.1 s.2.2.2 hd, fun f hf => by
    rcases List.mem_cons.1 hf with rfl | h
    · exact (psv_val E).2 Z.n₁ Z.D
    · rw [List.eq_of_mem_replicate h]; exact (psv_val E).1 Z.n⟩

theorem ldZeroS_err : Spec.ldZeroS_err E := fun Z => by
  show Z.co.err * Fintype.card (E × (Fin Z.k → E)) +
      Fintype.card Z.co.D *
        ((Fintype.card Z.D - 1) * Fintype.card (Fin Z.k → E) +
          Fintype.card E *
            (Fintype.card (Fin Z.k) * Fintype.card E ^ (Fintype.card (Fin Z.k) - 1))) = _
  simp

theorem ldZeroS_piece : Spec.ldZeroS_piece E := by
  intro Z S E₀ Wp Kc R0 msg q hd hco
  have e : Z.toIn.AllHold = Z.ZeroHolds :=
    funext fun st => funext fun m => propext (ldZeroS_all E Z st m)
  have h := pscIn_piece E Z.toIn S E₀ Wp Kc R0 msg q (ldZeroS_link E Z)
    (ldZeroS_back E Z) (ldZeroS_ok E Z hd hco)
  unfold PscIn.relsIn at h
  rw [e] at h
  exact h

end
end Cb
