-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdZeroProofs.lean: proofs for Cb/Ld/LdZero.lean: the general step (claims on values into one
sum claim), the evaders "one" and "prod", the zerocheck on the cube. (The Lagrange weights and the
zerocheck with a first variable over a domain: Cb/Ld/LdZeroSkipProofs.lean.)

In standard terms: a batching of claims, by a seed that the verifier draws, into the input claim of
a sumcheck; and the zerocheck.
An evader (`Cb.Evader`, Cb/Gen/BatEvader.lean): the seeds, the coefficients that a seed gives, and a
number err; its property (`Evader.OK`): a vector other than 0 is annihilated by at most err seeds.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (statements and hypotheses: Cb/Ld/LdZero.lean):
  `pscIn_iff`, `pscIn_fwd`: under `Z.Link`: the new claim as "the combination of the gaps is 0"; the
    new claim at every seed if all claims hold.
  `pscIn_cnt`: under `Z.Link` and `Z.ev.OK`, for each fixed tuple of entries of which not all claims
    hold: at most ev.err seeds at which the new claim holds.
  `pscIn_piece`: under `Z.Link`, `Z.Back` and `Z.ev.OK`: the step over a signature: a piece of a
    chain (`IOR.Piece`, Ior/Tail.lean) from (all claims, and R0) to (T's sum claim, and R0), with
    the one error `Z.ev.err`, a count of seeds.
  `ldZero_ok_one`, `ldZero_ok_prod`: the property `Evader.OK` of the evaders "one" and "prod": the
    product if both factors have it.
  `ldZero_link`, `ldZero_back`, `ldZero_ok`: the conditions of the step at the zerocheck on the cube
    (`ev.OK` under `Z.co.OK`).
  `ldZero_all`: "all claims hold" as the zerocheck's claim.
  `ldZero_tg`: the new target 0.
  `ldZero_vars`: the conditions on the variables of the sumcheck that follows.
  `ldZero_err`: the number of bad messages, as a count of the |co.D| |E|^k messages: co.err |E|^k +
    |co.D| k |E|^(k-1).
  `ldZero_piece`: under `Z.co.OK`: the zerocheck over a signature: `pscIn_piece` at `Z.toIn`, by the
    four on link, back, ok, all; its error: `ldZero_err`.

Notation:
  `Z`: the parameters of the step (`PscIn`), or of the zerocheck on the cube (`ZeroCube`);
  `Z.toIn`: the zerocheck as a step into a sumcheck;
  `Z.Link`: the new claim is a sum claim (`PscIn.Link`);
  `Z.Back`: `Z.old (Z.nx st β) = st` for all st and β (`PscIn.Back`);
  `T`: `Z.T`, the sumcheck that follows;
  `ev`, `co`: the evaders `Z.ev`, `Z.co`;
  `st`: a state before the step;
  `β`: a seed of `Z.ev`;
  `m`: of type `Z.T.J → E` (for a `ZeroCube`: `Z.J → E`; in the proof of `pscIn_piece`: of type
    `S.Msg`);
  `S`: a signature, the oracle messages of a statement (`Sig`, Cb/Ld/LdSig.lean);
  `R0`: a joint (`IOR.Rels`, Ior/Chain.lean);
  `msg`: of type `S.Msg → Z.T.J → E` (for a `ZeroCube`: `S.Msg → Z.J → E`);
  `q`: a predicate on sets of positions.
  (`PscIn`, `ZeroCube`, `toIn`: Cb/Ld/LdZero.lean; `Evader`: Cb/Gen/BatEvader.lean.)

Limits: see the head of Cb/Ld/LdZero.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdZero
import Cb.Ld.LdPscVarsProofs
import Cb.Gen.BatEvaderProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section
variable (E : Type) [Field E] [Fintype E]

theorem pscIn_iff : Spec.pscIn_iff E := by
  intro Z hL st β m
  show hSumAll (Z.T.vars (Z.nx st β)) (Z.T.sum (Z.nx st β) m) + ∑ j, Z.T.slS (Z.nx st β) j * m j =
      ∑ i, Z.ev.ze β i * Z.tg st i ↔
    _
  rw [hL st β m]
  simp only [mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.symm

theorem pscIn_fwd : Spec.pscIn_fwd E := fun Z hL st β m h =>
  (pscIn_iff E Z hL st β m).2 (Finset.sum_eq_zero fun i _ => by rw [h i, sub_self, mul_zero])

theorem pscIn_cnt : Spec.pscIn_cnt E := fun Z hL hOK st m hn =>
  (cnt_mono fun β h => (pscIn_iff E Z hL st β m).1 h).trans
    (hOK (fun i => Z.val st m i - Z.tg st i) fun h0 => hn fun i => sub_eq_zero.1 (congrFun h0 i))

theorem pscIn_piece : Spec.pscIn_piece E := by
  intro Z S E₀ Wp Kc R0 msg q hL hB hOK
  refine sig_draw E S Kc Z.St0 (E × Z.T.St) Wp Z.ev.D E₀ Z.nxX (Z.relsIn R0 msg) (Z.relsOut R0 msg)
    Z.ev.err q ?_ ?_ (fun _ => rfl) ?_
  · intro st y w β h
    refine ⟨?_, pscIn_fwd E Z hL st β (msg w.1) h.2⟩
    show R0.rel (Z.old (Z.nx st β)) y w
    rw [hB]
    exact h.1
  · intro st y β h
    show R0.on (Z.old (Z.nx st β), y)
    rw [hB]
    exact h
  · intro st y m _
    by_cases hA : Z.AllHold st (msg m)
    · rw [cnt_false]
      · exact Nat.zero_le _
      · rintro β ⟨wp, h1, h2⟩
        have h3 : R0.relR (Z.old (Z.nx st β), y) (m, wp) := h1.1
        rw [hB] at h3
        exact h2 ⟨h3, hA⟩
    · exact (cnt_mono fun β h => h.elim fun wp h1 => h1.1.2).trans
        (pscIn_cnt E Z hL hOK st (msg m) hA)

omit [Fintype E] in
theorem ldZero_ok_one : Spec.ldZero_ok_one E := by
  intro v hv
  rw [cnt_false]
  intro _ h
  apply hv
  funext u
  simpa using h

omit [Fintype E] in
theorem ldZero_ok_prod : Spec.ldZero_ok_prod E := by
  intro I₁ I₂ _ _ Z₁ Z₂ h₁ h₂ v hv
  obtain ⟨⟨i0, j0⟩, hij⟩ := Function.ne_iff.1 hv
  have hsum : ∀ ρ : Z₁.D × Z₂.D, ∑ i : I₁ × I₂, (Z₁.ze ρ.1 i.1 * Z₂.ze ρ.2 i.2) * v i =
      ∑ j, Z₂.ze ρ.2 j * ∑ i, Z₁.ze ρ.1 i * v (i, j) := by
    intro ρ
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine cnt_two_rounds_le
    (fun ρ : Z₁.D × Z₂.D => ∑ i : I₁ × I₂, (Z₁.ze ρ.1 i.1 * Z₂.ze ρ.2 i.2) * v i = 0)
    (fun ρ₁ => (fun j => ∑ i, Z₁.ze ρ₁ i * v (i, j)) = 0) Z₁.err Z₂.err ?_ ?_
  · exact (cnt_mono fun ρ₁ h => congrFun h j0).trans
      (h₁ (fun i => v (i, j0)) fun h0 => hij (congrFun h0 i0))
  · intro ρ₁ hρ
    refine (cnt_mono fun ρ₂ h => ?_).trans (h₂ _ hρ)
    rw [← hsum (ρ₁, ρ₂)]
    exact h

theorem ldZero_link : Spec.ldZero_link E := by
  intro Z st β m
  show hSumAll (pVars (List.replicate Z.k (pfCube E Z.n)) (pdEqs E Z.n Z.k (Z.zS β.2)))
        (Z.next.sum (st, β) m) +
      ∑ j : Z.J, (0 : E) * m j =
    ∑ i : Z.Tt × (Fin Z.k → Bool),
      (Z.co.ze β.1 i.1 * Alg.eqk β.2 i.2) * Z.G st m i.1 (Alg.corner i.2)
  rw [psv_eqs_sum E]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Fintype.sum_equiv (Z.sg.arrowCongr (Equiv.refl Bool)) _ _ fun b => ?_
  show _ = ∑ t, (Z.co.ze β.1 t * Alg.eqk β.2 (fun v => b (Z.sg.symm v))) *
    Z.G st m t (Alg.corner fun v => b (Z.sg.symm v))
  have he : Alg.eqk (Z.zS β.2) b = Alg.eqk β.2 (fun v => b (Z.sg.symm v)) := by
    have h := Alg.eqk_equiv Z.sg β.2 (fun v => b (Z.sg.symm v))
    simp only [Equiv.symm_apply_apply] at h
    exact h
  have hx : Z.fn β.2 (pH _ (pdEqs E Z.n Z.k (Z.zS β.2)) (ppOf (pfCube E Z.n) Z.k (Alg.corner b))) =
      Alg.corner fun v => b (Z.sg.symm v) := by
    funext i
    show hFnOf (pfCube E Z.n) Z.k (pdEqs E Z.n Z.k (Z.zS β.2))
        (pH _ (pdEqs E Z.n Z.k (Z.zS β.2)) (ppOf (pfCube E Z.n) Z.k (Alg.corner b)))
        (Z.sg.symm i) = _
    rw [psv_fn_pt E (pfCube E Z.n) Z.k (pdEqs E Z.n Z.k (Z.zS β.2)) (Alg.corner b)]
    rfl
  have hs : Z.next.sum (st, β) m
        (pH _ (pdEqs E Z.n Z.k (Z.zS β.2)) (ppOf (pfCube E Z.n) Z.k (Alg.corner b))) =
      ∑ t, Z.co.ze β.1 t * Z.G st m t (Alg.corner fun v => b (Z.sg.symm v)) := by
    show (∑ t, Z.co.ze β.1 t * Z.S0 st t (Z.fn β.2 _) fun a => Z.F st m a (Z.fn β.2 _)) +
        ∑ b', (∑ t, Z.co.ze β.1 t * Z.S1 st t (Z.fn β.2 _) (fun a => Z.F st m a (Z.fn β.2 _)) b') *
          Z.Fb st m b' (Z.fn β.2 _) = _
    rw [hx]
    unfold ZeroCube.G
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hs, he, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem ldZero_back : Spec.ldZero_back E := fun _ _ _ => rfl

theorem ldZero_ok : Spec.ldZero_ok E := fun Z h =>
  ldZero_ok_prod E _ _ Z.co (Evader.eqPt E (Fin Z.k)) h (ok_eqPt E (Fin Z.k))

theorem ldZero_all : Spec.ldZero_all E := fun _ _ _ => ⟨fun h t b => h (t, b), fun h i => h i.1 i.2⟩

theorem ldZero_tg : Spec.ldZero_tg E := fun Z st β => by
  show ∑ i : Z.Tt × (Fin Z.k → Bool), (Z.co.ze β.1 i.1 * Alg.eqk β.2 i.2) * (0 : E) = 0
  simp

theorem ldZero_vars : Spec.ldZero_vars E := fun Z =>
  ⟨fun s => psv_eqs_ok E Z.n Z.k (Z.zS s.2.2),
    fun f hf => by rw [List.eq_of_mem_replicate hf]; exact (psv_val E).1 Z.n⟩

theorem ldZero_err : Spec.ldZero_err E := fun Z => by
  show Z.co.err * Fintype.card (Fin Z.k → E) +
      Fintype.card Z.co.D *
        (Fintype.card (Fin Z.k) * Fintype.card E ^ (Fintype.card (Fin Z.k) - 1)) = _
  simp

theorem ldZero_piece : Spec.ldZero_piece E := by
  intro Z S E₀ Wp Kc R0 msg q hco
  have e : Z.toIn.AllHold = Z.ZeroHolds :=
    funext fun st => funext fun m => propext (ldZero_all E Z st m)
  have h :=
    pscIn_piece E Z.toIn S E₀ Wp Kc R0 msg q (ldZero_link E Z) (ldZero_back E Z) (ldZero_ok E Z hco)
  unfold PscIn.relsIn at h
  rw [e] at h
  exact h

end
end Cb
