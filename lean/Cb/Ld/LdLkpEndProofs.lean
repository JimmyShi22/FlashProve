-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpEndProofs.lean: the proofs of the statements of Cb/Ld/LdLkpEnd.lean (the end claim of the
table's product trees in the lookup, closed by one sumcheck for a polynomial summand).

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names, each under the hypotheses of its statement (Cb/Ld/LdLkpEnd.lean):
  `ldLkpEnd_sum`: the claim is the sumcheck's input claim.
  `ldLkpEnd_vars`, `ldLkpEnd_degX`, `ldLkpEnd_degY`: all conditions of the sumcheck
    (`PscOur.VarsOK`, `ValInj`, `DegX`, `DegY`, Cb/Ld/LdPsc.lean) hold of `B.psc`.
  `ldLkpEnd_joint`: the input joint is the sumcheck's own.
  `ldLkpEnd_goodAt`: at the base, for each fixed tuple of messages of any type, any joint A0 riding
    along: `GoodAt` from (A0 and the claim) to (A0 and the sumcheck's two rows); the identity
    extracts; no hypothesis is left beyond those of its statement.
  `ldLkpEnd_good`: the same over a signature: all of `IOR.GoodT` but zero knowledge. Knowledge
    soundness covers only the statements at which A0's condition holds and samples and words of S
    are collision-free (`S.CF`, Cb/Ld/LdSig.lean).
  `ldLkpEnd_lin`, `ldLkpEnd_rows`: the output rows are linear rows with public targets.
  `ldLkpEnd_row`: the row on the bits.
  `ldLkpEnd_less`: the constant taken out.
  `ldLkpEnd_len`: k + 3 rounds.
How the two main theorems are got (read off the proofs): `ldLkpEnd_joint` rewrites the input joint;
then `psc_our_goodAt` (Cb/Ld/LdLineAt.lean) for `ldLkpEnd_goodAt`, `psc_our_goodB_true`
(Cb/Ld/LdPscSig.lean) for `ldLkpEnd_good`, each at `ldLkpEnd_vars`, `ldLkpEnd_degX`,
`ldLkpEnd_degY`.

Limits: see the head of Cb/Ld/LdLkpEnd.lean.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpEnd
import Cb.Ld.LdLkpBitProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpEnd_sum : Spec.ldLkpEnd_sum E := by
  intro B x m
  have e : hSumAll (B.psc.vars x.2) (B.psc.sum x.2 m) =
      Alg.mle (fun b => 1 + m (B.tAt b) * B.cp x.2 b) (B.z x.2) := by
    show hSumAll (pVars (List.replicate B.k (pfCube E 2)) (pdEqs E 2 B.k (B.z x.2)))
        (B.psc.sum x.2 m) = _
    rw [psv_eqs_sum E]
    unfold Alg.mle
    refine Finset.sum_congr rfl fun b _ => ?_
    have hx : B.fn x.2 (pH _ (pdEqs E 2 B.k (B.z x.2)) (ppOf (pfCube E 2) B.k (Alg.corner b))) =
        Alg.corner b :=
      psv_fn_pt E (pfCube E 2) B.k (pdEqs E 2 B.k (B.z x.2)) (Alg.corner b)
    have hs : B.psc.sum x.2 m
          (pH _ (pdEqs E 2 B.k (B.z x.2)) (ppOf (pfCube E 2) B.k (Alg.corner b))) =
        1 + m (B.tAt b) * B.cp x.2 b := by
      show 1 + Alg.mle (B.cp x.2) (B.fn x.2 _) * B.Y m (B.fn x.2 _) + ∑ b' : Empty, _ = _
      rw [hx]
      unfold LkEnd.Y
      rw [Alg.mle_corner, Alg.mle_corner]
      simp [mul_comm]
    exact congrArg (fun s => Alg.eqk (B.z x.2) b * s) hs
  show hSumAll (B.psc.vars x.2) (B.psc.sum x.2 m) + ∑ j, B.inc x.2 j * m j = x.1 ↔ _
  rw [e]
  exact Iff.rfl

theorem ldLkpEnd_vars : Spec.ldLkpEnd_vars E := fun B =>
  ⟨fun s => psv_eqs_ok E 2 B.k (B.z s),
    fun f hf => by rw [List.eq_of_mem_replicate hf]; exact (psv_val E).1 2⟩

theorem ldLkpEnd_degX : Spec.ldLkpEnd_degX E := by
  intro B st (m : B.J → E) (u : Unit → E)
  have hg : Alg.DegLE (fun _ : Fin B.k => (pfCube E 2).n) fun z =>
      1 + Alg.mle (B.cp st) z * (B.Y m z + u ()) :=
    (Alg.DegLE.const _ 1).add
      (((Alg.DegLE.mle _).mul ((Alg.DegLE.mle _).add (Alg.DegLE.const _ (u ())))).mono
        fun _ => le_refl _)
  have h := hdeg_of_degLE (pfCube E 2) B.k (pdEqs E 2 B.k (B.z st)) _ hg
  have e : (fun X =>
        B.psc.S0 st X (fun a => B.psc.F st m a X + u a) +
          ∑ b, B.psc.S1 st X (fun a => B.psc.F st m a X + u a) b * B.psc.Fb st m b X) =
      fun X =>
        1 + Alg.mle (B.cp st) (hFnOf (pfCube E 2) B.k (pdEqs E 2 B.k (B.z st)) X) *
              (B.Y m (hFnOf (pfCube E 2) B.k (pdEqs E 2 B.k (B.z st)) X) + u ()) := by
    funext X
    exact add_zero _
  rw [e]
  exact h

theorem ldLkpEnd_degY : Spec.ldLkpEnd_degY E := by
  intro B st X (v : Unit → E) (u : Unit → E) r
  obtain ⟨c, hc⟩ :=
    degY_prod 1 ![1 + Alg.mle (B.cp st) (B.fn st X) * v ()] ![Alg.mle (B.cp st) (B.fn st X) * u ()]
  refine ⟨c, fun y => ?_⟩
  refine Eq.trans ?_ (hc y)
  show 1 + Alg.mle (B.cp st) (B.fn st X) * (v () + u () * y) + ∑ b : Empty, _ = _
  simp
  ring

theorem ldLkpEnd_joint : Spec.ldLkpEnd_joint E := by
  intro B Ex Wt Kc A0 msg
  have e : B.psc.SumHolds = B.Holds :=
    funext fun x => funext fun m => propext (ldLkpEnd_sum E B x m)
  unfold PscOur.baseIn PscPar.baseRels
  rw [e]
  rfl

theorem ldLkpEnd_goodAt : Spec.ldLkpEnd_goodAt E := by
  intro B Ex M Wp Kc A0 msg
  rw [ldLkpEnd_joint E]
  exact psc_our_goodAt E B.psc Ex M Wp Kc A0 msg (ldLkpEnd_vars E B).1 (ldLkpEnd_degX E B)
    (ldLkpEnd_degY E B) (ldLkpEnd_vars E B).2

theorem ldLkpEnd_good : Spec.ldLkpEnd_good E := by
  intro B S E₀ Wp Kc A0 msg
  rw [ldLkpEnd_joint E]
  exact psc_our_goodB_true E S B.psc E₀ Wp Kc A0 msg (ldLkpEnd_vars E B).1 (ldLkpEnd_degX E B)
    (ldLkpEnd_degY E B) (ldLkpEnd_vars E B).2

theorem ldLkpEnd_row : Spec.ldLkpEnd_row E := fun _ _ _ => Iff.rfl

theorem ldLkpEnd_lin : Spec.ldLkpEnd_lin E := by
  intro B
  refine ⟨fun s m a X => ?_, fun _ _ b _ => b.elim⟩
  classical
  have h := lk_row_sum B.tAt (Alg.eqk (B.fn s (B.psc.ini s X))) B.cAt (B.psc.lst s X) m
  refine Eq.trans ?_ (Eq.trans h.symm ?_)
  · rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    unfold LkEnd.rowA
    congr 2

theorem ldLkpEnd_rows : Spec.ldLkpEnd_rows E := fun B o m =>
  ⟨fun h =>
      ⟨(psc_row_U E _ _ (ldLkpEnd_lin E B).2 o m).1 h.1,
        (psc_row_E E _ _ (ldLkpEnd_lin E B).1 o m ()).1 (h.2 ())⟩,
    fun h =>
      ⟨(psc_row_U E _ _ (ldLkpEnd_lin E B).2 o m).2 h.1,
        fun _ => (psc_row_E E _ _ (ldLkpEnd_lin E B).1 o m ()).2 h.2⟩⟩

theorem ldLkpEnd_less : Spec.ldLkpEnd_less E := by
  intro B x m
  have e : Alg.mle (fun b => 1 + m (B.tAt b) * B.cp x.2 b) (B.z x.2) =
      1 + Alg.mle (fun b => B.cp x.2 b * m (B.tAt b)) (B.z x.2) := by
    unfold Alg.mle
    simp only [mul_add, mul_one, Finset.sum_add_distrib, Alg.sum_eqk]
    exact congrArg _ (Finset.sum_congr rfl fun b _ => by ring)
  unfold LkEnd.Holds
  rw [e]
  constructor
  · intro h; rw [← h]; ring
  · intro h; rw [add_assoc, h]; ring

theorem ldLkpEnd_len : Spec.ldLkpEnd_len E := fun B Ex => by
  rw [psc_our_len E]
  show (List.replicate B.k (pfCube E 2)).length + 3 = _
  rw [List.length_replicate]

end
end Cb
