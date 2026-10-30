-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefPend.lean: if 1 ≤ X.n, the pending tensor row that a segment's batching leaves is
again a tensor row whose mask form is coefficients on names, laid by a fixed map: all its parts are
readers (functions) of the batching's last claim.

Definitions, one statement (`Cb.Spec.ldSegRef_pend`) and its proof.
The matter: the linear claim, on the index's matrix and on entries of the oracle messages, that the
sumcheck of a batching leaves open.

Why: the batching of a segment's tensor rows (`X : LdTenD E Kc`, Cb/Req1/LdSegRefTen.lean) ends with
a claim z (state, seed, ε, point, last value). The row that it leaves is pending: it rides on, with
those of the other segments, to one more batching after the last segment. That batching asks its
conditions at all states; so its claims must not hold mask forms as free data.
The state in which the pending rows pile up: for each earlier batching its last claim z, as it
stands.

Main names (what is read of z):
  `X.pG z`: the row vector: ε · ∑_q χ_q eq(ψ_q, γ) g_q.
  `X.pPt z`: the point γ of the batching's sumcheck.
  `X.PN`, `X.pAt`: the names of the mask coordinates: the batching's own masks, and the names of its
    incoming forms; their places: fixed (wAt, μAt).
  `X.pMf z`: the coefficients on these names: the hiding polynomial's form at γ; ε γ_1 ·· γ_k ∑_q
    χ_q (incoming coefficients).
  `X.pTg z`: the target: the last value.
  `Spec.ldSegRef_pend`: if 1 ≤ X.n: the claim that the batching leaves holds of (message of the
    index, messages) if and only if < pG z ⊗ eq(pPt z, ·), matrix > + < pMf z laid at pAt, entries >
    = pTg z: the form of a claim of Cb/Req1/LdSegRefTen.lean (`TenOK`).
So a later batching takes: z in its state; g := pG, pt := pPt, PN among its names Nm, mf := pMf, pAt
within its μAt; its conditions on own entries are: its own places differ from wAt and μAt of the
earlier ones. (all of them: `LdTenD.Own`, Cb/Req1/LdSegRefTen.lean; `Spec.ldSegRef_pe_own`,
Cb/Req1/LdSegRefPendEnds.lean)

Limits: this file says nothing on the later batching itself. It does not say that the oracle
message which holds these masks is kept at every closing.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefTenProofs
import Cb.Ld.LdRngProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.RngPk IOR

namespace LdTenD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc)

/-- the row vector, the point, the target of the pending row -/
def pG (z : X.bt.par.Mid) : X.Rw → E := fun r =>
  z.eps * ∑ q, X.bt.chi z q * Alg.eqPt (X.bt.pt z.st.1 q) (X.bt.outPt z) * X.bt.g z.st.1 q r
def pPt (z : X.bt.par.Mid) : Fin X.k → E := X.bt.outPt z
def pTg (z : X.bt.par.Mid) : E := z.fin

/-- The names of its mask coordinates, and their places. -/
abbrev PN : Type := HIdx (pVars X.bt.fmt (pdPlains E X.n X.k)) ⊕ X.Nm
def pAt : X.PN → X.S.Ent :=
  Sum.elim (fun i => X.wAt (pIx X.bt.fmt (pdPlains E X.n X.k) i)) X.μAt

/-- The coefficients on these names. -/
def pMf (z : X.bt.par.Mid) : X.PN → E :=
  Sum.elim (fun i => hSl (X.bt.par.vars z.st) (X.bt.par.hp z.st z.pt) i) fun a =>
    z.eps * (∏ i, X.bt.outPt z i) * ∑ q, X.bt.chi z q * X.mf (X.stOf z).2 q a

end LdTenD

/-- States: if 1 ≤ X.n, the pending row is a tensor row with a mask form on names. -/
def Spec.ldSegRef_pend : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenD E Kc), 1 ≤ X.n →
    ∀ (z : X.bt.par.Mid) (um : X.C.Msg × X.S.Msg),
      X.bt.par.MidHolds z (X.msg um) ↔
      X.bt.ten (X.pG z) (X.pPt z) (X.msg um) +
          ∑ j, (Sum.elim (fun _ => 0) (placed X.pAt (X.pMf z)) : X.bt.J → E) j * X.msg um j =
        X.pTg z

theorem ldSegRef_pend : Spec.ldSegRef_pend := by
  intro E Kc _ _ X hn z um
  rw [batt_row E X.bt hn z (X.msg um)]
  unfold BattPar.RowHolds
  -- a form on the entries of the messages, read on all entries of the block
  have hs : ∀ c : X.S.Ent → E,
      ∑ j, (Sum.elim (fun _ => 0) c : X.bt.J → E) j * X.msg um j = ∑ n, c n * X.S.ents um.2 n := by
    intro c
    refine (Fintype.sum_sum_type (fun x : (X.Rw × (Fin X.k → Bool)) ⊕ X.S.Ent =>
      (Sum.elim (fun _ => (0 : E)) c x) * X.msg um x)).trans ?_
    simp only [Sum.elim_inl, zero_mul, Finset.sum_const_zero, zero_add]
    rfl
  have hp : ∀ {I : Type} [Fintype I] (at' : I → X.S.Ent) (a : I → E),
      ∑ n, placed at' a n * X.S.ents um.2 n = ∑ i, a i * X.S.ents um.2 (at' i) :=
    fun {I} _ at' a => ldRng_placed I X.S.Ent E at' a (X.S.ents um.2)
  -- the tensor part
  have e1 : X.bt.ten (X.pG z) (X.pPt z) (X.msg um) =
      z.eps * X.bt.ten
          (fun r =>
            ∑ q, X.bt.chi z q * Alg.eqPt (X.bt.pt z.st.1 q) (X.bt.outPt z) * X.bt.g z.st.1 q r)
          (X.bt.outPt z) (X.msg um) := by
    have a1 : X.pG z =
        fun r =>
          ∑ q, (z.eps * (X.bt.chi z q * Alg.eqPt (X.bt.pt z.st.1 q) (X.bt.outPt z))) *
              X.bt.g z.st.1 q r := by
      funext r
      unfold LdTenD.pG
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    unfold LdTenD.pPt
    rw [a1, BattPar.ten_comb, BattPar.ten_comb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  -- the mask part
  have e2 : ∑ j, (Sum.elim (fun _ => 0) (placed X.pAt (X.pMf z)) : X.bt.J → E) j * X.msg um j =
      ∑ i, hSl (X.bt.par.vars z.st) (X.bt.par.hp z.st z.pt) i *
          X.msg um (X.bt.wAt (pIx X.bt.fmt (pdPlains E X.bt.n X.bt.k) i)) +
        z.eps * (∏ i, X.bt.outPt z i) *
          ∑ q, X.bt.chi z q * ∑ j, X.bt.slM q z.st.1 j * X.msg um j := by
    rw [hs, hp, Fintype.sum_sum_type]
    congr 1
    have a2 : ∀ q, ∑ j, X.bt.slM q z.st.1 j * X.msg um j =
        ∑ a, X.mf (X.stOf z).2 q a * X.S.ents um.2 (X.μAt a) :=
      fun q => (hs _).trans (hp _ _)
    simp only [a2]
    show ∑ a, (z.eps * (∏ i, X.bt.outPt z i) * ∑ q, X.bt.chi z q * X.mf (X.stOf z).2 q a) *
        X.S.ents um.2 (X.μAt a) = _
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => by ring
  rw [e1, e2]
  unfold LdTenD.pTg
  constructor <;> intro h <;> linear_combination h

end Cb
