-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Weights.lean: the last stretch of a layers' sub-proof's own rounds: the claims on the
committed weights are combined under the powers of one element and merged by one sumcheck.

Before the stretch n claims are open. Claim a says
    (sum over the corners x of the cube of fa a (x)) + m (nm a) * be a = sh a:
the weights of a unit, under given factors, sum to a value that was sent masked: nm a is the name of
its mask entry, be a the mask's factor, sh a the scalar that was sent. The verifier draws one
element; its powers, from the power 0 on, are the claims' coefficients. Then comes the merge
(Cb/Pv/Lay/Merge.lean).

This file has the stretch with an empty message in the round of the draw: the form of every group of
layers but the first. (In the first group one more value is sent in that round.)

Main names:
  `WeightsL`: the parameters. `WeightsL.Cl`: a claim.
  `WeightsL.L`: the merge's parameters behind the draw: the summand, the incoming form and the
    target are the claims' combinations.
  `WeightsL.link`: the combined claim is the merge's input claim.
  `WeightsL.blk V`, `WeightsL.knowAt`, `WeightsL.know`: the reduction; its knowledge soundness for
    each fixed tuple of messages, from "what rides, and all n claims" to "what rides, one row on
    names, the row on the end value".
  `WeightsL.errs`: its errors, round by round: n - 1; 1; 2 for each column bit; 1; 0.

Limits: the field `deg` (each summand has degree at most 2 in each variable) is to be paid by
whoever fills the record. For the rest as in Cb/Pv/Lay/Merge.lean and Cb/Pv/Lay/Draws.lean.

-/
import Cb.Pv.Lay.Merge
import Cb.Pv.Lay.Draws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole

noncomputable section

/-- The parameters of the stretch. -/
structure WeightsL (E : Type) [Field E] [Fintype E] where
  J : Type
  [finJ : Fintype J]
  /-- the number of column bits -/
  k : ℕ
  /-- the number of claims -/
  n : ℕ
  St : Type
  /-- a claim's summand -/
  fa : Fin n → St → (J → E) → (Fin k → E) → E
  deg : ∀ a st m, Alg.DegLE (fun _ : Fin k => 2) (fa a st m)
  /-- the name of a claim's mask entry, its factor, the scalar that was sent -/
  nm : Fin n → J
  be : Fin n → St → E
  sh : Fin n → St → E
  wAt : PIdx (ldPartFmt E k (fun _ => 2) ++ [pDummy E 1]) → J
  cAt : J
  Rd : St → (J → E) → Prop

attribute [instance] WeightsL.finJ

variable {E : Type} [Field E] [Fintype E]

namespace WeightsL
variable (G : WeightsL E)

/-- the value of claim a, with its mask -/
def val (st : G.St) (m : G.J → E) (a : Fin G.n) : E :=
  ∑ b : Fin G.k → Bool, G.fa a st m (Alg.corner b) + m (G.nm a) * G.be a st

/-- claim a -/
def Cl (st : G.St) (m : G.J → E) (a : Fin G.n) : Prop := G.val st m a = G.sh a st

open Classical in
/-- the merge's parameters behind the draw -/
@[reducible] def L : MergeL E where
  J := G.J
  k := G.k
  St := G.St × E
  f := fun x m z => ∑ a : Fin G.n, x.2 ^ (a : ℕ) * G.fa a x.1 m z
  deg := fun x m => Alg.DegLE.sum Finset.univ fun a _ => (G.deg a x.1 m).const_mul (x.2 ^ (a : ℕ))
  inc := fun x j => ∑ a : Fin G.n, if j = G.nm a then x.2 ^ (a : ℕ) * G.be a x.1 else 0
  tg := fun x => ∑ a : Fin G.n, x.2 ^ (a : ℕ) * G.sh a x.1
  wAt := G.wAt
  cAt := G.cAt
  Rd := fun x m => G.Rd x.1 m

theorem inc_sum (x : G.St × E) (m : G.J → E) :
    ∑ j, G.L.inc x j * m j = ∑ a : Fin G.n, x.2 ^ (a : ℕ) * (m (G.nm a) * G.be a x.1) := by
  classical
  show ∑ j, (∑ a : Fin G.n, if j = G.nm a then x.2 ^ (a : ℕ) * G.be a x.1 else 0) * m j = _
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (G.nm a)]
  · rw [if_pos rfl]
    ring
  · intro j _ hj
    rw [if_neg hj, zero_mul]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

/-- The combined claim is the merge's input claim. -/
theorem link (x : G.St × E) (m : G.J → E) :
    G.L.Sg x m ↔
      ∑ a, (Evader.powers E G.n).ze x.2 a * G.val x.1 m a = ∑ a, (Evader.powers E G.n).ze x.2 a *
          G.sh a x.1 := by
  unfold MergeL.Sg
  rw [G.inc_sum]
  have h : ∑ b : Fin G.k → Bool, G.L.f x m (Alg.corner b) =
      ∑ a : Fin G.n, x.2 ^ (a : ℕ) * ∑ b : Fin G.k → Bool, G.fa a x.1 m (Alg.corner b) := by
    show ∑ b : Fin G.k → Bool, ∑ a : Fin G.n, x.2 ^ (a : ℕ) * G.fa a x.1 m (Alg.corner b) = _
    rw [sum_comm]
    exact sum_congr rfl fun a _ => (mul_sum _ _ _).symm
  rw [h, ← sum_add_distrib]
  have e : ∀ a : Fin G.n, x.2 ^ (a : ℕ) * ∑ b : Fin G.k → Bool, G.fa a x.1 m (Alg.corner b) +
      x.2 ^ (a : ℕ) * (m (G.nm a) * G.be a x.1) = (Evader.powers E G.n).ze x.2 a * G.val x.1 m a :=
    fun a => (mul_add _ _ _).symm
  simp only [e]

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc G.St Ex (M × Wp)) (msg : M → G.J → E)

/-- what rides before the draw -/
@[reducible] def A0 : Rels Kc G.St Ex (M × Wp) :=
  ⟨fun st y w => R0.rel st y w ∧ G.Rd st (msg w.1), fun a w => R0.relR a w ∧ G.Rd a.1 (msg w.1),
    R0.on, R0.core⟩

/-- the base, read at the old state -/
@[reducible] def R1 : Rels Kc (G.St × E) Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x.1 y w, fun a w => R0.relR (a.1.1, a.2) w, fun a => R0.on
      (a.1.1, a.2), R0.core⟩

/-- the joint before the stretch: what rides, and all claims -/
@[reducible] def relIn : Rels Kc G.St Ex (M × Wp) := combIn (G.A0 R0 msg) msg G.val
    fun st a => G.sh a st

variable (V : ShortK G.L.T.par Ex)

/-- The reduction. -/
def blk : IOR G.St Ex G.L.T.par.Out Ex := (comb (Evader.powers E G.n) G.St Ex).seq (G.L.blk V)

/-- its errors -/
def eps : Err (G.blk V).shape :=
  Err.app (s := (comb (Evader.powers E G.n) G.St Ex).shape)
    (Nums.draw Kc E (fun (st : G.St) (β : E) => (st, β)) Ex (G.n - 1)).err V.ε

theorem knowAt :
    KnowAt (G.blk V) (G.relIn R0 msg) (G.L.relOut (G.R1 R0) msg) (fun _ _ _ wp => wp) (G.eps
        (Kc := Kc) V) := by
  have h1 := comb_knowAt (Evader.powers E G.n) (G.A0 R0 msg) msg G.val (fun st a => G.sh a st)
      (ok_powers E G.n)
  have h2 := G.L.knowAt (G.R1 R0) msg V
  refine knowAt_seq h1 (knowAt_mono h2 (fun _ h => h) (fun a w _ h => ?_)
      (fun _ _ _ h => h) fun _ h => h)
  exact ⟨h.1, (G.link a.1 _).1 h.2⟩

theorem know (m : M) :
    (G.blk V).red.Know (G.relIn R0 msg).on (fun a wp => (G.relIn R0 msg).relR a (m, wp))
      (fun b wp => (G.L.relOut (G.R1 R0) msg).relR b (m, wp)) (fun _ _ wp => wp)
          (G.eps (Kc := Kc) V) :=
  (G.knowAt R0 msg V).know m

theorem errs : TWhole.errList (G.eps (Kc := Kc) V) = (G.n - 1) :: 1 ::
    (List.replicate G.k 2 ++ [1, 0]) := by
  refine (errList_app (Nums.draw Kc E (fun (st : G.St) (β : E) => (st, β)) Ex (G.n
      - 1)).err V.ε).trans ?_
  rw [errList_draw, G.L.errs V]
  rfl

end Block

end WeightsL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.WeightsL.link
#print axioms Cb.Pv.Lay.WeightsL.knowAt
#print axioms Cb.Pv.Lay.WeightsL.errs
