-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Start.lean: the form from which the batched sumcheck of a layers' sub-proof starts, as
a target and an incoming form, and the law Mid.link (Cb/Pv/Lay/OwnAll.lean) from it.

Main names:
  `overTg`, `overInc`: for any sumcheck Y and output o: the public part and the coefficients of
    overAt Y o (Cb/Pv/Lay/Over.lean) as an affine form in the entries, written as overAt is: the
    last value and the hiding polynomial's form divided by the drawn coefficient (0⁻¹ = 0).
  `St4`: the states of the batched sumcheck: the lookup's point; the public part and the form of
    what the lookup's end leaves for the calls' joint extension; the sent sum of the terms; the
    output of the terms' sumcheck; the element drawn.
  `startTg`, `startInc`: target and incoming form.
  `overAt_form`: overAt Y o m = overTg Y o - the sum of overInc Y o j times m j, at every o, the
    drawn coefficient 0 among them.
  `start_form`: the target less the incoming form's value is (what the lookup's end leaves - the
    affine side - the hidden sum of the terms) + β overAt.
  `link_of`: so, if the sum over the cube is the matrix products' side plus β times the kept part,
    the sum claim at that target and form gives: (the join's gap at the hidden sum) + β (keptAt -
    overAt) = 0.

Limits: that the programs' start form is this one is not said here. Nothing is said on an honest
prover or on hiding.


-/
import Cb.Pv.Lay.Over
import Cb.Ld.LdPscProofsIor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.At
open Iop Prob Cb IOR Finset TWhole

noncomputable section

variable {E : Type} [Field E]

section Over
variable (Y : PscPar E) [DecidableEq Y.J]

/-- The public part of overAt. -/
def overTg (o : Y.Out) : E := o.fin / o.eps - Y.S0 o.st (Y.hp o.st o.pt) o.vals

/-- The coefficient of entry j in what overAt takes off its public part. -/
def overInc (o : Y.Out) (j : Y.J) : E :=
  (∑ i, if Y.wAt (pIx Y.fmt (Y.dat o.st) i) = j then hSl (Y.vars o.st) (Y.hp o.st o.pt) i else 0) /
      o.eps +
    hPsi (Y.vars o.st) (Y.hp o.st o.pt) * Y.slS o.st j

/-- **overAt is an affine form in the entries**, at every output. -/
theorem overAt_form (o : Y.Out) (m : Y.J → E) :
    overAt Y o m = overTg Y o - ∑ j, overInc Y o j * m j := by
  have h1 : hU (Y.vars o.st) (Y.W o.st m) (Y.hp o.st o.pt) =
      ∑ j, (∑ i, if Y.wAt (pIx Y.fmt (Y.dat o.st) i) = j then hSl (Y.vars o.st) (Y.hp o.st o.pt) i
          else 0) * m j := by
    rw [hide_form E E]
    simp only [Finset.sum_mul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  have h2 : ∑ j, overInc Y o j * m j =
      (∑ j, (∑ i, if Y.wAt (pIx Y.fmt (Y.dat o.st) i) = j then
          hSl (Y.vars o.st) (Y.hp o.st o.pt) i else 0) * m j) / o.eps +
        hPsi (Y.vars o.st) (Y.hp o.st o.pt) * ∑ j, Y.slS o.st j * m j := by
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold overInc
    ring
  unfold overAt overTg PscPar.inc
  rw [h2, ← h1]
  ring

end Over

/-- The states of the batched sumcheck. O: the outputs of the terms' sumcheck. -/
structure St4 (E J O : Type) where
  /-- the lookup's point -/
  z : ℕ → E
  /-- what the lookup's end leaves for the calls' joint extension: its public part, its form -/
  kTg : E
  kInc : J → E
  /-- the sent sum of the terms -/
  s : E
  /-- the output of the terms' sumcheck -/
  o3 : O
  /-- the element drawn -/
  β : E

section Start
variable (Y : PscPar E) [DecidableEq Y.J] (lnTg : (ℕ → E) → E) (lnInc : (ℕ → E) → Y.J → E)
  (rT : Y.J)

/-- The target of the batched sumcheck. -/
def startTg (st : St4 E Y.J Y.Out) : E :=
  st.kTg - lnTg st.z - st.s + st.β * overTg Y st.o3

/-- Its incoming form. -/
def startInc (st : St4 E Y.J Y.Out) (j : Y.J) : E :=
  st.kInc j + lnInc st.z j - (if j = rT then 1 else 0) + st.β * overInc Y st.o3 j

/-- **The start form.** -/
theorem start_form (st : St4 E Y.J Y.Out) (m : Y.J → E) :
    startTg Y lnTg st - ∑ j, startInc Y lnInc rT st j * m j =
      (st.kTg - ∑ j, st.kInc j * m j) - (lnTg st.z + ∑ j, lnInc st.z j * m j) - (st.s - m rT) +
        st.β * overAt Y st.o3 m := by
  have h : ∑ j, startInc Y lnInc rT st j * m j =
      ∑ j, st.kInc j * m j + ∑ j, lnInc st.z j * m j - m rT +
        st.β * ∑ j, overInc Y st.o3 j * m j := by
    have e : ∑ j, (if j = rT then (1 : E) else 0) * m j = m rT := by
      simp
    rw [← e, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold startInc
    ring
  rw [h, overAt_form]
  unfold startTg
  ring

/-- **The law link, from the panels' identity.** cube: the sum over the cube; acc, line: the two
sides of the join. -/
theorem link_of (st : St4 E Y.J Y.Out) (m : Y.J → E) (cube acc line : E)
    (hl : line = lnTg st.z + ∑ j, lnInc st.z j * m j)
    (hc : cube = acc + st.β * keptAt Y st.o3 m)
    (hs : cube + ∑ j, startInc Y lnInc rT st j * m j = startTg Y lnTg st) :
    (acc + line + (st.s - m rT) - (st.kTg - ∑ j, st.kInc j * m j)) +
      st.β * (keptAt Y st.o3 m - overAt Y st.o3 m) = 0 := by
  have h := start_form Y lnTg lnInc rT st m
  linear_combination hs - hc + hl + h

end Start
end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.overAt_form
#print axioms Cb.Pv.Lay.At.start_form
#print axioms Cb.Pv.Lay.At.link_of
