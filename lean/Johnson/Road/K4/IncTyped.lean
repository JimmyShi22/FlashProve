-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/IncTyped.lean: THE INCOMING MASKS' FORM OF SIX OF THE SEVEN SUMCHECKS OF THE CHAIN
OF A LAYERS' SUB-PROOF's OWN ROUNDS, AT THE LIBRARY's VALUE (`FullPar.own`; a sub-proof that is not
the first), WRITTEN OUT: `PscPar.inc st m` (Cb/Ld/LdPsc.lean) as a formula in the state's parts and
in the entries of m under the value's names of mask entries. Six statements. The twin, for the
masks, of Johnson/Road/K4/ClaimsTyped.lean.

  `inc1` (the sums of squares): the formula of `cl1` with the entry under `mkS i s` in the place of
    the sent scalar (by `RoutedL.inc_sum`, `SquaresL.inci_sum`).
  `inc2`, `inc3` (the two token sumchecks): the one entry under `rP`, under `rT` (`TokL.inc_sum`).
  `inc5` (the gated products): the state's factor times the entry under the name of the gated
    products' end value.
  `inc6` (the routed experts' gated products): the formula of `cl6` with the factor times the entry.
  `inc7` (the merge): the formula of `cl7` with the entry times the factor (`WeightsL.inc_sum`).

Limits. The typed side alone: nothing here names a program's record.
-/
import Cb.Pv.Lay.At.OwnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)

/-- The sums of squares. -/
theorem inc1 (st : P.nr.sq.St1 × (Fin (P.D.lL + 1) → E)) (m : P.J → E) :
    P.own.toOwn.tail.s1.L.T.par.inc st m =
      ∑ i : Fin P.D.nNu, Blocks.eqN (P.D.lL + 1) 0 (Blocks.nat st.2) i.val *
        ((2⁻¹ : E) ^ lDd P.D * ∑ s : Fin 9, st.1.2 ^ (s : ℕ) * m (P.nr.sq.mkS i s)) :=
  (P.nr.sq.R.inc_sum st m).trans
    (Finset.sum_congr rfl fun i _ => congrArg _ (P.nr.sq.inci_sum i st.1 m))

/-- The products of the rows. -/
theorem inc2 (st : P.own.toOwn.tail.s2.L.T.par.St) (m : P.J → E) :
    P.own.toOwn.tail.s2.L.T.par.inc st m = m P.nr.rows.rJ :=
  P.nr.rows.tok.inc_sum st m

/-- The terms. -/
theorem inc3 (st : P.own.toOwn.tail.s3.L.T.par.St) (m : P.J → E) :
    P.own.toOwn.tail.s3.L.T.par.inc st m = m P.rT :=
  P.tp.tm.inc_sum st m

/-- The gated products. -/
theorem inc5 (st : St5 E P.D) (m : P.J → E) :
    P.own.toOwn.tail.s5.L.T.par.inc st m = st.be * m (P.cI (.inl (aH1 P.D))) := by
  classical
  show ∑ j, P.fp.gp.inc st j * m j = _
  unfold FootPar0.gp
  simp

/-- The routed experts' gated products. -/
theorem inc6 (st : St6 E P.D × (Fin (P.D.lL - 1) → E)) (m : P.J → E) :
    P.own.toOwn.tail.s6.L.T.par.inc st m =
      ∑ i : Fin P.D.ne, Blocks.eqN (P.D.lL - 1) 0 (Blocks.nat st.2) i.val *
        (st.1.be * m (P.cI (.inl (aH2 P.D i)))) := by
  classical
  refine (P.fp.rt.inc_sum st m).trans (Finset.sum_congr rfl fun i _ => congrArg _ ?_)
  show ∑ j, P.fp.rt.inci i st.1 j * m j = _
  unfold FootPar0.rt
  simp

/-- The merge. -/
theorem inc7 (st : P.wp0.wt.St × E) (m : P.J → E) :
    P.own.toOwn.tail.s7.L.T.par.inc st m =
      ∑ a : Fin P.wp0.wt.n, st.2 ^ (a : ℕ) * (m (P.wp0.wt.nm a) * P.wp0.wt.be a st.1) :=
  P.wp0.wt.inc_sum st m

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.inc1
#print axioms OnBytes.Road.K4.inc2
#print axioms OnBytes.Road.K4.inc3
#print axioms OnBytes.Road.K4.inc5
#print axioms OnBytes.Road.K4.inc6
#print axioms OnBytes.Road.K4.inc7
