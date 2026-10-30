-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/Parts.lean: a maker of last statements of the chain of a layers' sub-proof's own
rounds, at any letters of the chain.

A last statement of the chain is a nest of pairs: the first statement, and stage by stage the sent
scalars, the drawn elements and each sumcheck's output. Cb/Pv/Lay/End/Last.lean reads its parts off
it. This file goes the other way. A record holds the parts side by side, the statement is made from
the record, and each reading of Cb/Pv/Lay/End/Last.lean gives back the record's part. All of it is
shown at any letters T, where nothing has to be unfolded. At a value of T one rewrites by these
equations.

Main names:
  `Parts T`: the parts of a last statement.
  `Parts.b1` .. `Parts.b6`, `Parts.e`: the statements behind the stages; the last statement.
  `b1_e` .. `b6_e`, `xL_e`, `xP_e`, `xW_e`, `y7_e`: the readings give back the parts.
  `bill_e`: what the chain owes at the statement made from a record, clause by clause in the
  record's parts.
Limits: no letters are given a value here, and no clause is shown.


-/
import Cb.Pv.Lay.End.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.LayTail

variable {E : Type} [Field E] [Fintype E] {M X : Type}

/-- The parts of a last statement of the chain, in the order in which they come up. -/
structure Parts (T : LayTail E M X) where
  /-- the first statement -/
  x : X
  /-- the limbs' scalars; the element drawn behind them; the point of the join of the norms -/
  sL : Fin T.nL → E
  cN : E
  pN : Fin T.gN → E
  /-- the sums of squares: further scalars, output; the element drawn behind it -/
  r1 : Fin T.s1.n → E
  o1 : T.s1.L.T.par.Out
  d1 : E
  /-- the products' scalars; the element drawn behind them -/
  sP : Fin T.nP → E
  cP : E
  /-- the products of the rows; the terms -/
  r2 : Fin T.s2.n → E
  o2 : T.s2.L.T.par.Out
  r3 : Fin T.s3.n → E
  o3 : T.s3.L.T.par.Out
  /-- the element that combines; the batched inner products -/
  c4 : E
  r4 : Fin T.s4.n → E
  o4 : T.s4.L.T.par.Out
  /-- the gated products; the element drawn behind them; the point of the join of the layers with
  routed experts -/
  r5 : Fin T.s5.n → E
  o5 : T.s5.L.T.par.Out
  d5 : E
  pR : Fin T.gR → E
  /-- the routed gated products; the element drawn behind them -/
  r6 : Fin T.s6.n → E
  o6 : T.s6.L.T.par.Out
  d6 : E
  /-- the weight claims' round: scalars; the element drawn behind them; the merge -/
  sW : Fin T.nW → E
  cW : E
  r7 : Fin T.s7.n → E
  o7 : T.s7.L.T.par.Out

namespace Parts
variable {T : LayTail E M X} (p : Parts T)

/-- The statement behind the sums of squares. -/
def b1 : T.s1.Nx := (((((p.x, p.sL), p.cN), p.pN), p.r1), p.o1)
/-- The statement behind the products of the rows. -/
def b2 : T.s2.Nx := (((((p.b1, p.d1), p.sP), p.cP), p.r2), p.o2)
/-- The statement behind the terms. -/
def b3 : T.s3.Nx := ((p.b2, p.r3), p.o3)
/-- The statement behind the batched inner products. -/
def b4 : T.s4.Nx := (((p.b3, p.c4), p.r4), p.o4)
/-- The statement behind the gated products. -/
def b5 : T.s5.Nx := ((p.b4, p.r5), p.o5)
/-- The statement behind the routed gated products. -/
def b6 : T.s6.Nx := ((((p.b5, p.d5), p.pR), p.r6), p.o6)
/-- The last statement. -/
def e : T.s7.Nx := (((((p.b6, p.d6), p.sW), p.cW), p.r7), p.o7)

theorem y7_e : T.y7 p.e = (((p.b6, p.d6), p.sW), p.cW) := rfl
theorem xW_e : T.xW p.e = (p.b6, p.d6) := rfl
theorem b6_e : T.b6 p.e = p.b6 := rfl
theorem b5_e : T.b5 p.e = p.b5 := rfl
theorem b4_e : T.b4 p.e = p.b4 := rfl
theorem b3_e : T.b3 p.e = p.b3 := rfl
theorem b2_e : T.b2 p.e = p.b2 := rfl
theorem xP_e : T.xP p.e = (p.b1, p.d1) := rfl
theorem b1_e : T.b1 p.e = p.b1 := rfl
theorem xL_e : T.xL p.e = p.x := rfl

/-- What the chain owes at the statement made from the record, in the record's parts. -/
theorem bill_e (Dn : X → M → Prop) (m : M) :
    T.Bill Dn p.e m ↔
      Dn p.x m ∧ T.lL p.x p.sL m ∧ T.s1.Lc (((p.x, p.sL), p.cN), p.pN) p.r1 m ∧ T.ow1 p.b1 m ∧
      T.lP (p.b1, p.d1) p.sP m ∧ T.s2.Lc (((p.b1, p.d1), p.sP), p.cP) p.r2 m ∧ T.ow2 p.b2 m ∧
      T.s3.Lc p.b2 p.r3 m ∧ T.ow3 p.b3 m ∧ T.s4.Lc (p.b3, p.c4) p.r4 m ∧ T.ow4 p.b4 m ∧
      T.s5.Lc p.b4 p.r5 m ∧ T.ow5 p.b5 m ∧ T.s6.Lc ((p.b5, p.d5), p.pR) p.r6 m ∧ T.ow6 p.b6 m ∧
      T.lW (p.b6, p.d6) p.sW m ∧ T.s7.Lc (((p.b6, p.d6), p.sW), p.cW) p.r7 m ∧ T.s7.Out p.e m :=
  ⟨fun B => ⟨B.dn, B.lL, B.c1, B.o1, B.lP, B.c2, B.o2, B.c3, B.o3, B.c4, B.o4, B.c5, B.o5, B.c6,
    B.o6, B.lW, B.c7, B.o7⟩,
   fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ =>
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩⟩

end Parts

end Cb.Pv.Lay.LayTail

#print axioms Cb.Pv.Lay.LayTail.Parts.bill_e
