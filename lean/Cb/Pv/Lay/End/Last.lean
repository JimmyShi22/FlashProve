-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/Last.lean: what the chain of a layers' sub-proof's own rounds owes at its end, written
out clause by clause.

Cb/Pv/Lay/Own.lean has the chain at letters (LayTail, LayOwn), and Cb/Pv/Att/Chain.lean defines by
recursion what a chain claims at its end (Ch.Last): the claim Dn of the first statement, what is
claimed of every tuple of scalars sent, and what is owed of every sumcheck's output claims. The last
statement of the chain is a nested tuple that holds all that was sent, drawn and put out. This file
names the statements inside it and writes the claim as a record.

Main definitions: LayTail.y7 down to LayTail.xL: the statements inside a last statement;
LayTail.Bill: the clauses. Main theorems: LayTail.last_iff, LayOwn.last_iff, LayOwnFirst.last_iff:
Ch.Last is the record.

Limits: a rewriting of a definition. Nothing is said on whether a clause holds.


-/
import Cb.Pv.Lay.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Cb.Pv.Att

variable {E : Type} [Field E] [Fintype E] {M X : Type}

namespace LayTail
variable (T : LayTail E M X)

/-- The statement before the merge of the weight claims. -/
def y7 (e : T.s7.Nx) : ((T.s6.Nx × E) × (Fin T.nW → E)) × E := e.1.1
/-- The statement before the weight claims' round. -/
def xW (e : T.s7.Nx) : T.s6.Nx × E := (T.y7 e).1.1
/-- The statement behind the routed gated products. -/
def b6 (e : T.s7.Nx) : T.s6.Nx := (T.xW e).1
/-- The statement behind the gated products. -/
def b5 (e : T.s7.Nx) : T.s5.Nx := (T.b6 e).1.1.1.1
/-- The statement behind the batched inner products. -/
def b4 (e : T.s7.Nx) : T.s4.Nx := (T.b5 e).1.1
/-- The statement behind the terms. -/
def b3 (e : T.s7.Nx) : T.s3.Nx := (T.b4 e).1.1.1
/-- The statement behind the products of the rows. -/
def b2 (e : T.s7.Nx) : T.s2.Nx := (T.b3 e).1.1
/-- The statement before the products' scalars. -/
def xP (e : T.s7.Nx) : T.s1.Nx × E := (T.b2 e).1.1.1.1
/-- The statement behind the sums of squares. -/
def b1 (e : T.s7.Nx) : T.s1.Nx := (T.xP e).1
/-- The first statement. -/
def xL (e : T.s7.Nx) : X := (T.b1 e).1.1.1.1.1

/-- What the chain from the limbs' scalars on claims at its end. -/
structure Bill (Dn : X → M → Prop) (e : T.s7.Nx) (m : M) : Prop where
  dn : Dn (T.xL e) m
  lL : T.lL (T.xL e) (T.b1 e).1.1.1.1.2 m
  c1 : T.s1.Lc (T.b1 e).1.1 (T.b1 e).1.2 m
  o1 : T.ow1 (T.b1 e) m
  lP : T.lP (T.xP e) (T.b2 e).1.1.1.2 m
  c2 : T.s2.Lc (T.b2 e).1.1 (T.b2 e).1.2 m
  o2 : T.ow2 (T.b2 e) m
  c3 : T.s3.Lc (T.b3 e).1.1 (T.b3 e).1.2 m
  o3 : T.ow3 (T.b3 e) m
  c4 : T.s4.Lc (T.b4 e).1.1 (T.b4 e).1.2 m
  o4 : T.ow4 (T.b4 e) m
  c5 : T.s5.Lc (T.b5 e).1.1 (T.b5 e).1.2 m
  o5 : T.ow5 (T.b5 e) m
  c6 : T.s6.Lc (T.b6 e).1.1 (T.b6 e).1.2 m
  o6 : T.ow6 (T.b6 e) m
  lW : T.lW (T.xW e) (T.y7 e).1.2 m
  c7 : T.s7.Lc (T.y7 e) e.1.2 m
  o7 : T.s7.Out e m

/-- What the chain claims at its end is the record. -/
theorem last_iff (Dn : X → M → Prop) (e : T.s7.Nx) (m : M) :
    T.ch.Last Dn e m ↔ T.Bill Dn e m := by
  constructor
  · intro h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hlL⟩, hc1, ho1⟩, hlP⟩, hc2, ho2⟩, hc3, ho3⟩, hc4, ho4⟩, hc5, ho5⟩, hc6,
      ho6⟩, hlW⟩, hc7, ho7⟩ := h
    exact ⟨hD, hlL, hc1, ho1, hlP, hc2, ho2, hc3, ho3, hc4, ho4, hc5, ho5, hc6, ho6, hlW, hc7, ho7⟩
  · intro B
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨B.dn, B.lL⟩, B.c1, B.o1⟩, B.lP⟩, B.c2, B.o2⟩, B.c3, B.o3⟩, B.c4, B.o4⟩, B.c5,
      B.o5⟩, B.c6, B.o6⟩, B.lW⟩, B.c7, B.o7⟩

end LayTail

/-- The same with the token point before the stages: the claim of the first statement is read at the
statement before the point. -/
theorem LayOwn.last_iff (A : LayOwn E M X) (Dn : X → M → Prop) (e : A.tail.s7.Nx) (m : M) :
    A.ch.Last Dn e m ↔ A.tail.Bill (fun b m => Dn b.1 m) e m :=
  A.tail.last_iff (fun b m => Dn b.1 m) e m

/-- The same for the first sub-proof, with its three points before the stages. -/
theorem LayOwnFirst.last_iff (A : LayOwnFirst E M X) (Dn : X → M → Prop) (e : A.tail.s7.Nx)
    (m : M) : A.ch.Last Dn e m ↔ A.tail.Bill (fun b m => Dn b.1.1.1 m) e m :=
  A.tail.last_iff (fun b m => Dn b.1.1.1 m) e m

end Cb.Pv.Lay
