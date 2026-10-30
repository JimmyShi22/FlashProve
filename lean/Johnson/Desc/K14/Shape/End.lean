-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Shape/End.lean: the shared chain's shape (Johnson/Desc/K14/Shape/Lin.lean): WHAT
STANDS AT EACH BORDER UP TO THE ONE BEHIND "SPLIT", AS A TERM WITH CODE: the updates (Run.lean:
updS) one behind the other, from a first shape. Definitions with code, and three laws.

What for. The test at the border 9 (Facts.lean: factsB) says less than the next sub-protocol of the
chain asks. What a proximity test asks of the structure in front of it sets that structure beside
THE TEST's OWN PLAN (its stages' numbers and codes, the declared trees' numbers and widths, the
count of roots): no law here gives that from this kind's plan; it is left to an evaluation at a
written plan. For an evaluation the shape in front must be a term with code.

Main names:
  upTo                **the shape at the border n, from the shape at the border 0**: a total
                      function. At 0 and at 1 it is one shape (the update at 0 changes nothing);
                      from 10 on it stays what it is at 9, and that is no law on the chain
  endAt               **the shape behind "SPLIT"**: THAT IS A NAME FOR A TERM: upTo at 9, from the
                      first state's shape; of the key it reads the sizes. No law here says that the
                      state of a run behind "SPLIT" has this shape (below)
  facts_upTo          under PlanFacts and the two sendings' test on the plan: at every border from 1
                      to 9 the closed form passes that border's test, where the first shape passes
                      the test at 1. By the law on shapes (Up.lean: facts_up)
  upTo_step           where what goes out with o_u can be said and the plan has two codes: a state
                      whose shape is the closed form at b, and a step of the sub-protocol number b
                      that returns: the shape behind is the closed form at b + 1; b = 1 to 8, ONE
                      STEP AT A TIME. By Run.lean's stepCarries
  frontAt             all nineteen clauses of the front of a proximity test
                      (Johnson/Desc/K12/Front.lean: frontL: the library's own list), AT THE STATE
                      THAT lift MAKES OF A SHAPE (Up.lean): a Bool with code
  FrontReads, front_of_shape   FrontReads: frontL reads a state through the core's shape alone: a
                      definition: a premise's form. Under it frontL says at every state what frontAt
                      says at the state's shape. THE PREMISE IS SHOWN IN NO FILE THAT THIS FILE
                      STANDS OVER: its proof wants the proximity test's own laws on shapes, over
                      which this file does not stand; of that kind's names it names frontL
                      (Front.lean) alone

What is assumed, as premises: at facts_upTo: PlanFacts, the two sendings' test on the plan, Eight P
(Run.lean's head spells them out); at upTo_step: what goes out with o_u; two codes; Eight P. sentU
is a free letter in upTo and endAt: they are the chain's only where withU P.S = some sentU.

What is not claimed. THAT THE STATE OF ANY RUN BEHIND "SPLIT" HAS THE SHAPE endAt: upTo_step is one
step; the eight steps are joined in no theorem here; of the front sub-protocol (number 0) no law is
here: that it leaves the state is a reading (Run.lean: updS); the one test at a whole run is an
evaluation at a small written example (EndToy.lean), which proves nothing. That frontAt is true at
any plan: evaluations at three written plans stand in EndToy.lean. Anything at the IOP's own type of
claims: the steps of upTo_step are those of Eight P, at the kind's own type (Run.lean's head says
how a caller carries them across). Anything at the sub-protocols behind the eight. Nothing on
soundness, on completeness or on hiding.
-/
import Johnson.Desc.K14.Shape.Up
import Johnson.Desc.K12.Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Shape
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (OpenedColumn)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Ground.Sh (coreSh)
open VerifiableInference.Desc.K1 (planOkOwn)
open VerifiableInference.Desc.K12 (frontL)
open Desc.K14.Law (parU parO)
open Desc.K14.Honest (Eight PlanFacts)

/-- **THE SHAPE AT THE BORDER n, FROM THE SHAPE a AT THE BORDER 0**: the updates of the
sub-protocols 0 to n - 1, one behind the other: a function with code of the plan, of sentU (a free
letter: the chain's only where withU P.S = some sentU) and of a. A total function. The update at 0
changes nothing, so upTo at 0 and at 1 are one shape: that is why facts_upTo asks the test AT 1 of
the shape a. From 10 on upTo stays what it is at 9: the update from 9 on changes nothing, AND THAT
IS NO LAW: the sub-protocols there change the state (Run.lean: updS). -/
def upTo (P : P14) (sentU : Array OracleNotice) : Nat → Sh2 → Sh2
  | 0, a => a
  | n + 1, a => updS P sentU n (upTo P sentU n a)

/-- **THE SHAPE BEHIND "SPLIT"**: a name for a term: upTo at 9, from the first state's shape. Of the
key it reads the sizes. sentU is a free letter. No theorem here says that the state of a run behind
"SPLIT" has this shape: upTo_step goes one step at a time. -/
def endAt (P : P14) (sentU : Array OracleNotice) (key : TableKey) : Sh2 :=
  upTo P sentU 9 (sh2 (first P.codes key))

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-- **At every border up to 9 it passes that border's test**, where a passes the first (h: the test
at 1), under PlanFacts (hP) and the two sendings' test on the plan (hBU, hBO), at the eight of B
(Eight P). -/
theorem facts_upTo (hP : PlanFacts P.par P.codes sentU layO)
    (hBU : planOkOwn (parU P sentU) = true) (hBO : planOkOwn (parO P) = true) (B : Eight P)
    (a : Sh2) (h : factsB P 1 a = true) :
    ∀ n, n ≤ 8 → factsB P (n + 1) (upTo P sentU (n + 1) a) = true
  | 0, _ => h
  | n + 1, hn =>
    facts_up hP hBU hBO B (upTo P sentU (n + 1) a) (n + 1) (by omega) hn
      (facts_upTo hP hBU hBO B a h n (by omega))

/-- **A state whose shape is the closed form at b, and a step of the sub-protocol number b that
returns: the shape behind is the closed form at b + 1**, b = 1 to 8, where what goes out with o_u
can be said (hU: withU P.S = some sentU), the plan has two codes (hS) and the kind's text makes its
eight (B: Eight P). a is any shape. One step at a time: the eight are not joined. -/
theorem upTo_step (hU : withU P.S = some sentU) (hS : P.S.sharedSplitNeeded = true) (B : Eight P)
    (ft : Nat) (a : Sh2) (d d' : St) (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) :
    (sh2 d = upTo P sentU 1 a → B.b1.step ft d rs c = .ok (d', n) → sh2 d' = upTo P sentU 2 a) ∧
    (sh2 d = upTo P sentU 2 a → B.b2.step ft d rs c = .ok (d', n) → sh2 d' = upTo P sentU 3 a) ∧
    (sh2 d = upTo P sentU 3 a → B.b3.step ft d rs c = .ok (d', n) → sh2 d' = upTo P sentU 4 a) ∧
    (sh2 d = upTo P sentU 4 a → B.b4.step ft d rs c = .ok (d', n) → sh2 d' = upTo P sentU 5 a) ∧
    (sh2 d = upTo P sentU 5 a → B.b5.step ft d rs c = .ok (d', n) → sh2 d' = upTo P sentU 6 a) ∧
    (sh2 d = upTo P sentU 6 a → B.b6.step ft d rs c = .ok (d', n) → sh2 d' = upTo P sentU 7 a) ∧
    (sh2 d = upTo P sentU 7 a → B.b7.step ft d rs c = .ok (d', n) → sh2 d' = upTo P sentU 8 a) ∧
    (sh2 d = upTo P sentU 8 a → B.b8.step ft d rs c = .ok (d', n) → sh2 d' = upTo P sentU 9 a) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := stepCarries hU hS B ft d d' rs c n
  exact ⟨fun e h => (c1 h).trans (by rw [e]; rfl), fun e h => (c2 h).trans (by rw [e]; rfl),
    fun e h => (c3 h).trans (by rw [e]; rfl), fun e h => (c4 h).trans (by rw [e]; rfl),
    fun e h => (c5 h).trans (by rw [e]; rfl), fun e h => (c6 h).trans (by rw [e]; rfl),
    fun e h => (c7 h).trans (by rw [e]; rfl), fun e h => (c8 h).trans (by rw [e]; rfl)⟩

/-- **All nineteen clauses of the front of a proximity test, at a shape**: the library's own list,
at the state that lift makes of the shape: with code. g: the group under test. mask: the first
fold's mask, if it has come. -/
def frontAt (e : Sh2) (g : Nat) (mask : Option Nat) : Bool :=
  ok (frontL (lift e).st (lift e).book g mask)

/-- The front's list reads a state through the core's shape alone: a premise's form. It is a
definition: nothing is claimed of it here. -/
def FrontReads : Prop :=
  ∀ (S S' : Statement) (B B' : TreeBook) (r r' g : Nat) (mask : Option Nat),
    coreSh ⟨S, B, r⟩ = coreSh ⟨S', B', r'⟩ → frontL S B g mask = frontL S' B' g mask

/-- **Under that premise, at every state the front's clauses say what frontAt says there.** -/
theorem front_of_shape (hR : FrontReads) (d : St) (g : Nat) (mask : Option Nat) :
    ok (frontL d.st d.book g mask) = frontAt (sh2 d) g mask := by
  unfold frontAt
  rw [hR d.st (lift (sh2 d)).st d.book (lift (sh2 d)).book d.roots (lift (sh2 d)).roots g mask
    (congrArg Sh2.core (sh2_lift (sh2 d))).symm]

end Desc.K14.Shape

#print axioms Desc.K14.Shape.facts_upTo
#print axioms Desc.K14.Shape.upTo_step
#print axioms Desc.K14.Shape.front_of_shape
