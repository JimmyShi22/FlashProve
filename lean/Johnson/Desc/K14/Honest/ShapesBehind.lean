--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/ShapesBehind.lean: the book-keeping on the verifier's state along the eight
sub-protocols of the linear claim's shared rounds, read forwards: one of the tests with code that
the kind's laws ask in front of each sub-protocol (Johnson/Desc/K14/Law/ShapesSend.lean: shapeK) is
handed on from in front of a sub-protocol to behind it, wherever that sub-protocol's function
returns.

The library has a forward law for each of the eight, at a place's function or a sending's decide
function that returns. This file says each in shapeK's own terms, and lays them in a row along a
run, each from the run up to that sub-protocol alone (Johnson/Desc/K14/Honest/RunsTo.lean: To1, …,
To8). No premise speaks of words, or of a value that a prover sends but for the form of what is
sent: it is true of every prover.

ON THE KEY. The library's shapeK at every number from 2 to 9 itself asks that the key's sizes fit
(through shape2 and shape1: Johnson/Desc/K14/Law/PointCounts.lean). The verifier tests that only in
"(rec_gamma)". So behind "LIN point" and behind the sending of o_u the test is passed only where the
key's sizes fit: it is a premise here of shape_next1 (as the library's shape1) and of
Public8.shape1, Public8.shape2 and Public8.rows2. From "(rec_gamma)" on it is no premise: that
function's return gives it (keyFits_of). Whoever takes shapeK for what is known of the state at the
first two takes the key's sizes with it.

Main names:
  shape_next1, …, shape_next8   **from shapeK in front of a sub-protocol to shapeK behind it**
  shapeAtRun          shapeK at a run's numbers: o_u is the first new message, o_omega the third; as
                      many locations as planned
  Public8.shape1, …, shape8   along a run, from the run up to there
  Public8.keyFits_of  where "(rec_gamma)"'s function has returned, the key's sizes fit
  Public8.rows2, rows3, rows4, rows7, rows8   how many rows lie on the two groups
  Public8.codes1, …, codes8   the state's codes are the plan's (the library's codX), each from the
                      run up to there
  quiet_each          what "(rec_gamma)", "LOC", the joinings and "SPLIT" leave (QuietStep:
                      Johnson/Desc/K14/Law/LedgerOne.lean)

What is not claimed. That a run is there (eight_return). What else the kind's laws and the library's
table ask of the state beside shapeK and codX: the further letter beside the layout's test; the
tests at the numbers 0, 1, 10, 11, 12; that nothing is left at the chain's end; the promises on the
committed table and on the sampled messages; that the statement is in order. What "LIN point", the
two sendings and "LIN zeta" leave, beyond what At1, AtU, AtO write out. Nothing on soundness, on
completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.RunsTo
import Johnson.Desc.K14.Law.LedgerOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Own (keyFits)
open Desc.K14.Law (parU parO parK1_sent shapeK shapeP_iff shapeM_iff shapeU_iff shapeO_iff shape1
  shape2 point_extras linPoint_inv shapeU_sendU shapeM_rec shapeM_loc shapeO_sendO shapeO_joins
  shapeO_zeta shapeO_split QuietStep quiet_at laysRecW rowsOn codX codX_iff onward_split)

/-! ## From the test in front of a sub-protocol to the test behind it -/

/-- **"LIN point"**: where its function returns, the test behind it is passed. In front: the key's
sizes fit (the library's shape1) and nU messages are there. -/
theorem shape_next1 (p : Par) (hS : p.S.sharedSplitNeeded = true) (nU nO n : Nat) (a b : St)
    (r : Fmt.RoundView) (k : linPoint p a [r] = some b) (hn : a.st.oracles.size = nU)
    (hpt : (drawn r).length = p.S.kCol) (h : shape1 p a = true) :
    shapeK p nU nO n 2 b = true := by
  obtain ⟨e1, e2, e3⟩ := point_extras p hS nU a b [r] k hn
  obtain ⟨r', hr, hp, hk, _, _⟩ := linPoint_inv p a b [r] k
  obtain rfl : r = r' := by simpa using hr
  refine (shapeP_iff p nU b).2 ⟨?_, e1, e2, e3⟩
  unfold shape2 shape1
  rw [hk, hp, hpt, Bool.and_eq_true]
  exact ⟨h, beq_self_eq_true _⟩

/-- **The sending of o_u**, which brings two messages: where its decide function returns .ok, the
test in front of it gives the test behind. -/
theorem shape_next2 (P : P14) (nm : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (sentU : Array OracleNotice)
    (hU : withU P.par.S = some sentU) (hQ : Q.sent = sentU) (h2 : sentU.size = 2) (nU n : Nat)
    (a b : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (k : (sendAt P nm Q inFront groups (behindU P.par)).decide a rs gs = .ok b)
    (h : shapeK P.par nU (nU + 2) n 2 a = true) : shapeK P.par nU (nU + 2) n 3 b = true := by
  obtain ⟨x, y⟩ := shapeU_sendU P nm Q inFront groups sentU hU hQ nU a b rs gs k h
  rw [h2] at y
  exact (shapeM_iff P.par nU (nU + 2) 0 b).2 ⟨x, y⟩

/-- **"(rec_gamma)"**: where its function returns, the test in front of it gives the test behind. -/
theorem shape_next3 (p : Par) (nU nO n : Nat) (a b : St) (rs : List Fmt.RoundView)
    (k : laysRec p a rs = some b) (h : shapeK p nU nO n 3 a = true) :
    shapeK p nU nO n 4 b = true := by
  have e := shapeM_rec p nU nO 0 a b rs k h
  rw [Nat.zero_add] at e
  exact e

/-- **"LOC"**, where n locations were sampled: where its function returns, the test in front of it
gives the test behind. -/
theorem shape_next4 (p : Par) (nU nO n : Nat) (a b : St) (r : Fmt.RoundView)
    (cols : List (Nat × List UInt64)) (k : loc p a [r] [cols] = some b)
    (hn : r.drawn.poss.length = n) (h : shapeK p nU nO n 4 a = true) :
    shapeK p nU nO n 5 b = true := by
  have e := shapeM_loc p nU nO _ a b r cols k h
  rw [hn] at e
  exact e

/-- **The sending of o_omega and o_sp**: where its decide function returns .ok, the test in front
of it gives the test behind. -/
theorem shape_next5 (P : P14) (nm : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (hQ : Q.sent = withOmega P.par.S)
    (hS : P.par.S.sharedSplitNeeded = true) (nU nO n : Nat) (hne : nO ≠ nU) (a b : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (k : (sendAt P nm Q inFront groups (behindOmega P.par)).decide a rs gs = .ok b)
    (h : shapeK P.par nU nO n 5 a = true) : shapeK P.par nU nO n 6 b = true := by
  obtain ⟨x, y⟩ := (shapeM_iff P.par nU nO _ a).1 h
  exact shapeO_sendO P nm Q inFront groups hQ hS nU nO _ hne a b rs gs k x y

/-- **The joinings**: where their function returns, the test in front gives the test behind. -/
theorem shape_next6 (p : Par) (nU nO n : Nat) (a b : St) (rs : List Fmt.RoundView)
    (k : joins p a rs = some b) (h : shapeK p nU nO n 6 a = true) :
    shapeK p nU nO n 7 b = true :=
  shapeO_joins p nU nO _ 0 a b rs k h

/-- **"LIN zeta"**: where its function returns, the test in front of it gives the test behind. -/
theorem shape_next7 (p : Par) (nU nO n : Nat) (a b : St) (r : Fmt.RoundView)
    (k : linZeta a [r] = some b) (h : shapeK p nU nO n 7 a = true) :
    shapeK p nU nO n 8 b = true :=
  shapeO_zeta p nU nO _ 0 a b r k h

/-- **"SPLIT"**: where its function returns, the test in front of it gives the test behind. -/
theorem shape_next8 (p : Par) (nU nO n : Nat) (a b : St) (r : Fmt.RoundView)
    (k : split p a [r] = some b) (h : shapeK p nU nO n 8 a = true) :
    shapeK p nU nO n 9 b = true :=
  shapeO_split p nU nO _ 0 a b r k h

/-! ## Along a run, from the run up to each sub-protocol -/

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay} {d0 : St} {V : View8}
  {D : States8}

/-- The library's test in front of sub-protocol k, at the run's numbers: o_u is the first new
message, o_omega the third; as many locations as planned. -/
abbrev shapeAtRun (P : P14) (d0 : St) (k : Nat) (d : St) : Bool :=
  shapeK P.par d0.st.oracles.size (d0.st.oracles.size + 2) P.par.S.fold.columns k d

/-- Behind "LIN point" the test is passed, WHERE THE KEY's SIZES FIT. -/
theorem Public8.shape1 (S : Public8 P sentU layO d0) (u : To1 P d0 V D)
    (hkey : keyFits d0.loc.key P.par.S.fold.index = true) : shapeAtRun P d0 2 D.d1 = true :=
  shape_next1 P.par S.facts.two _ _ _ d0 D.d1 V.r1 u.k1 rfl u.point hkey

/-- Behind the sending of o_u the test is passed, WHERE THE KEY's SIZES FIT. -/
theorem Public8.shape2 (S : Public8 P sentU layO d0) (u : To2 P sentU d0 V D)
    (hkey : keyFits d0.loc.key P.par.S.fold.index = true) : shapeAtRun P d0 3 D.d2 = true :=
  shape_next2 P "send o_u" (parU P sentU) none [] sentU S.facts.goes (parK1_sent P 2 _ sentU)
    S.facts.goesTwo _ _ D.d1 D.d2 [V.r2a, V.r2b] [] (u.s2.decides P "send o_u" none [] [])
    (S.shape1 u.front hkey)

/-- Where "(rec_gamma)"'s function has returned, the key's sizes fit: it has tested them. -/
theorem Public8.keyFits_of (S : Public8 P sentU layO d0) (u : To3 P sentU d0 V D) :
    keyFits d0.loc.key P.par.S.fold.index = true := by
  have hok := (laysRecW P.par D.d2 D.d3 V.rs3 u.k3).1
  simp only [ok, laysRecL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
  have h : D.d2.loc.key.fits P.par.S.fold.index = true := hok.1
  rw [(S.at2 u.front).carried.key] at h
  exact h

/-- Behind "(rec_gamma)" the test is passed. -/
theorem Public8.shape3 (S : Public8 P sentU layO d0) (u : To3 P sentU d0 V D) :
    shapeAtRun P d0 4 D.d3 = true :=
  shape_next3 P.par _ _ _ D.d2 D.d3 V.rs3 u.k3 (S.shape2 u.front (S.keyFits_of u))

/-- Behind "LOC" the test is passed. -/
theorem Public8.shape4 (S : Public8 P sentU layO d0) (u : To4 P sentU d0 V D) :
    shapeAtRun P d0 5 D.d4 = true :=
  shape_next4 P.par _ _ _ D.d3 D.d4 V.r4 V.cols u.k4 u.locs (S.shape3 u.front)

/-- Behind the sending of o_omega and o_sp the test is passed. -/
theorem Public8.shape5 (S : Public8 P sentU layO d0) (u : To5 P sentU d0 V D) :
    shapeAtRun P d0 6 D.d5 = true :=
  shape_next5 P "send o_omega" (parO P) none [] (parK1_sent P 5 _ _) S.facts.two _ _ _ (by omega)
    D.d4 D.d5 [V.r5a, V.r5b] [] (u.s5.decides P "send o_omega" none [] []) (S.shape4 u.front)

/-- Behind the joinings the test is passed. -/
theorem Public8.shape6 (S : Public8 P sentU layO d0) (u : To6 P sentU d0 V D) :
    shapeAtRun P d0 7 D.d6 = true :=
  shape_next6 P.par _ _ _ D.d5 D.d6 V.rs6 u.k6 (S.shape5 u.front)

/-- Behind "LIN zeta" the test is passed. -/
theorem Public8.shape7 (S : Public8 P sentU layO d0) (u : To7 P sentU d0 V D) :
    shapeAtRun P d0 8 D.d7 = true :=
  shape_next7 P.par _ _ _ D.d6 D.d7 V.r7 u.k7 (S.shape6 u.front)

/-- Behind "SPLIT" the test is passed. -/
theorem Public8.shape8 (S : Public8 P sentU layO d0) (u : To8 P sentU d0 V D) :
    shapeAtRun P d0 9 D.d8 = true :=
  shape_next8 P.par _ _ _ D.d7 D.d8 V.r8 u.k8 (S.shape7 u.front)

/-! ## How many rows lie on the two groups -/

/-- Behind its sending no row lies on o_u's group yet, WHERE THE KEY's SIZES FIT. -/
theorem Public8.rows2 (S : Public8 P sentU layO d0) (u : To2 P sentU d0 V D)
    (hkey : keyFits d0.loc.key P.par.S.fold.index = true) :
    (rowsOn D.d2 D.d2.loc.gU).length = 0 :=
  ((shapeU_iff P.par _ _ D.d2).1 ((shapeM_iff P.par _ _ _ D.d2).1 (S.shape2 u hkey)).1).2.2.2

/-- Behind "(rec_gamma)" just its rows lie on o_u's group: as many as the key has answers a row. -/
theorem Public8.rows3 (S : Public8 P sentU layO d0) (u : To3 P sentU d0 V D) :
    (rowsOn D.d3 D.d3.loc.gU).length = P.par.S.fold.index.answers :=
  ((shapeU_iff P.par _ _ D.d3).1 ((shapeM_iff P.par _ _ _ D.d3).1 (S.shape3 u)).1).2.2.2

/-- Behind "LOC": and one row more for each sampled location. -/
theorem Public8.rows4 (S : Public8 P sentU layO d0) (u : To4 P sentU d0 V D) :
    (rowsOn D.d4 D.d4.loc.gU).length = P.par.S.fold.index.answers + P.par.S.fold.columns :=
  ((shapeU_iff P.par _ _ D.d4).1 ((shapeM_iff P.par _ _ _ D.d4).1 (S.shape4 u)).1).2.2.2

/-- In front of "SPLIT": as behind "LOC" on o_u's group, and no row on o_omega's. -/
theorem Public8.rows7 (S : Public8 P sentU layO d0) (u : To7 P sentU d0 V D) :
    (rowsOn D.d7 D.d7.loc.gU).length = P.par.S.fold.index.answers + P.par.S.fold.columns ∧
      (rowsOn D.d7 D.d7.loc.gOmega).length = 0 := by
  obtain ⟨hU, _, _, _, hO, _⟩ := (shapeO_iff P.par _ _ _ _ D.d7).1 (S.shape7 u)
  exact ⟨((shapeU_iff P.par _ _ D.d7).1 hU).2.2.2, hO⟩

/-- Behind "SPLIT": one row more on o_u's group, and one row on o_omega's. -/
theorem Public8.rows8 (S : Public8 P sentU layO d0) (u : To8 P sentU d0 V D) :
    (rowsOn D.d8 D.d8.loc.gU).length =
        P.par.S.fold.index.answers + P.par.S.fold.columns + 1 ∧
      (rowsOn D.d8 D.d8.loc.gOmega).length = 1 := by
  obtain ⟨hU, _, _, _, hO, _⟩ := (shapeO_iff P.par _ _ _ _ D.d8).1 (S.shape8 u)
  exact ⟨((shapeU_iff P.par _ _ D.d8).1 hU).2.2.2, hO⟩

/-! ## The codes, and what four of the eight leave -/

/-- The state's codes are the plan's behind "LIN point" (the library's codX), from the run up to
there. -/
theorem Public8.codes1 (S : Public8 P sentU layO d0) (u : To1 P d0 V D) (j : Nat) :
    codX P j D.d1 = true :=
  (codX_iff P j _).2 (S.at1 u).carried.codes

/-- The state's codes are the plan's behind the sending of o_u (the library's codX), from the run up
to there. -/
theorem Public8.codes2 (S : Public8 P sentU layO d0) (u : To2 P sentU d0 V D) (j : Nat) :
    codX P j D.d2 = true :=
  (codX_iff P j _).2 (S.at2 u).carried.codes

/-- The state's codes are the plan's behind "(rec_gamma)" (the library's codX), from the run up to
there. -/
theorem Public8.codes3 (S : Public8 P sentU layO d0) (u : To3 P sentU d0 V D) (j : Nat) :
    codX P j D.d3 = true :=
  (codX_iff P j _).2 (S.at3 u).carried.codes

/-- The state's codes are the plan's behind "LOC" (the library's codX), from the run up to there. -/
theorem Public8.codes4 (S : Public8 P sentU layO d0) (u : To4 P sentU d0 V D) (j : Nat) :
    codX P j D.d4 = true :=
  (codX_iff P j _).2 (S.at4 u).carried.codes

/-- The state's codes are the plan's behind the sending of o_omega and o_sp (the library's codX),
from the run up to there. -/
theorem Public8.codes5 (S : Public8 P sentU layO d0) (u : To5 P sentU d0 V D) (j : Nat) :
    codX P j D.d5 = true :=
  (codX_iff P j _).2 (S.at5 u).carried.codes

/-- The state's codes are the plan's behind the joinings (the library's codX), from the run up to
there. -/
theorem Public8.codes6 (S : Public8 P sentU layO d0) (u : To6 P sentU d0 V D) (j : Nat) :
    codX P j D.d6 = true :=
  (codX_iff P j _).2 (S.at6 u).carried.codes

/-- The state's codes are the plan's behind "LIN zeta" (the library's codX), from the run up to
there. -/
theorem Public8.codes7 (S : Public8 P sentU layO d0) (u : To7 P sentU d0 V D) (j : Nat) :
    codX P j D.d7 = true :=
  (codX_iff P j _).2 (S.at7 u).2

/-- The state's codes are the plan's behind "SPLIT" (the library's codX). -/
theorem Public8.codes8 (S : Public8 P sentU layO d0) (u : To8 P sentU d0 V D) (j : Nat) :
    codX P j D.d8 = true :=
  (codX_iff P j _).2
    (((onward_split P.par D.d7 D.d8 V.r8 S.facts.two u.k8).1.grows.1).trans (S.at7 u.front).2)

/-- **Where the decide function of "(rec_gamma)", "LOC", the joinings or "SPLIT" returns .ok, it
leaves what the kind notes, the messages and the book** (the library's quiet_at, said for each by
name). -/
theorem quiet_each (P : P14) (hS : P.S.sharedSplitNeeded = true)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (a b : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (b3.decide a rs gs = .ok b → QuietStep a b) ∧ (b4.decide a rs gs = .ok b → QuietStep a b) ∧
      (b6.decide a rs gs = .ok b → QuietStep a b) ∧
      (b8.decide a rs gs = .ok b → QuietStep a b) := by
  have q := quiet_at P b1 b2 b3 b4 b5 b6 b7 b8 hb hS
  exact ⟨q b3 (by simp) a rs gs b, q b4 (by simp) a rs gs b, q b6 (by simp) a rs gs b,
    q b8 (by simp) a rs gs b⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.shape_next1
#print axioms Desc.K14.Honest.shape_next2
#print axioms Desc.K14.Honest.shape_next3
#print axioms Desc.K14.Honest.shape_next4
#print axioms Desc.K14.Honest.shape_next5
#print axioms Desc.K14.Honest.shape_next6
#print axioms Desc.K14.Honest.shape_next7
#print axioms Desc.K14.Honest.shape_next8
#print axioms Desc.K14.Honest.Public8.shape1
#print axioms Desc.K14.Honest.Public8.shape2
#print axioms Desc.K14.Honest.Public8.keyFits_of
#print axioms Desc.K14.Honest.Public8.shape3
#print axioms Desc.K14.Honest.Public8.shape4
#print axioms Desc.K14.Honest.Public8.shape5
#print axioms Desc.K14.Honest.Public8.shape6
#print axioms Desc.K14.Honest.Public8.shape7
#print axioms Desc.K14.Honest.Public8.shape8
#print axioms Desc.K14.Honest.Public8.rows2
#print axioms Desc.K14.Honest.Public8.rows3
#print axioms Desc.K14.Honest.Public8.rows4
#print axioms Desc.K14.Honest.Public8.rows7
#print axioms Desc.K14.Honest.Public8.rows8
#print axioms Desc.K14.Honest.Public8.codes1
#print axioms Desc.K14.Honest.Public8.codes2
#print axioms Desc.K14.Honest.Public8.codes3
#print axioms Desc.K14.Honest.Public8.codes4
#print axioms Desc.K14.Honest.Public8.codes5
#print axioms Desc.K14.Honest.Public8.codes6
#print axioms Desc.K14.Honest.Public8.codes7
#print axioms Desc.K14.Honest.Public8.codes8
#print axioms Desc.K14.Honest.quiet_each
