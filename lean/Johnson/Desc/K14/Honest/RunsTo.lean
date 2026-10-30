--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/RunsTo.lean: the eight sub-protocols of the linear claim's shared rounds: a
run of the kind's functions UP TO a sub-protocol, and the facts on the verifier's state that follow
from such a run and from public premises alone.

The files above this one show something behind each of the eight. Their premise on the run is the
run up to that sub-protocol: what a later sub-protocol asks is no premise of an earlier one. So
nothing is asked of the key in front of "(rec_gamma)", whose function alone tests the key. This file
has the definitions, and no word on a prover: it speaks of no words, tables or honest values.

Main names:
  View8, States8, View8.fill, States8.fill   a view's eight rounds with the columns; the states of a
                      run; fillers for the fields behind an early sub-protocol, which no premise on
                      a run up to there reads
  Public8             what stands in front of the eight, as far as it is public: PlanFacts; the two
                      sendings pass their kind's test on the plan; the first state's codes are the
                      plan's; its statement and book are in step. Nothing on the key
  To1, …, To8         a run up to the first, …, the eighth sub-protocol: the places' functions and
                      decideSend have returned; of a round's form, what the format's test on that
                      round gives
  SentTo.unique       a sending and the note behind it return one state
  At1, AtU, AtO, Public8.at1, …, at7   **the facts on the state behind each sub-protocol, from the
                      run up to it**
  linOk_of, AtU.stands   the shape's conditions in the library's form `linOk`; between the two
                      sendings o_u stands as the laws of "(rec_gamma)" and "LOC" ask it
  Public8.returned    the whole run, in the form of Johnson/Desc/K14/Honest/YesChain.lean

What is not claimed. That a run is there: eight_return (YesChain.lean). That a decision accepts: a
run here speaks of the places' functions and of decideSend; from the format's step to these:
Johnson/Desc/K14/Honest/StepsBack.lean. Nothing on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (roundsFit)
open VerifiableInference.Desc.K1 (planOkOwn)
open VerifiableInference.Desc.Key (laid_point laid_rec laid_loc joined_joins)
open VerifiableInference.Desc.Key.LaidW (inFrontOf)
open Desc.K14.Law (parK1_sent parU parO linZeta_inv seatedUB seatedUB_iff)

/-! ## A view, the states of a run, and a run up to a sub-protocol -/

/-- A view's eight rounds of the shared rounds, with the columns that "LOC" is shown. rs3, rs6: what
the two sub-protocols without a round are handed. -/
structure View8 where
  r1 : Fmt.RoundView
  r2a : Fmt.RoundView
  r2b : Fmt.RoundView
  r4 : Fmt.RoundView
  r5a : Fmt.RoundView
  r5b : Fmt.RoundView
  r7 : Fmt.RoundView
  r8 : Fmt.RoundView
  cols : List (Nat × List UInt64)
  rs3 : List Fmt.RoundView
  rs6 : List Fmt.RoundView

/-- The states of a run: behind each of the eight; x2, x5, ids2, ids5: what the two sendings' own
decisions return. -/
structure States8 where
  d1 : St
  d2 : St
  d3 : St
  d4 : St
  d5 : St
  d6 : St
  d7 : St
  d8 : St
  x2 : DState (Array Nat)
  x5 : DState (Array Nat)
  ids2 : Array Nat
  ids5 : Array Nat

/-- A view all of whose rounds are r, without a column: for whoever speaks of a run up to an early
sub-protocol and has to fill the later fields, which no premise on such a run reads. -/
def View8.fill (r : Fmt.RoundView) : View8 := ⟨r, r, r, r, r, r, r, r, [], [], []⟩

/-- States that are all d: for the same use. -/
def States8.fill (d : St) : States8 :=
  ⟨d, d, d, d, d, d, d, d, inFrontOf d, inFrontOf d, #[], #[]⟩

/-- **What stands in front of the eight, as far as it is public**: on the parameters and on the
first state's book-keeping. Nothing on the key, on words or on a value shown. -/
structure Public8 (P : P14) (sentU : Array OracleNotice) (layO : TreeLay) (d0 : St) : Prop where
  facts : PlanFacts P.par P.codes sentU layO
  planU : planOkOwn (parU P sentU) = true
  planO : planOkOwn (parO P) = true
  codes : d0.st.codes = P.codes
  step : d0.st.oracles.size = d0.book.place.size

/-- A run up to "LIN point": its function has returned; its round has the planned form. -/
structure To1 (P : P14) (d0 : St) (V : View8) (D : States8) : Prop where
  k1 : linPoint P.par d0 [V.r1] = some D.d1
  point : (drawn V.r1).length = P.par.S.kCol

/-- A run up to the sending of o_u: decideSend has returned and the kind's note is made; the two
rounds pass the format's test on their form. -/
structure To2 (P : P14) (sentU : Array OracleNotice) (d0 : St) (V : View8) (D : States8) :
    Prop where
  front : To1 P d0 V D
  s2 : SentTo (parU P sentU) (behindU P.par) D.d1 D.d2 V.r2a V.r2b D.x2 D.ids2
  fitsU : roundsFit (VerifiableInference.Desc.K1.rounds (parU P sentU)) [V.r2a, V.r2b] = true

/-- A run up to "(rec_gamma)". -/
structure To3 (P : P14) (sentU : Array OracleNotice) (d0 : St) (V : View8) (D : States8) :
    Prop where
  front : To2 P sentU d0 V D
  k3 : laysRec P.par D.d2 V.rs3 = some D.d3

/-- A run up to "LOC": its function has returned; as many locations were sampled as planned. -/
structure To4 (P : P14) (sentU : Array OracleNotice) (d0 : St) (V : View8) (D : States8) :
    Prop where
  front : To3 P sentU d0 V D
  k4 : loc P.par D.d3 [V.r4] [V.cols] = some D.d4
  locs : V.r4.drawn.poss.length = P.par.S.fold.columns

/-- A run up to the sending of o_omega and o_sp. -/
structure To5 (P : P14) (sentU : Array OracleNotice) (d0 : St) (V : View8) (D : States8) :
    Prop where
  front : To4 P sentU d0 V D
  s5 : SentTo (parO P) (behindOmega P.par) D.d4 D.d5 V.r5a V.r5b D.x5 D.ids5
  fitsO : roundsFit (VerifiableInference.Desc.K1.rounds (parO P)) [V.r5a, V.r5b] = true

/-- A run up to the joinings. -/
structure To6 (P : P14) (sentU : Array OracleNotice) (d0 : St) (V : View8) (D : States8) :
    Prop where
  front : To5 P sentU d0 V D
  k6 : joins P.par D.d5 V.rs6 = some D.d6

/-- A run up to "LIN zeta": its function has returned; its round has the planned form. -/
structure To7 (P : P14) (sentU : Array OracleNotice) (d0 : St) (V : View8) (D : States8) :
    Prop where
  front : To6 P sentU d0 V D
  k7 : linZeta D.d6 [V.r7] = some D.d7
  zeta : (drawn V.r7).length = P.par.S.kRow

/-- A run up to "SPLIT": the whole run. -/
structure To8 (P : P14) (sentU : Array OracleNotice) (d0 : St) (V : View8) (D : States8) :
    Prop where
  front : To7 P sentU d0 V D
  k8 : split P.par D.d7 [V.r8] = some D.d8

/-! ## The facts behind each sub-protocol, from the run up to it -/

/-- A sending and the note behind it return one state. -/
theorem SentTo.unique {Q : VerifiableInference.Desc.K1.Par} {note : St → Array Nat → Option St}
    {d d' d'' : St} {ra rb : Fmt.RoundView} {x x' : DState (Array Nat)} {ids ids' : Array Nat}
    (h : SentTo Q note d d' ra rb x ids) (k : SentTo Q note d d'' ra rb x' ids') : d' = d'' := by
  have a : (ids, x) = (ids', x') := Except.ok.inj (h.sent.symm.trans k.sent)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj a
  exact Option.some.inj (h.noted.symm.trans k.noted)

/-- The facts behind "LIN point". -/
structure At1 (P : P14) (d0 : St) (r1 : Fmt.RoundView) (d : St) : Prop where
  carried : Carried P.par P.codes d0.loc.key d [] []
  loc : d.loc = { d0.loc with
    psiSh := drawn r1, gU := d0.st.groups.size, gOmega := d0.st.groups.size + 1 }
  size : d.st.oracles.size = d0.st.oracles.size

/-- The facts between o_u's sending and o_omega's. mU: the members of o_u's group. -/
structure AtU (P : P14) (d0 : St) (r1 : Fmt.RoundView) (d : St) (mU : List Nat) : Prop where
  carried : Carried P.par P.codes d0.loc.key d mU []
  hasU : HasU P.par d
  loc : d.loc = locU P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1
  size : d.st.oracles.size = d0.st.oracles.size + 2

/-- The facts behind o_omega's sending. mU, mO: the members of the two groups. -/
structure AtO (P : P14) (d0 : St) (r1 : Fmt.RoundView) (d : St) (mU mO : List Nat) : Prop where
  carried : Carried P.par P.codes d0.loc.key d mU mO
  hasU : HasU P.par d
  hasO : HasO P.par d
  loc : d.loc = locO P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay} {d0 : St} {V : View8}
  {D : States8}

/-- The shape's conditions, in the library's form `linOk`. -/
theorem linOk_of (hP : PlanFacts P.par P.codes sentU layO) : linOk P.codes P.par.S = true :=
  (VerifiableInference.Desc.Own.linFits_eq _ _).symm.trans hP.lin

/-- Between the two sendings o_u stands as the laws of "(rec_gamma)" and "LOC" ask it. -/
theorem AtU.stands {r1 : Fmt.RoundView} {d : St} {mU : List Nat} (A : AtU P d0 r1 d mU)
    (hP : PlanFacts P.par P.codes sentU layO) : seatedUB P.par d = true := by
  obtain ⟨x, hx, hs, _⟩ := A.hasU.u
  exact (seatedUB_iff P.par d).2
    ⟨⟨x, hx, hs⟩, A.hasU.lay, by rw [A.carried.codes]; exact linOk_of hP⟩

/-- The facts behind "LIN point", from the run up to it. -/
theorem Public8.at1 (S : Public8 P sentU layO d0) (u : To1 P d0 V D) : At1 P d0 V.r1 D.d1 := by
  obtain ⟨r, hr, L1⟩ := laid_point P.par d0 D.d1 [V.r1] S.facts.two u.k1
  obtain rfl : V.r1 = r := by simpa using hr
  exact ⟨carried_point P.par P.codes d0.loc.key d0 D.d1 V.r1 S.codes S.step rfl u.point L1, L1.loc,
    by rw [L1.oracles]⟩

/-- The facts behind the sending of o_u, from the run up to it. -/
theorem Public8.at2 (S : Public8 P sentU layO d0) (u : To2 P sentU d0 V D) :
    AtU P d0 V.r1 D.d2 [] := by
  have A := S.at1 u.front
  obtain ⟨d2, x2, ids2, s2, B2, U2, l2⟩ := sendU_returns P.par P.codes d0.loc.key (parU P sentU)
    sentU layO S.facts rfl (parK1_sent P 2 _ sentU) D.d1 V.r2a V.r2b A.carried
    (seeds_nz _ _ _ u.fitsU) (fitB_of_rounds _ _ _ S.planU S.facts.lengths u.fitsU)
  obtain rfl : D.d2 = d2 := u.s2.unique s2
  refine ⟨B2, U2, ?_, by rw [u.s2.size, A.size]⟩
  rw [l2, A.loc, A.size]
  rfl

/-- The facts behind "(rec_gamma)", from the run up to it. -/
theorem Public8.at3 (S : Public8 P sentU layO d0) (u : To3 P sentU d0 V D) :
    AtU P d0 V.r1 D.d3 [D.d3.loc.oU.oracle] := by
  have A := S.at2 u.front
  obtain ⟨GU, rows, L⟩ := laid_rec P.par D.d2 D.d3 V.rs3 u.k3
  have B := carried_rec P.par P.codes _ D.d2 D.d3 GU rows [] A.carried L
  rw [← L.loc] at B
  exact ⟨B, hasU_rec P.par D.d2 D.d3 GU rows A.hasU L, L.loc.trans A.loc, by rw [L.size, A.size]⟩

/-- The facts behind "LOC", from the run up to it. -/
theorem Public8.at4 (S : Public8 P sentU layO d0) (u : To4 P sentU d0 V D) :
    AtU P d0 V.r1 D.d4 [D.d4.loc.oU.oracle] := by
  have A := S.at3 u.front
  obtain ⟨r, cs, GU, rows, _, _, L⟩ := laid_loc P.par D.d3 D.d4 [V.r4] [V.cols] u.k4
  have B := carried_loc P.par P.codes _ D.d3 D.d4 r GU rows _ _ A.carried L
  rw [← L.loc] at B
  exact ⟨B, hasU_loc P.par D.d3 D.d4 r GU rows A.hasU L, L.loc.trans A.loc,
    by rw [L.oracles, A.size]⟩

/-- The facts behind the sending of o_omega and o_sp, from the run up to it. -/
theorem Public8.at5 (S : Public8 P sentU layO d0) (u : To5 P sentU d0 V D) :
    AtO P d0 V.r1 D.d5 [D.d5.loc.oU.oracle] [] := by
  have A := S.at4 u.front
  obtain ⟨d5, x5, ids5, s5, B5, U5, O5, l5⟩ := sendO_returns P.par P.codes d0.loc.key (parO P)
    sentU layO S.facts rfl (parK1_sent P 5 _ _) D.d4 V.r5a V.r5b _ _ A.carried A.hasU
    (seeds_nz _ _ _ u.fitsO) (fitB_of_rounds _ _ _ S.planO S.facts.lengths u.fitsO)
  obtain rfl : D.d5 = d5 := u.s5.unique s5
  have e5 : D.d5.loc.oU = D.d4.loc.oU := by rw [l5]
  rw [← e5] at B5
  refine ⟨B5, U5, O5, ?_⟩
  rw [l5, A.loc, A.size]
  rfl

/-- The facts behind the joinings, from the run up to them. -/
theorem Public8.at6 (S : Public8 P sentU layO d0) (u : To6 P sentU d0 V D) :
    AtO P d0 V.r1 D.d6 [D.d6.loc.oU.oracle, D.d6.loc.oSp] [D.d6.loc.oOmega, D.d6.loc.oSp] := by
  have A := S.at5 u.front
  obtain ⟨GU, GO, L⟩ := joined_joins P.par D.d5 D.d6 V.rs6 S.facts.two u.k6
  have B := carried_joined P.par P.codes _ D.d5 D.d6 GU GO A.carried L
  rw [← L.loc] at B
  exact ⟨B, hasU_joined P.par D.d5 D.d6 GU GO A.hasU A.hasO L,
    hasO_joined P.par D.d5 D.d6 GU GO A.hasO L, L.loc.trans A.loc⟩

/-- What "LIN zeta" leaves: the state in front with the sampled point noted. -/
theorem To7.d7_eq (u : To7 P sentU d0 V D) :
    D.d7 = { D.d6 with loc := { D.d6.loc with zFd := drawn V.r7 } } :=
  linZeta_inv D.d6 D.d7 V.r7 u.k7

/-- What the kind notes behind "LIN zeta", and the codes there. -/
theorem Public8.at7 (S : Public8 P sentU layO d0) (u : To7 P sentU d0 V D) :
    D.d7.loc = locZ P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size V.r1 V.r7 ∧
      D.d7.st.codes = P.codes := by
  have A := S.at6 u.front
  rw [u.d7_eq]
  refine ⟨?_, A.carried.codes⟩
  show ({ D.d6.loc with zFd := drawn V.r7 } : Lin) = _
  rw [A.loc]
  rfl

/-- **The whole run, in the form of Johnson/Desc/K14/Honest/YesChain.lean.** -/
theorem Public8.returned (S : Public8 P sentU layO d0) (u : To8 P sentU d0 V D) :
    Returned P sentU d0 V.r1 V.r2a V.r2b V.r4 V.r5a V.r5b V.r7 V.r8 V.cols V.rs3 V.rs6
      D.d1 D.d2 D.d3 D.d4 D.d5 D.d6 D.d7 D.d8 D.x2 D.x5 D.ids2 D.ids5 := by
  have u7 := u.front
  have u6 := u7.front
  have u5 := u6.front
  have u4 := u5.front
  have u3 := u4.front
  have u2 := u3.front
  have A6 := S.at6 u6
  have e7 := u7.d7_eq
  have U7 : HasU P.par D.d7 := by
    rw [e7]
    exact ⟨A6.hasU.lay, A6.hasU.u⟩
  have O7 : HasO P.par D.d7 := by
    rw [e7]
    exact ⟨A6.hasO.omega, A6.hasO.sp, A6.hasO.ledger, A6.hasO.apart, A6.hasO.apartU,
      A6.hasO.apartOU, A6.hasO.alone⟩
  have F8 : Front8 P.par D.d7 := by
    have U7' : HasU P.par { D.d6 with loc := { D.d6.loc with zFd := drawn V.r7 } } :=
      ⟨A6.hasU.lay, A6.hasU.u⟩
    have O7' : HasO P.par { D.d6 with loc := { D.d6.loc with zFd := drawn V.r7 } } :=
      ⟨A6.hasO.omega, A6.hasO.sp, A6.hasO.ledger, A6.hasO.apart, A6.hasO.apartU, A6.hasO.apartOU,
        A6.hasO.alone⟩
    rw [e7]
    exact front8_of S.facts.lin ⟨A6.carried.codes, A6.carried.step, A6.carried.key, A6.carried.psi,
      A6.carried.two, A6.carried.gU, A6.carried.gO⟩ U7' O7' u7.zeta S.facts.free
  exact ⟨u2.front.k1, u2.s2, u3.k3, u4.k4, u5.s5, u6.k6, u7.k7, u.k8, (S.at2 u2).loc,
    (S.at3 u3).loc, (S.at7 u7).1, (S.at1 u2.front).size, (S.at4 u4).size,
    (S.at2 u2).carried.codes, (S.at3 u3).carried.codes, (S.at7 u7).2,
    frontU_of S.facts.lin (S.at3 u3).carried (S.at3 u3).hasU, F8, (S.at2 u2).hasU,
    (S.at3 u3).hasU, U7, O7⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.SentTo.unique
#print axioms Desc.K14.Honest.linOk_of
#print axioms Desc.K14.Honest.AtU.stands
#print axioms Desc.K14.Honest.Public8.at1
#print axioms Desc.K14.Honest.Public8.at2
#print axioms Desc.K14.Honest.Public8.at3
#print axioms Desc.K14.Honest.Public8.at4
#print axioms Desc.K14.Honest.Public8.at5
#print axioms Desc.K14.Honest.Public8.at6
#print axioms Desc.K14.Honest.To7.d7_eq
#print axioms Desc.K14.Honest.Public8.at7
#print axioms Desc.K14.Honest.Public8.returned
