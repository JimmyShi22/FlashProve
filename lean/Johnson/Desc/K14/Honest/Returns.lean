-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Honest/Returns.lean: the eight sub-protocols of the linear claim's shared rounds:
THE «RETURNS» LAW, sub-protocol by sub-protocol, AT ANY STATE: from facts on the state in front, the
step's own tests on rounds and columns, and the named tests on values: the sub-protocol's own step
returns .ok, and the facts behind hold.

Johnson/Desc/K14/Honest/StepsOn.lean has the step's return from a run of steps in front. Here no run
is asked: the premise is a list of facts on the state's flags, counts, numbers, shapes, codes and
pad places (Johnson/Desc/K14/Honest/YesBorders.lean: Carried, HasU, HasO), and each law hands the
next one its premise. NOTHING IS ASKED OF A VALUE THAT A PROVER SENDS. OF THE VERIFIER's OWN RANDOM
VALUES THE PREMISE Block.Fits ASKS SOMETHING: at the two sendings no sampled seed has the factor 0
as machine words; at "LOC" every sampled location is below 2 ^ logN: lists of challenges that fail
there are shut out by that premise. Of the key "(rec_gamma)" asks: no seed has the factor 0.

Main names:
  Facts P k b d       the facts at the border in front of the sub-protocol number b. One of them is
                      no fact on a shape: the key is k
  facts_first         the shared chain's first state has them
  returns1, …, returns7   **Facts b, and the library's Block.Fits: the step returns, and Facts (b +
                      1) behind.** At the two sendings beside: their kind's test on the plan. AT
                      returns3 BESIDE: the key's sizes fit, and no seed of the key has the factor 0
  returns8            "SPLIT" returns. What lies behind it is not said
  shapeK_not_enough   the library's book-keeping test shapeK is too weak for such a law: strike the
                      groups of a state that passes it in front of "(rec_gamma)": it still passes,
                      and the function returns nothing
  rec_rejects         the test on values is not idle: where a seed of the key has the factor 0 the
                      step does not return

What is assumed, as premises: PlanFacts (Johnson/Desc/K14/Honest/YesChain.lean), and that the kind's
text makes its eight at P (Eight P). Among the clauses of PlanFacts: the shape has two codes; the
masks go ahead; o_u's sending has two messages, o_u among them; o_omega has a tree of its own. At
another plan returns1, …, returns8 say nothing.

What is not claimed. That what lies behind is a function of a typed shape in front: the facts are
propositions, and no projection of the state onto a shape is defined. That each fact is needed. That
the tests on rounds and columns are passed. Nothing on soundness or on hiding. This is not
completeness of the protocol or of a program.

-/
import Johnson.Desc.K14.Honest.StepsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block OpenedColumn noDigest groupsOf roundsFit_noDigest roundsFit_two'
  step_iff)
open VerifiableInference.Desc.Own (keyFits allZero)
open VerifiableInference.Desc.K1 (planOkOwn)
open VerifiableInference.Desc.Key (laid_point laid_rec laid_loc joined_joins)
open Desc.K14.Law (parU parO parK1_sent point_fits loc_fits fits_one shapeK shapeM shapeM_iff
  shapeU_iff midB_iff rowsOn laysRecW)
open VerifiableInference.Desc.Ground (joinP joinL)

/-- **The facts on the state at the border in front of the sub-protocol number b** (1: "LIN point",
…, 8: "SPLIT"). All are on flags, counts, numbers, shapes, codes and pad places, but one: the key
is k. -/
def Facts (P : P14) (k : TableKey) : Nat → St → Prop
  | 1, d => d.st.codes = P.codes ∧ d.st.oracles.size = d.book.place.size ∧ d.loc.key = k
  | 2, d => Carried P.par P.codes k d [] []
  | 3, d => Carried P.par P.codes k d [] [] ∧ HasU P.par d
  | 4, d => Carried P.par P.codes k d [d.loc.oU.oracle] [] ∧ HasU P.par d
  | 5, d => Carried P.par P.codes k d [d.loc.oU.oracle] [] ∧ HasU P.par d
  | 6, d => Carried P.par P.codes k d [d.loc.oU.oracle] [] ∧ HasU P.par d ∧ HasO P.par d
  | 7, d => Carried P.par P.codes k d [d.loc.oU.oracle, d.loc.oSp] [d.loc.oOmega, d.loc.oSp] ∧
      HasU P.par d ∧ HasO P.par d
  | 8, d => Carried P.par P.codes k d [d.loc.oU.oracle, d.loc.oSp] [d.loc.oOmega, d.loc.oSp] ∧
      HasU P.par d ∧ HasO P.par d ∧ d.loc.zFd.length = P.par.S.kRow
  | _, _ => True

/-- The shared chain's first state has the facts in front of "LIN point". -/
theorem facts_first (P : P14) (key : TableKey) : Facts P key 1 (first P.codes key) :=
  ⟨rfl, rfl, rfl⟩

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay} {k : TableKey}

/-- **"LIN point"**: from the facts in front and the step's own tests on rounds and columns: the
step returns, and the facts behind hold. -/
theorem returns1 (hP : PlanFacts P.par P.codes sentU layO) (B : Eight P) (ft : Nat) (d : St)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (h : Facts P k 1 d) (hF : B.b1.Fits ft rs cols) :
    ∃ d', B.b1.step ft d rs cols = .ok (d', (B.b1.want ft rs).length) ∧ Facts P k 2 d' := by
  obtain ⟨hc, hst, hk⟩ := h
  obtain ⟨R, rfl, _⟩ := point_fits P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made rs hF.1
  have k1 := linPoint_returns P.par d (noDigest R) (by rw [hc]; exact hP.lengths)
    (by rw [hc]; exact hP.lin) (by rw [hc]; exact hP.groupU) (by rw [hc]; exact hP.groupO) hP.two
  have hs := (step_iff ft B.b1 d _ [R] cols _).2 ⟨hF, (B.forth hP.goes).1 _ _ _ _ k1, rfl⟩
  obtain ⟨R', hR', _, _, hpt⟩ := B.back1 hP.goes ft d _ _ _ _ hs
  obtain rfl : R = R' := by simpa using hR'
  obtain ⟨r, hr, L1⟩ := laid_point P.par d _ [noDigest R] hP.two k1
  obtain rfl : noDigest R = r := by simpa using hr
  exact ⟨_, hs, carried_point P.par P.codes k d _ (noDigest R) hc hst hk hpt L1⟩

/-- **The sending of o_u.** The OOD answers shown are not tested. -/
theorem returns2 (hP : PlanFacts P.par P.codes sentU layO)
    (hBU : planOkOwn (parU P sentU) = true) (B : Eight P) (ft : Nat) (d : St) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (h : Facts P k 2 d) (hF : B.b2.Fits ft rs cols) :
    ∃ d', B.b2.step ft d rs cols = .ok (d', (B.b2.want ft rs).length) ∧ Facts P k 3 d' := by
  obtain ⟨_, e2, _⟩ := blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hP.goes
  have hf := hF.1
  rw [e2] at hf
  obtain ⟨Ra, Rb, rfl⟩ := roundsFit_two' _ _ rs hf
  have hf' := (roundsFit_noDigest _ [Ra, Rb]).trans hf
  obtain ⟨d2, x, ids, s2, B2, U2, _⟩ := sendU_returns P.par P.codes k (parU P sentU) sentU layO hP
    rfl (parK1_sent P 2 _ sentU) d _ _ h (seeds_nz _ _ _ hf')
    (fitB_of_rounds _ _ _ hBU hP.lengths hf')
  exact ⟨d2, (step_iff ft B.b2 d _ [Ra, Rb] cols _).2
    ⟨hF, (B.forth hP.goes).2.1 _ _ _ _ _ _ _ s2, rfl⟩, B2, U2⟩

/-- **"(rec_gamma)"**, WHERE THE KEY's SIZES FIT AND NO SEED OF THE KEY HAS THE FACTOR 0. -/
theorem returns3 (hP : PlanFacts P.par P.codes sentU layO) (B : Eight P) (ft : Nat) (d : St)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (h : Facts P k 3 d)
    (hkey : keyFits k P.par.S.fold.index = true) (hbeta : (k.seeds.all (!allZero ·.beta)) = true)
    (hF : B.b3.Fits ft rs cols) :
    ∃ d', B.b3.step ft d rs cols = .ok (d', (B.b3.want ft rs).length) ∧ Facts P k 4 d' := by
  obtain ⟨hB, hH⟩ := h
  obtain ⟨_, _, _, _, k3⟩ := laysRec_returns P.par d (rs.map noDigest) (frontU_of hP.lin hB hH)
    (by rw [hB.key]; exact hkey) (by rw [hB.key]; exact hbeta)
  obtain ⟨GU, rows, L⟩ := laid_rec P.par d _ _ k3
  have C := carried_rec P.par P.codes k d _ GU rows [] hB L
  rw [← L.loc] at C
  exact ⟨_, (step_iff ft B.b3 d _ rs cols _).2 ⟨hF, (B.forth hP.goes).2.2.1 _ _ _ _ k3, rfl⟩, C,
    hasU_rec P.par d _ GU rows hH L⟩

/-- **"LOC".** The columns' words are not tested. -/
theorem returns4 (hP : PlanFacts P.par P.codes sentU layO) (B : Eight P) (ft : Nat) (d : St)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (h : Facts P k 4 d) (hF : B.b4.Fits ft rs cols) :
    ∃ d', B.b4.step ft d rs cols = .ok (d', (B.b4.want ft rs).length) ∧ Facts P k 5 d' := by
  obtain ⟨hB, hH⟩ := h
  obtain ⟨_, _, _, e4, _⟩ := blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
    hP.goes
  obtain ⟨R, rfl, hl, _⟩ := loc_fits P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made rs hF.1
  have hg : groupsOf ft B.b4.rounds ([R].map (·.drawn)) =
      [(Fmt.listOf (R.drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
        (Fmt.storedKey P.item, x, P.S.fold.index.rows)] := by
    rw [e4]
    exact loc_groups P ft R.drawn hl
  have hw : B.b4.want ft [R] =
      (Fmt.listOf (R.drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
        (Fmt.storedKey P.item, x, P.S.fold.index.rows) := by
    unfold Block.want
    rw [hg]
    simp
  have hc : (cols.take (B.b4.want ft [R]).length).map (fun c => (c.1, c.2.1, c.2.2.length)) =
      B.b4.want ft [R] := by simpa using hF.2
  have hlen : (cols.take (B.b4.want ft [R]).length).length = (B.b4.want ft [R]).length := by
    have e := congrArg List.length hc
    rw [List.length_map] at e
    exact e
  have hsh : B.b4.shown ft [R] cols =
      [(cols.take (B.b4.want ft [R]).length).map fun c => (c.2.1, c.2.2)] := by
    have e1 : ((Fmt.listOf (R.drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
        (Fmt.storedKey P.item, x, P.S.fold.index.rows)).length =
        (cols.take (B.b4.want ft [R]).length).length := by
      rw [← hw]
      exact hlen.symm
    unfold Block.shown
    rw [hg]
    simp only [List.map_cons, List.map_nil, e1]
    show [((cols.take (B.b4.want ft [R]).length).take
      (cols.take (B.b4.want ft [R]).length).length).map fun c => (c.2.1, c.2.2)] = _
    rw [List.take_length]
  have hcl := cols_of_step P R.drawn (cols.take (B.b4.want ft [R]).length) (hc.trans hw)
  obtain ⟨_, _, k4⟩ := loc_returns P.par d (noDigest R)
    ((cols.take (B.b4.want ft [R]).length).map fun c : OpenedColumn => (c.2.1, c.2.2))
    (frontU_of hP.lin hB hH) hcl
  have hdec := (B.forth hP.goes).2.2.2.1 _ _ _ _ k4
  rw [← hsh] at hdec
  obtain ⟨r, cs, GU, rows, _, _, L⟩ := laid_loc P.par d _ _ _ k4
  have C := carried_loc P.par P.codes k d _ r GU rows _ _ hB L
  rw [← L.loc] at C
  exact ⟨_, (step_iff ft B.b4 d _ [R] cols _).2 ⟨hF, hdec, rfl⟩, C,
    hasU_loc P.par d _ r GU rows hH L⟩

/-- **The sending of o_omega and o_sp.** The OOD answers shown are not tested. -/
theorem returns5 (hP : PlanFacts P.par P.codes sentU layO) (hBO : planOkOwn (parO P) = true)
    (B : Eight P) (ft : Nat) (d : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (h : Facts P k 5 d)
    (hF : B.b5.Fits ft rs cols) :
    ∃ d', B.b5.step ft d rs cols = .ok (d', (B.b5.want ft rs).length) ∧ Facts P k 6 d' := by
  obtain ⟨hB, hH⟩ := h
  obtain ⟨_, _, _, _, e5, _⟩ := blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8
    B.made hP.goes
  have hf := hF.1
  rw [e5] at hf
  obtain ⟨Ra, Rb, rfl⟩ := roundsFit_two' _ _ rs hf
  have hf' := (roundsFit_noDigest _ [Ra, Rb]).trans hf
  obtain ⟨d5, x, ids, s5, B5, U5, O5, l5⟩ := sendO_returns P.par P.codes k (parO P) sentU layO hP
    rfl (parK1_sent P 5 _ _) d _ _ _ _ hB hH (seeds_nz _ _ _ hf')
    (fitB_of_rounds _ _ _ hBO hP.lengths hf')
  have e : d5.loc.oU = d.loc.oU := by rw [l5]
  rw [← e] at B5
  exact ⟨d5, (step_iff ft B.b5 d _ [Ra, Rb] cols _).2
    ⟨hF, (B.forth hP.goes).2.2.2.2.1 _ _ _ _ _ _ _ s5, rfl⟩, B5, U5, O5⟩

/-- **The joinings.** -/
theorem returns6 (hP : PlanFacts P.par P.codes sentU layO) (B : Eight P) (ft : Nat) (d : St)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (h : Facts P k 6 d) (hF : B.b6.Fits ft rs cols) :
    ∃ d', B.b6.step ft d rs cols = .ok (d', (B.b6.want ft rs).length) ∧ Facts P k 7 d' := by
  obtain ⟨hB, hH, hO⟩ := h
  obtain ⟨_, _, _, _, k6⟩ := joins_returns P.par d (rs.map noDigest) hP.two
    (front6_of hP.lin hB hO)
  obtain ⟨GU, GO, L⟩ := joined_joins P.par d _ _ hP.two k6
  have C := carried_joined P.par P.codes k d _ GU GO hB L
  rw [← L.loc] at C
  exact ⟨_, (step_iff ft B.b6 d _ rs cols _).2
    ⟨hF, (B.forth hP.goes).2.2.2.2.2.1 _ _ _ _ k6, rfl⟩, C, hasU_joined P.par d _ GU GO hH hO L,
    hasO_joined P.par d _ GU GO hO L⟩

/-- **"LIN zeta".** -/
theorem returns7 (hP : PlanFacts P.par P.codes sentU layO) (B : Eight P) (ft : Nat) (d : St)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (h : Facts P k 7 d) (hF : B.b7.Fits ft rs cols) :
    ∃ d', B.b7.step ft d rs cols = .ok (d', (B.b7.want ft rs).length) ∧ Facts P k 8 d' := by
  obtain ⟨hB, hH, hO⟩ := h
  obtain ⟨d', hs⟩ := B.on7 hP.goes ft d rs cols hF
  obtain ⟨R, _, _, kz, hz⟩ := B.back7 hP.goes ft d d' rs cols _ hs
  obtain rfl : _ = d' := Option.some.inj ((linZeta_returns d (noDigest R)).symm.trans kz)
  exact ⟨_, hs, ⟨hB.codes, hB.step, hB.key, hB.psi, hB.two, hB.gU, hB.gO⟩, ⟨hH.lay, hH.u⟩,
    ⟨hO.omega, hO.sp, hO.ledger, hO.apart, hO.apartU, hO.apartOU, hO.alone⟩, hz⟩

/-- **"SPLIT".** The scalar shown is not tested. What lies behind it is not said here. -/
theorem returns8 (hP : PlanFacts P.par P.codes sentU layO) (B : Eight P) (ft : Nat) (d : St)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (h : Facts P k 8 d) (hF : B.b8.Fits ft rs cols) :
    ∃ d', B.b8.step ft d rs cols = .ok (d', (B.b8.want ft rs).length) := by
  obtain ⟨hB, hH, hO, hz⟩ := h
  obtain ⟨dd, hdd⟩ := B.rounds8 hP.two
  have hf := hF.1
  rw [hdd] at hf
  obtain ⟨R, rfl, _⟩ := fits_one hf
  obtain ⟨xv, hx⟩ := scalar_of_rounds P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hP.two R hF.1
  obtain ⟨_, _, _, _, _, _, k8⟩ := split_returns P.par d (noDigest R) xv hP.two
    (front8_of hP.lin hB hH hO hz hP.free) hx
  exact ⟨_, (step_iff ft B.b8 _ _ [R] cols _).2
    ⟨hF, (B.forth hP.goes).2.2.2.2.2.2.2 _ _ _ _ k8, rfl⟩⟩

/-! ## The premises are not idle -/

/-- **The library's book-keeping test is too weak for a law of this form.** Take any state that
passes shapeK at the border in front of "(rec_gamma)", and strike its groups: it still passes, and
"(rec_gamma)"'s function returns nothing. So the facts above cannot be had from shapeK. No state
that passes shapeK there is shown in this file: Johnson/Desc/K14/Honest/ShapesBehind.lean has one,
given a run up to there and where the key's sizes fit. -/
theorem shapeK_not_enough (p : Par) (nU nO n : Nat) (s : St) (rs : List Fmt.RoundView)
    (h : shapeK p nU nO n 3 s = true) :
    shapeK p nU nO n 3 { s with st := { s.st with groups := #[] } } = true ∧
      laysRec p { s with st := { s.st with groups := #[] } } rs = none := by
  have h' : shapeM p nU nO 0 s = true := h
  obtain ⟨hU, hM⟩ := (shapeM_iff p nU nO 0 s).1 h'
  obtain ⟨h2, hs, hn, _⟩ := (shapeU_iff p nU 0 s).1 hU
  obtain ⟨m1, _, m3⟩ := (midB_iff nO s).1 hM
  constructor
  · show shapeM p nU nO 0 _ = true
    exact (shapeM_iff p nU nO 0 _).2 ⟨(shapeU_iff p nU 0 _).2 ⟨h2, hs, hn, by simp [rowsOn]⟩,
      (midB_iff nO _).2 ⟨m1, by simp [rowsOn], m3⟩⟩
  · have hj : ∀ g o,
        joinP ({ s with st := { s.st with groups := #[] } } : St) g o false = none := by
      intro g o
      unfold joinP
      rw [if_neg]
      simp [joinL, VerifiableInference.Desc.Ground.ok]
    unfold laysRec
    simp only [Option.bind_eq_bind, hj, Option.bind_none, Option.bind_fun_none]

/-- **Where a seed of the key has the factor 0, "(rec_gamma)"'s step does not return.** -/
theorem rec_rejects (hU : withU P.S = some sentU) (B : Eight P) (ft : Nat) (d d' : St)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat)
    (hz : (d.loc.key.seeds.all (!allZero ·.beta)) = false) :
    B.b3.step ft d rs cols ≠ .ok (d', n) := by
  intro hs
  obtain ⟨_, _, k3⟩ := B.back3 hU ft d d' rs cols n hs
  obtain ⟨hok, _⟩ := laysRecW P.par d d' _ k3
  simp only [VerifiableInference.Desc.Ground.ok, laysRecL, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true] at hok
  rw [hz] at hok
  exact absurd hok.2.1 (by simp)

end Desc.K14.Honest

#print axioms Desc.K14.Honest.facts_first
#print axioms Desc.K14.Honest.returns1
#print axioms Desc.K14.Honest.returns2
#print axioms Desc.K14.Honest.returns3
#print axioms Desc.K14.Honest.returns4
#print axioms Desc.K14.Honest.returns5
#print axioms Desc.K14.Honest.returns6
#print axioms Desc.K14.Honest.returns7
#print axioms Desc.K14.Honest.returns8
#print axioms Desc.K14.Honest.shapeK_not_enough
#print axioms Desc.K14.Honest.rec_rejects
