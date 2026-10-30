-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Honest/StepsOn.lean: the eight sub-protocols of the linear claim's shared rounds:
ONE STEP MORE RETURNS: behind a run of steps up to the sub-protocol in front, the next
sub-protocol's own step returns .ok wherever the step's own tests on rounds and columns are passed.

Johnson/Desc/K14/Honest/ChainSteps.lean shows that all eight steps return one behind the other, from
the first state. Here that is cut sub-protocol by sub-protocol. NOTHING IS ASKED OF A VALUE THAT A
PROVER SENDS: the OOD answers, the scalar and the columns' words are tested by none of the eight. OF
THE VERIFIER's OWN RANDOM VALUES THE PREMISE Block.Fits ASKS SOMETHING: at the two sendings no
sampled seed has the factor 0 as machine words; at "LOC" every sampled location is below 2 ^ logN:
lists of challenges that fail there are shut out by that premise. Of the key "(rec_gamma)" asks: no
seed has the factor 0.

Main names:
  Eight.forth         where a place's function returns (at a sending: where the sending is made),
                      the sub-protocol's decide function returns .ok
  Eight.rounds8       "SPLIT" declares one round
  Public8.on1, …, on6, Eight.on7, Public8.on8   **the step returns.** Asked: Public8; the run of
                      steps up to the sub-protocol in front
                      (Johnson/Desc/K14/Honest/StepsBack.lean); the library's Block.Fits at the
                      rounds and columns handed (Johnson/Top/H0/StepLaws/StepLaws.lean). AT on3
                      BESIDE: the key's sizes fit, and no seed of the key has the factor 0

How. The facts on the state in front come from the run (Johnson/Desc/K14/Honest/RunsTo.lean: at1, …,
at6); from them each function returns by its own law (linPoint_returns, sendU_returns,
laysRec_returns, loc_returns, sendO_returns, joins_returns, linZeta_returns, split_returns).

What is not claimed. That the tests on rounds and columns are passed. What the state behind is
(StepsBack.lean and the files above it say what follows from the step's .ok). Nothing on soundness
or on hiding. This is not completeness of the protocol or of a program.

-/
import Johnson.Desc.K14.Honest.StepsBack
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block OpenedColumn noDigest groupsOf roundsFit_noDigest roundsFit_two'
  step_iff)
open VerifiableInference.Desc.Own (keyFits allZero)
open Desc.K14.Law (parU parO parK1_sent point_fits loc_fits zeta_fits fits_one)

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-- **Where a place's function returns (at a sending: where the sending is made), the sub-protocol's
decide function returns .ok**, whatever groups of columns it is shown. -/
theorem Eight.forth (B : Eight P) (hU : withU P.S = some sentU) :
    (∀ d rs gs d', linPoint P.par d rs = some d' → B.b1.decide d rs gs = .ok d') ∧
      (∀ d d' ra rb x ids gs, SentTo (parU P sentU) (behindU P.par) d d' ra rb x ids →
        B.b2.decide d [ra, rb] gs = .ok d') ∧
      (∀ d rs gs d', laysRec P.par d rs = some d' → B.b3.decide d rs gs = .ok d') ∧
      (∀ d rs gs d', loc P.par d rs gs = some d' → B.b4.decide d rs gs = .ok d') ∧
      (∀ d d' ra rb x ids gs, SentTo (parO P) (behindOmega P.par) d d' ra rb x ids →
        B.b5.decide d [ra, rb] gs = .ok d') ∧
      (∀ d rs gs d', joins P.par d rs = some d' → B.b6.decide d rs gs = .ok d') ∧
      (∀ d rs gs d', linZeta d rs = some d' → B.b7.decide d rs gs = .ok d') ∧
      ∀ d rs gs d', split P.par d rs = some d' → B.b8.decide d rs gs = .ok d' := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := B
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU', hU', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  obtain rfl : sentU = sentU' := Option.some.inj (hU.symm.trans hU')
  exact ⟨fun d rs gs d' h => why_of_some _ h, fun d d' ra rb x ids gs h => h.decides P _ _ _ gs,
    fun d rs gs d' h => why_of_some _ h, fun d rs gs d' h => why_of_some _ h,
    fun d d' ra rb x ids gs h => h.decides P _ _ _ gs, fun d rs gs d' h => why_of_some _ h,
    fun d rs gs d' h => why_of_some _ h, fun d rs gs d' h => why_of_some _ h⟩

variable {d0 : St} {B : Eight P} {ft : Nat} {W : Seen8} {D : States8}

/-- **"LIN point" returns**, wherever the step's own tests on rounds and columns are passed. -/
theorem Public8.on1 (S : Public8 P sentU layO d0) (B : Eight P) (ft : Nat) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (hF : B.b1.Fits ft rs cols) :
    ∃ s', B.b1.step ft d0 rs cols = .ok (s', (B.b1.want ft rs).length) := by
  obtain ⟨R, rfl, _⟩ := point_fits P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made rs hF.1
  have k := linPoint_returns P.par d0 (noDigest R) (by rw [S.codes]; exact S.facts.lengths)
    (by rw [S.codes]; exact S.facts.lin) (by rw [S.codes]; exact S.facts.groupU)
    (by rw [S.codes]; exact S.facts.groupO) S.facts.two
  exact ⟨_, (step_iff ft B.b1 d0 _ [R] cols _).2 ⟨hF, (B.forth S.facts.goes).1 _ _ _ _ k, rfl⟩⟩

/-- **The sending of o_u returns**, behind a run of steps up to "LIN point". -/
theorem Public8.on2 (S : Public8 P sentU layO d0) (u : StepTo1 B ft d0 W D) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (hF : B.b2.Fits ft rs cols) :
    ∃ s', B.b2.step ft D.d1 rs cols = .ok (s', (B.b2.want ft rs).length) := by
  obtain ⟨_, e2, _⟩ := blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
    S.facts.goes
  have hf := hF.1
  rw [e2] at hf
  obtain ⟨Ra, Rb, rfl⟩ := roundsFit_two' _ _ rs hf
  have hf' := (roundsFit_noDigest _ [Ra, Rb]).trans hf
  obtain ⟨d2, x, ids, s2, _⟩ := sendU_returns P.par P.codes d0.loc.key (parU P sentU) sentU layO
    S.facts rfl (parK1_sent P 2 _ sentU) D.d1 _ _ (S.at1 (S.to1 u)).carried (seeds_nz _ _ _ hf')
    (fitB_of_rounds _ _ _ S.planU S.facts.lengths hf')
  exact ⟨d2, (step_iff ft B.b2 D.d1 _ [Ra, Rb] cols _).2
    ⟨hF, (B.forth S.facts.goes).2.1 _ _ _ _ _ _ _ s2, rfl⟩⟩

/-- **"(rec_gamma)" returns**, behind a run of steps up to the sending of o_u, WHERE THE KEY's SIZES
FIT AND NO SEED OF THE KEY HAS THE FACTOR 0. -/
theorem Public8.on3 (S : Public8 P sentU layO d0) (u : StepTo2 B ft d0 W D)
    (hkey : keyFits d0.loc.key P.par.S.fold.index = true)
    (hbeta : (d0.loc.key.seeds.all (!allZero ·.beta)) = true) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : B.b3.Fits ft rs cols) :
    ∃ s', B.b3.step ft D.d2 rs cols = .ok (s', (B.b3.want ft rs).length) := by
  obtain ⟨x, ids, t⟩ := S.to2 u
  have A := S.at2 t
  obtain ⟨_, _, _, _, k⟩ := laysRec_returns P.par D.d2 (rs.map noDigest)
    (frontU_of S.facts.lin A.carried A.hasU) (by rw [A.carried.key]; exact hkey)
    (by rw [A.carried.key]; exact hbeta)
  exact ⟨_, (step_iff ft B.b3 D.d2 _ rs cols _).2
    ⟨hF, (B.forth S.facts.goes).2.2.1 _ _ _ _ k, rfl⟩⟩

/-- **"LOC" returns**, behind a run of steps up to "(rec_gamma)". -/
theorem Public8.on4 (S : Public8 P sentU layO d0) (u : StepTo3 B ft d0 W D) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (hF : B.b4.Fits ft rs cols) :
    ∃ s', B.b4.step ft D.d3 rs cols = .ok (s', (B.b4.want ft rs).length) := by
  obtain ⟨_, _, _, e4, _⟩ := blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
    S.facts.goes
  obtain ⟨R, rfl, hl, _⟩ := loc_fits P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made rs hF.1
  obtain ⟨x, ids, t⟩ := S.to3 u
  have A := S.at3 t
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
  obtain ⟨_, _, k⟩ := loc_returns P.par D.d3 (noDigest R)
    ((cols.take (B.b4.want ft [R]).length).map fun c : OpenedColumn => (c.2.1, c.2.2))
    (frontU_of S.facts.lin A.carried A.hasU) hcl
  have hdec := (B.forth S.facts.goes).2.2.2.1 _ _ _ _ k
  rw [← hsh] at hdec
  exact ⟨_, (step_iff ft B.b4 D.d3 _ [R] cols _).2 ⟨hF, hdec, rfl⟩⟩

/-- **The sending of o_omega and o_sp returns**, behind a run of steps up to "LOC". -/
theorem Public8.on5 (S : Public8 P sentU layO d0) (u : StepTo4 B ft d0 W D) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (hF : B.b5.Fits ft rs cols) :
    ∃ s', B.b5.step ft D.d4 rs cols = .ok (s', (B.b5.want ft rs).length) := by
  obtain ⟨_, _, _, _, e5, _⟩ := blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8
    B.made S.facts.goes
  have hf := hF.1
  rw [e5] at hf
  obtain ⟨Ra, Rb, rfl⟩ := roundsFit_two' _ _ rs hf
  have hf' := (roundsFit_noDigest _ [Ra, Rb]).trans hf
  obtain ⟨x, ids, t⟩ := S.to4 u
  have A := S.at4 t
  obtain ⟨d5, x', ids', s5, _⟩ := sendO_returns P.par P.codes d0.loc.key (parO P) sentU layO
    S.facts rfl (parK1_sent P 5 _ _) D.d4 _ _ _ _ A.carried A.hasU (seeds_nz _ _ _ hf')
    (fitB_of_rounds _ _ _ S.planO S.facts.lengths hf')
  exact ⟨d5, (step_iff ft B.b5 D.d4 _ [Ra, Rb] cols _).2
    ⟨hF, (B.forth S.facts.goes).2.2.2.2.1 _ _ _ _ _ _ _ s5, rfl⟩⟩

/-- **The joinings return**, behind a run of steps up to the second sending. -/
theorem Public8.on6 (S : Public8 P sentU layO d0) (u : StepTo5 B ft d0 W D) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (hF : B.b6.Fits ft rs cols) :
    ∃ s', B.b6.step ft D.d5 rs cols = .ok (s', (B.b6.want ft rs).length) := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to5 u
  have A := S.at5 t
  obtain ⟨_, _, _, _, k⟩ := joins_returns P.par D.d5 (rs.map noDigest) S.facts.two
    (front6_of S.facts.lin A.carried A.hasO)
  exact ⟨_, (step_iff ft B.b6 D.d5 _ rs cols _).2
    ⟨hF, (B.forth S.facts.goes).2.2.2.2.2.1 _ _ _ _ k, rfl⟩⟩

/-- **"LIN zeta" returns**, at any state. -/
theorem Eight.on7 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d : St)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hF : B.b7.Fits ft rs cols) :
    ∃ s', B.b7.step ft d rs cols = .ok (s', (B.b7.want ft rs).length) := by
  obtain ⟨R, rfl, _⟩ := zeta_fits P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made rs hF.1
  exact ⟨_, (step_iff ft B.b7 d _ [R] cols _).2
    ⟨hF, (B.forth hU).2.2.2.2.2.2.1 _ _ _ _ (linZeta_returns d (noDigest R)), rfl⟩⟩

/-- Where the shape has two codes, "SPLIT" declares one round. -/
theorem Eight.rounds8 (B : Eight P) (hS : P.S.sharedSplitNeeded = true) :
    ∃ d, B.b8.rounds = [d] := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := B
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  refine ⟨{ entry := { name := "SPLIT", work := 0, msg := 24 } }, ?_⟩
  show (((entries P).drop 3).take (if P.S.sharedSplitNeeded then 1 else 0)).map
    (fun e => ({ entry := e } : Fmt.DeclaredRound)) = _
  unfold entries rounds whys
  rw [if_pos hS, if_pos hS]
  rfl

/-- **"SPLIT" returns**, behind a run of steps up to "LIN zeta". The scalar shown is not tested. -/
theorem Public8.on8 (S : Public8 P sentU layO d0) (u : StepTo7 B ft d0 W D) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (hF : B.b8.Fits ft rs cols) :
    ∃ s', B.b8.step ft D.d7 rs cols = .ok (s', (B.b8.want ft rs).length) := by
  obtain ⟨x, ids, x', ids', t⟩ := S.to7 u
  have A := S.at6 t.front
  have e7 : D.d7 = { D.d6 with loc := { D.d6.loc with zFd := drawn W.view.r7 } } := t.d7_eq
  obtain ⟨dd, hdd⟩ := B.rounds8 S.facts.two
  have hf := hF.1
  rw [hdd] at hf
  obtain ⟨R, rfl, _⟩ := fits_one hf
  obtain ⟨xv, hx⟩ := scalar_of_rounds P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made S.facts.two R
    hF.1
  have B6 := A.carried
  have U7 : HasU P.par { D.d6 with loc := { D.d6.loc with zFd := drawn W.view.r7 } } :=
    ⟨A.hasU.lay, A.hasU.u⟩
  have O7 : HasO P.par { D.d6 with loc := { D.d6.loc with zFd := drawn W.view.r7 } } :=
    ⟨A.hasO.omega, A.hasO.sp, A.hasO.ledger, A.hasO.apart, A.hasO.apartU, A.hasO.apartOU,
      A.hasO.alone⟩
  have F8 : Front8 P.par { D.d6 with loc := { D.d6.loc with zFd := drawn W.view.r7 } } :=
    front8_of S.facts.lin ⟨B6.codes, B6.step, B6.key, B6.psi, B6.two, B6.gU, B6.gO⟩ U7 O7 t.zeta
      S.facts.free
  obtain ⟨_, _, _, _, _, _, k⟩ := split_returns P.par
    { D.d6 with loc := { D.d6.loc with zFd := drawn W.view.r7 } } (noDigest R) xv S.facts.two F8 hx
  rw [e7]
  exact ⟨_, (step_iff ft B.b8 _ _ [R] cols _).2
    ⟨hF, (B.forth S.facts.goes).2.2.2.2.2.2.2 _ _ _ _ k, rfl⟩⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.Eight.forth
#print axioms Desc.K14.Honest.Public8.on1
#print axioms Desc.K14.Honest.Public8.on2
#print axioms Desc.K14.Honest.Public8.on3
#print axioms Desc.K14.Honest.Public8.on4
#print axioms Desc.K14.Honest.Public8.on5
#print axioms Desc.K14.Honest.Public8.on6
#print axioms Desc.K14.Honest.Eight.on7
#print axioms Desc.K14.Honest.Eight.rounds8
#print axioms Desc.K14.Honest.Public8.on8
