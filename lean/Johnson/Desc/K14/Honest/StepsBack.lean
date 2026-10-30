--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/StepsBack.lean: the eight sub-protocols of the linear claim's shared rounds:
from the format's own step back to the kind's functions.

A sub-protocol's decision is its step (Johnson/Desc/Block.lean: Block.step), and a chain's decision
is the fold of the steps (foldBlocks). The files beside this one speak of a run of the kind's
functions (Johnson/Desc/K14/Honest/RunsTo.lean: To1, …, To8: linPoint, decideSend with the kind's
note, laysRec, loc, joins, linZeta, split have returned). Johnson/Desc/K14/Honest/ChainSteps.lean
goes from these to the steps. This file goes back: where a step has returned .ok, the function has
returned, at the rounds without the sealed digest, and the round has the form that the format's test
gives.

Main names:
  Eight P             the eight sub-protocols that the kind's text makes at P (blocks P), at the
                      kind's own type of claims
  Seen8, Seen8.view   the eight rounds as a view holds them, with the columns that "LOC" reads; what
                      the decide functions are handed of them
  Eight.fronts, step_plain_back   what the first, the second and the fifth are made of; a step of a
                      sub-protocol whose rounds read no column
  Eight.back1, …, back8   **sub-protocol by sub-protocol, at any state**: from the step's .ok: how
                      many rounds it was handed; how many columns it took; the function's return (at
                      a sending: the decide function's .ok and the test on the two rounds); at
                      "LOC": the columns taken are, in key, position and width, those that the round
                      reads
  Eight.sentU_back, sentO_back   at a sending, with the facts in front of it: what the sending is
                      made of (SentTo). Forwards by sendU_returns and sendO_returns, and then: .ok
                      is injective
  StepTo1, …, StepTo8   a run of steps up to a sub-protocol: the first so many Block.step equations,
                      each at whatever columns lie ahead, and nothing else
  Public8.to1, …, to8   **from a run of steps to a run of the kind's functions**
  Eight.peel1, …, peel8, fold_nil   one sub-protocol off the front of a fold

What is assumed, as premises: at back1, …, back8: what goes out with o_u (withU); at "SPLIT": two
codes. At to1, …, to8: Public8. A run of steps fixes no random value, no value sent and no later
sub-protocol's return: it is a conjunction of the verifier's own equations. It does EXCLUDE what
these equations refuse: at the two sendings a sampled seed whose factor is 0; a location not below
2 ^ logN; and from StepTo3 on a key whose sizes do not fit or one of whose seeds has the factor 0.

What is not claimed. That a step returns .ok: eight_steps_hold (ChainSteps.lean). Nothing on the
front sub-protocol, the two proximity tests and the chain's closing. NOTHING ON THE CARRYING TO
ANOTHER TYPE OF CLAIMS: a proof file's IOP as written in Lean holds the shared chain carried to the
file's type of claims (Johnson/Desc/K14/Law/SharedFlat.lean): its members are these eight carried,
behind a front sub-protocol; that a carried sub-protocol has the same step, and a fold over carried
ones the same return, is not in this file. Nothing on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.RunsTo
import Johnson.Desc.K14.Honest.ChainSteps
import Johnson.Desc.K14.Law.BlocksSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block OpenedColumn roundsFit noDigest groupsOf foldBlocks roundsFit_noDigest
  roundsFit_two')
open VerifiableInference.Desc.Sound (step_ok_iff groupsAt roundsFit_len foldBlocks_cons_ok)
open VerifiableInference.Desc.First.Att.P (groupsOf_none)
open VerifiableInference.Desc.K1 (planOkOwn)
open Desc.K14.Law (parU parO parK1_sent why_some quiet_of_blocks loc_of_blocks zeta_of_blocks
  decidesBySplit_of_blocks split_one point_fits loc_fits zeta_fits)

/-! ## The eight, and what a view holds for them -/

/-- The eight sub-protocols that the kind's text makes at the parameters P (blocks P), at the kind's
own type of claims. A proof file's IOP as written in Lean holds them carried to another type. -/
structure Eight (P : P14) where
  b1 : Block St Unit
  b2 : Block St Unit
  b3 : Block St Unit
  b4 : Block St Unit
  b5 : Block St Unit
  b6 : Block St Unit
  b7 : Block St Unit
  b8 : Block St Unit
  made : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]

/-- The eight rounds as a view holds them, and the columns that "LOC" reads. -/
structure Seen8 where
  R1 : Fmt.RoundView
  R2a : Fmt.RoundView
  R2b : Fmt.RoundView
  R4 : Fmt.RoundView
  R5a : Fmt.RoundView
  R5b : Fmt.RoundView
  R7 : Fmt.RoundView
  R8 : Fmt.RoundView
  cs : List OpenedColumn

/-- What the decide functions are handed of it: each round without the sealed digest; each column as
its position and its words; no round at the two sub-protocols that declare none. -/
def Seen8.view (W : Seen8) : View8 :=
  ⟨noDigest W.R1, noDigest W.R2a, noDigest W.R2b, noDigest W.R4, noDigest W.R5a, noDigest W.R5b,
    noDigest W.R7, noDigest W.R8, W.cs.map fun c => (c.2.1, c.2.2), [], []⟩

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-! ## Sub-protocol by sub-protocol, at any state -/

/-- What the first, the second and the fifth are made of. -/
theorem Eight.fronts (B : Eight P) (hU : withU P.S = some sentU) :
    (∀ d rs gs d', B.b1.decide d rs gs = .ok d' → linPoint P.par d rs = some d') ∧
      (∃ n f g, B.b2 = sendAt P n (parU P sentU) f g (behindU P.par)) ∧
      ∃ n f g, B.b5 = sendAt P n (parO P) f g (behindOmega P.par) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := B
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU', hU', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  obtain rfl : sentU = sentU' := Option.some.inj (hU.symm.trans hU')
  exact ⟨fun d rs gs d' h => why_some h, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩

/-- A step of a sub-protocol whose rounds read no column: the test on the rounds, no column taken,
and the decide function's .ok. -/
theorem step_plain_back (b : Block St Unit) (hb : ∀ r ∈ b.rounds, ReadsNone r) (ft : Nat)
    (s s' : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat)
    (h : b.step ft s rs cols = .ok (s', n)) :
    roundsFit b.rounds rs = true ∧ n = 0 ∧ b.decide s (rs.map noDigest) [] = .ok s' := by
  obtain ⟨hf, _, hn, hd⟩ := (step_ok_iff ft b s s' rs cols n).1 h
  have hg := groupsOf_none ft b.rounds (rs.map (·.drawn)) hb
  rw [hg] at hn
  unfold groupsAt at hd
  rw [hg] at hd
  exact ⟨hf, hn, hd⟩

/-- **"LIN point".** -/
theorem Eight.back1 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d d' : St)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) (h : B.b1.step ft d rs c = .ok (d', n)) :
    ∃ R, rs = [R] ∧ n = 0 ∧ linPoint P.par d [noDigest R] = some d' ∧
      (drawn (noDigest R)).length = P.par.S.kCol := by
  obtain ⟨p1, _⟩ := blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hU
  obtain ⟨hf, hn, hd⟩ := step_plain_back B.b1 p1 ft d d' rs c n h
  obtain ⟨R, rfl, a1, _⟩ := point_fits P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made rs hf
  exact ⟨R, rfl, hn, (B.fronts hU).1 _ _ _ _ hd, by
    unfold drawn
    rw [List.length_map]
    exact a1⟩

/-- **The sending of o_u.** -/
theorem Eight.back2 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d d' : St)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) (h : B.b2.step ft d rs c = .ok (d', n)) :
    ∃ Ra Rb, rs = [Ra, Rb] ∧ n = 0 ∧
      roundsFit (VerifiableInference.Desc.K1.rounds (parU P sentU))
        [noDigest Ra, noDigest Rb] = true ∧
      B.b2.decide d [noDigest Ra, noDigest Rb] [] = .ok d' := by
  obtain ⟨_, e2, _⟩ := blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hU
  obtain ⟨hf, hn, hd⟩ := step_plain_back B.b2 (by rw [e2]; exact send_plain _) ft d d' rs c n h
  rw [e2] at hf
  obtain ⟨Ra, Rb, rfl⟩ := roundsFit_two' _ _ rs hf
  exact ⟨Ra, Rb, rfl, hn, (roundsFit_noDigest _ [Ra, Rb]).trans hf, hd⟩

/-- **"(rec_gamma)".** -/
theorem Eight.back3 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d d' : St)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) (h : B.b3.step ft d rs c = .ok (d', n)) :
    rs = [] ∧ n = 0 ∧ laysRec P.par d [] = some d' := by
  obtain ⟨_, _, e3, _⟩ := blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hU
  obtain ⟨hf, hn, hd⟩ := step_plain_back B.b3 (by rw [e3]; intro r hr; cases hr) ft d d' rs c n h
  have hl := roundsFit_len _ _ hf
  rw [e3] at hl
  obtain rfl : rs = [] := List.length_eq_zero_iff.1 hl
  exact ⟨rfl, hn,
    (quiet_of_blocks P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made).1 _ _ _ _ hd⟩

/-- **"LOC".** The columns taken are, in key, position and width, those that the round reads. -/
theorem Eight.back4 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d d' : St)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) (h : B.b4.step ft d rs c = .ok (d', n)) :
    ∃ R, rs = [R] ∧ R.drawn.poss.length = P.S.fold.columns ∧
      (c.take n).map (fun x => (x.1, x.2.1, x.2.2.length)) =
        (Fmt.listOf (R.drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map (fun x =>
          (Fmt.storedKey P.item, x, P.S.fold.index.rows)) ∧
      (c.take n).length = n ∧
      loc P.par d [noDigest R] [(c.take n).map fun x => (x.2.1, x.2.2)] = some d' := by
  obtain ⟨_, _, _, e4, _⟩ := blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hU
  obtain ⟨hf, hc, hn, hd⟩ := (step_ok_iff ft B.b4 d d' rs c n).1 h
  obtain ⟨R, rfl, hl, _⟩ := loc_fits P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made rs hf
  have hg : groupsOf ft B.b4.rounds ([R].map (·.drawn)) =
      [(Fmt.listOf (R.drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
        (Fmt.storedKey P.item, x, P.S.fold.index.rows)] := by
    rw [e4]
    exact loc_groups P ft R.drawn hl
  rw [hg] at hc hn
  have hc' : (c.take n).map (fun x => (x.1, x.2.1, x.2.2.length)) =
      (Fmt.listOf (R.drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map (fun x =>
        (Fmt.storedKey P.item, x, P.S.fold.index.rows)) := by simpa using hc
  have hlen : (c.take n).length = n := by
    have e := congrArg List.length hc'
    rw [List.length_map] at e
    rw [e]
    simpa using hn.symm
  refine ⟨R, rfl, hl, hc', hlen, ?_⟩
  unfold groupsAt at hd
  rw [hg] at hd
  have e1 : ((Fmt.listOf (R.drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
      (Fmt.storedKey P.item, x, P.S.fold.index.rows)).length = (c.take n).length := by
    rw [← hc', List.length_map]
  simp only [List.map_cons, List.map_nil, e1] at hd
  have hd' : B.b4.decide d [noDigest R]
      [((c.take n).take (c.take n).length).map fun x => (x.2.1, x.2.2)] = .ok d' := hd
  rw [List.take_length] at hd'
  exact loc_of_blocks P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made _ _ _ _ hd'

/-- **The sending of o_omega and o_sp.** -/
theorem Eight.back5 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d d' : St)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) (h : B.b5.step ft d rs c = .ok (d', n)) :
    ∃ Ra Rb, rs = [Ra, Rb] ∧ n = 0 ∧
      roundsFit (VerifiableInference.Desc.K1.rounds (parO P)) [noDigest Ra, noDigest Rb] = true ∧
      B.b5.decide d [noDigest Ra, noDigest Rb] [] = .ok d' := by
  obtain ⟨_, _, _, _, e5, _⟩ :=
    blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hU
  obtain ⟨hf, hn, hd⟩ := step_plain_back B.b5 (by rw [e5]; exact send_plain _) ft d d' rs c n h
  rw [e5] at hf
  obtain ⟨Ra, Rb, rfl⟩ := roundsFit_two' _ _ rs hf
  exact ⟨Ra, Rb, rfl, hn, (roundsFit_noDigest _ [Ra, Rb]).trans hf, hd⟩

/-- **The joinings.** -/
theorem Eight.back6 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d d' : St)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) (h : B.b6.step ft d rs c = .ok (d', n)) :
    rs = [] ∧ n = 0 ∧ joins P.par d [] = some d' := by
  obtain ⟨_, _, _, _, _, e6, _⟩ :=
    blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hU
  obtain ⟨hf, hn, hd⟩ := step_plain_back B.b6 (by rw [e6]; intro r hr; cases hr) ft d d' rs c n h
  have hl := roundsFit_len _ _ hf
  rw [e6] at hl
  obtain rfl : rs = [] := List.length_eq_zero_iff.1 hl
  exact ⟨rfl, hn,
    (quiet_of_blocks P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made).2 _ _ _ _ hd⟩

/-- **"LIN zeta".** -/
theorem Eight.back7 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat) (d d' : St)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) (h : B.b7.step ft d rs c = .ok (d', n)) :
    ∃ R, rs = [R] ∧ n = 0 ∧ linZeta d [noDigest R] = some d' ∧
      (drawn (noDigest R)).length = P.par.S.kRow := by
  obtain ⟨_, _, _, _, _, _, p7, _⟩ :=
    blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hU
  obtain ⟨hf, hn, hd⟩ := step_plain_back B.b7 p7 ft d d' rs c n h
  obtain ⟨R, rfl, a1, _⟩ := zeta_fits P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made rs hf
  exact ⟨R, rfl, hn, zeta_of_blocks P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made _ _ _ _ hd, by
    unfold drawn
    rw [List.length_map]
    exact a1⟩

/-- **"SPLIT"**, where the shape has two codes. -/
theorem Eight.back8 (B : Eight P) (hU : withU P.S = some sentU)
    (hS : P.S.sharedSplitNeeded = true) (ft : Nat) (d d' : St) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (n : Nat) (h : B.b8.step ft d rs c = .ok (d', n)) :
    ∃ R, rs = [R] ∧ n = 0 ∧ split P.par d [noDigest R] = some d' := by
  obtain ⟨_, _, _, _, _, _, _, p8⟩ :=
    blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hU
  obtain ⟨_, hn, hd⟩ := step_plain_back B.b8 p8 ft d d' rs c n h
  have k := decidesBySplit_of_blocks P B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made _ _ _ _ hd
  obtain ⟨r, hr⟩ := split_one P.par d d' _ hS k
  match rs, hr, k with
  | [R], _, k => exact ⟨R, rfl, hn, k⟩

/-! ## The two sendings: from the decide function's .ok to what a sending is made of -/

/-- **The sending of o_u**, with the facts in front of it. -/
theorem Eight.sentU_back (B : Eight P) (hP : PlanFacts P.par P.codes sentU layO)
    (hBU : planOkOwn (parU P sentU) = true) (k : TableKey) (d d' : St) (ra rb : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hB : Carried P.par P.codes k d [] [])
    (hf : roundsFit (VerifiableInference.Desc.K1.rounds (parU P sentU)) [ra, rb] = true)
    (hd : B.b2.decide d [ra, rb] gs = .ok d') :
    ∃ x ids, SentTo (parU P sentU) (behindU P.par) d d' ra rb x ids := by
  obtain ⟨d2, x, ids, s2, _⟩ := sendU_returns P.par P.codes k (parU P sentU) sentU layO hP rfl
    (parK1_sent P 2 _ sentU) d ra rb hB (seeds_nz _ _ _ hf)
    (fitB_of_rounds _ _ _ hBU hP.lengths hf)
  obtain ⟨n, f, g, e⟩ := (B.fronts hP.goes).2.1
  rw [e] at hd
  obtain rfl : d2 = d' := Except.ok.inj ((s2.decides P n f g gs).symm.trans hd)
  exact ⟨x, ids, s2⟩

/-- **The sending of o_omega and o_sp**, with the facts in front of it. -/
theorem Eight.sentO_back (B : Eight P) (hP : PlanFacts P.par P.codes sentU layO)
    (hBO : planOkOwn (parO P) = true) (k : TableKey) (d d' : St) (ra rb : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (mU mO : List Nat)
    (hB : Carried P.par P.codes k d mU mO) (hH : HasU P.par d)
    (hf : roundsFit (VerifiableInference.Desc.K1.rounds (parO P)) [ra, rb] = true)
    (hd : B.b5.decide d [ra, rb] gs = .ok d') :
    ∃ x ids, SentTo (parO P) (behindOmega P.par) d d' ra rb x ids := by
  obtain ⟨d5, x, ids, s5, _⟩ := sendO_returns P.par P.codes k (parO P) sentU layO hP rfl
    (parK1_sent P 5 _ _) d ra rb mU mO hB hH (seeds_nz _ _ _ hf)
    (fitB_of_rounds _ _ _ hBO hP.lengths hf)
  obtain ⟨n, f, g, e⟩ := (B.fronts hP.goes).2.2
  rw [e] at hd
  obtain rfl : d5 = d' := Except.ok.inj ((s5.decides P n f g gs).symm.trans hd)
  exact ⟨x, ids, s5⟩

/-! ## A run of steps up to a sub-protocol -/

/-- A run of steps up to "LIN point": the sub-protocol's own step has returned .ok, at whatever
columns lie ahead. -/
structure StepTo1 (B : Eight P) (ft : Nat) (d0 : St) (W : Seen8) (D : States8) : Prop where
  s1 : ∃ c n, B.b1.step ft d0 [W.R1] c = .ok (D.d1, n)

/-- A run of steps up to the sending of o_u. -/
structure StepTo2 (B : Eight P) (ft : Nat) (d0 : St) (W : Seen8) (D : States8) : Prop where
  front : StepTo1 B ft d0 W D
  s2 : ∃ c n, B.b2.step ft D.d1 [W.R2a, W.R2b] c = .ok (D.d2, n)

/-- A run of steps up to "(rec_gamma)". -/
structure StepTo3 (B : Eight P) (ft : Nat) (d0 : St) (W : Seen8) (D : States8) : Prop where
  front : StepTo2 B ft d0 W D
  s3 : ∃ c n, B.b3.step ft D.d2 [] c = .ok (D.d3, n)

/-- A run of steps up to "LOC", whose step takes just the columns W.cs. -/
structure StepTo4 (B : Eight P) (ft : Nat) (d0 : St) (W : Seen8) (D : States8) : Prop where
  front : StepTo3 B ft d0 W D
  s4 : ∃ c, B.b4.step ft D.d3 [W.R4] (W.cs ++ c) = .ok (D.d4, W.cs.length)

/-- A run of steps up to the sending of o_omega and o_sp. -/
structure StepTo5 (B : Eight P) (ft : Nat) (d0 : St) (W : Seen8) (D : States8) : Prop where
  front : StepTo4 B ft d0 W D
  s5 : ∃ c n, B.b5.step ft D.d4 [W.R5a, W.R5b] c = .ok (D.d5, n)

/-- A run of steps up to the joinings. -/
structure StepTo6 (B : Eight P) (ft : Nat) (d0 : St) (W : Seen8) (D : States8) : Prop where
  front : StepTo5 B ft d0 W D
  s6 : ∃ c n, B.b6.step ft D.d5 [] c = .ok (D.d6, n)

/-- A run of steps up to "LIN zeta". -/
structure StepTo7 (B : Eight P) (ft : Nat) (d0 : St) (W : Seen8) (D : States8) : Prop where
  front : StepTo6 B ft d0 W D
  s7 : ∃ c n, B.b7.step ft D.d6 [W.R7] c = .ok (D.d7, n)

/-- A run of steps up to "SPLIT": all eight. -/
structure StepTo8 (B : Eight P) (ft : Nat) (d0 : St) (W : Seen8) (D : States8) : Prop where
  front : StepTo7 B ft d0 W D
  s8 : ∃ c n, B.b8.step ft D.d7 [W.R8] c = .ok (D.d8, n)

variable {d0 : St} {B : Eight P} {ft : Nat} {W : Seen8} {D : States8}

/-! ## From a run of steps to a run of the kind's functions -/

/-- **Up to "LIN point".** -/
theorem Public8.to1 (S : Public8 P sentU layO d0) (u : StepTo1 B ft d0 W D) :
    To1 P d0 W.view D := by
  obtain ⟨c, n, h⟩ := u.s1
  obtain ⟨R, hr, _, k, hp⟩ := B.back1 S.facts.goes ft d0 D.d1 [W.R1] c n h
  obtain rfl : W.R1 = R := by simpa using hr
  exact ⟨k, hp⟩

/-- **Up to the sending of o_u.** x, ids: what decideSend has returned. -/
theorem Public8.to2 (S : Public8 P sentU layO d0) (u : StepTo2 B ft d0 W D) :
    ∃ x ids, To2 P sentU d0 W.view { D with x2 := x, ids2 := ids } := by
  have u1 := S.to1 u.front
  obtain ⟨c, n, h⟩ := u.s2
  obtain ⟨Ra, Rb, hr, _, hf, hd⟩ := B.back2 S.facts.goes ft D.d1 D.d2 _ c n h
  obtain ⟨rfl, rfl⟩ : W.R2a = Ra ∧ W.R2b = Rb := by simpa using hr
  obtain ⟨x, ids, s2⟩ := B.sentU_back S.facts S.planU d0.loc.key D.d1 D.d2 _ _ []
    (S.at1 u1).carried hf hd
  exact ⟨x, ids, ⟨u1.k1, u1.point⟩, s2, hf⟩

/-- **Up to "(rec_gamma)".** -/
theorem Public8.to3 (S : Public8 P sentU layO d0) (u : StepTo3 B ft d0 W D) :
    ∃ x ids, To3 P sentU d0 W.view { D with x2 := x, ids2 := ids } := by
  obtain ⟨x, ids, u2⟩ := S.to2 u.front
  obtain ⟨c, n, h⟩ := u.s3
  exact ⟨x, ids, u2, (B.back3 S.facts.goes ft D.d2 D.d3 [] c n h).2.2⟩

/-- **Up to "LOC".** -/
theorem Public8.to4 (S : Public8 P sentU layO d0) (u : StepTo4 B ft d0 W D) :
    ∃ x ids, To4 P sentU d0 W.view { D with x2 := x, ids2 := ids } := by
  obtain ⟨x, ids, u3⟩ := S.to3 u.front
  obtain ⟨c, h⟩ := u.s4
  obtain ⟨R, hr, hl, _, _, k⟩ := B.back4 S.facts.goes ft D.d3 D.d4 _ _ _ h
  obtain rfl : W.R4 = R := by simpa using hr
  rw [List.take_left' rfl] at k
  exact ⟨x, ids, u3, k, hl⟩

/-- **Up to the sending of o_omega and o_sp.** -/
theorem Public8.to5 (S : Public8 P sentU layO d0) (u : StepTo5 B ft d0 W D) :
    ∃ x ids x' ids',
      To5 P sentU d0 W.view { D with x2 := x, ids2 := ids, x5 := x', ids5 := ids' } := by
  obtain ⟨x, ids, u4⟩ := S.to4 u.front
  obtain ⟨c, n, h⟩ := u.s5
  obtain ⟨Ra, Rb, hr, _, hf, hd⟩ := B.back5 S.facts.goes ft D.d4 D.d5 _ c n h
  obtain ⟨rfl, rfl⟩ : W.R5a = Ra ∧ W.R5b = Rb := by simpa using hr
  have A := S.at4 u4
  obtain ⟨x', ids', s5⟩ := B.sentO_back S.facts S.planO d0.loc.key D.d4 D.d5 _ _ [] _ _ A.carried
    A.hasU hf hd
  exact ⟨x, ids, x', ids',
    ⟨⟨⟨⟨u4.front.front.front.k1, u4.front.front.front.point⟩, u4.front.front.s2,
      u4.front.front.fitsU⟩, u4.front.k3⟩, u4.k4, u4.locs⟩, s5, hf⟩

/-- **Up to the joinings.** -/
theorem Public8.to6 (S : Public8 P sentU layO d0) (u : StepTo6 B ft d0 W D) :
    ∃ x ids x' ids',
      To6 P sentU d0 W.view { D with x2 := x, ids2 := ids, x5 := x', ids5 := ids' } := by
  obtain ⟨x, ids, x', ids', u5⟩ := S.to5 u.front
  obtain ⟨c, n, h⟩ := u.s6
  exact ⟨x, ids, x', ids', u5, (B.back6 S.facts.goes ft D.d5 D.d6 [] c n h).2.2⟩

/-- **Up to "LIN zeta".** -/
theorem Public8.to7 (S : Public8 P sentU layO d0) (u : StepTo7 B ft d0 W D) :
    ∃ x ids x' ids',
      To7 P sentU d0 W.view { D with x2 := x, ids2 := ids, x5 := x', ids5 := ids' } := by
  obtain ⟨x, ids, x', ids', u6⟩ := S.to6 u.front
  obtain ⟨c, n, h⟩ := u.s7
  obtain ⟨R, hr, _, k, hz⟩ := B.back7 S.facts.goes ft D.d6 D.d7 _ c n h
  obtain rfl : W.R7 = R := by simpa using hr
  exact ⟨x, ids, x', ids', u6, k, hz⟩

/-- **Up to "SPLIT": the whole run.** -/
theorem Public8.to8 (S : Public8 P sentU layO d0) (u : StepTo8 B ft d0 W D) :
    ∃ x ids x' ids',
      To8 P sentU d0 W.view { D with x2 := x, ids2 := ids, x5 := x', ids5 := ids' } := by
  obtain ⟨x, ids, x', ids', u7⟩ := S.to7 u.front
  obtain ⟨c, n, h⟩ := u.s8
  obtain ⟨R, hr, _, k⟩ := B.back8 S.facts.goes S.facts.two ft D.d7 D.d8 _ c n h
  obtain rfl : W.R8 = R := by simpa using hr
  exact ⟨x, ids, x', ids', u7, k⟩

/-! ## From the fold: one sub-protocol off the front -/

/-- A list whose first so many members are one member. -/
theorem cons_of_take {α : Type} {l : List α} {n : Nat} {a : α} (h : l.take n = [a]) :
    l = a :: l.drop n := by
  have e := List.take_append_drop n l
  rw [h] at e
  exact e.symm

/-- A list whose first so many members are two members. -/
theorem cons2_of_take {α : Type} {l : List α} {n : Nat} {a b : α} (h : l.take n = [a, b]) :
    l = a :: b :: l.drop n := by
  have e := List.take_append_drop n l
  rw [h] at e
  exact e.symm

/-- "LIN point" off the front of a fold. -/
theorem Eight.peel1 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat)
    (l : List (Block St Unit)) (d : St) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (r : St × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft (B.b1 :: l) d rs c = .ok r) :
    ∃ R d' rs', rs = R :: rs' ∧ B.b1.step ft d [R] c = .ok (d', 0) ∧
      foldBlocks ft l d' rs' c = .ok r := by
  obtain ⟨d', k, _, hs, hf⟩ := foldBlocks_cons_ok ft B.b1 l d rs c r h
  obtain ⟨R, hr, rfl, _⟩ := B.back1 hU ft d d' _ c k hs
  rw [hr] at hs
  rw [List.drop_zero] at hf
  exact ⟨R, d', _, cons_of_take hr, hs, hf⟩

/-- The sending of o_u off the front of a fold. -/
theorem Eight.peel2 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat)
    (l : List (Block St Unit)) (d : St) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (r : St × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft (B.b2 :: l) d rs c = .ok r) :
    ∃ Ra Rb d' rs', rs = Ra :: Rb :: rs' ∧ B.b2.step ft d [Ra, Rb] c = .ok (d', 0) ∧
      foldBlocks ft l d' rs' c = .ok r := by
  obtain ⟨d', k, _, hs, hf⟩ := foldBlocks_cons_ok ft B.b2 l d rs c r h
  obtain ⟨Ra, Rb, hr, rfl, _⟩ := B.back2 hU ft d d' _ c k hs
  rw [hr] at hs
  rw [List.drop_zero] at hf
  exact ⟨Ra, Rb, d', _, cons2_of_take hr, hs, hf⟩

/-- "(rec_gamma)" off the front of a fold. -/
theorem Eight.peel3 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat)
    (l : List (Block St Unit)) (d : St) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (r : St × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft (B.b3 :: l) d rs c = .ok r) :
    ∃ d', B.b3.step ft d [] c = .ok (d', 0) ∧ foldBlocks ft l d' rs c = .ok r := by
  obtain ⟨_, _, e3, _⟩ := blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hU
  obtain ⟨d', k, _, hs, hf⟩ := foldBlocks_cons_ok ft B.b3 l d rs c r h
  obtain ⟨hr, rfl, _⟩ := B.back3 hU ft d d' _ c k hs
  rw [hr] at hs
  rw [List.drop_zero, e3] at hf
  exact ⟨d', hs, hf⟩

/-- "LOC" off the front of a fold: it takes the columns cs. -/
theorem Eight.peel4 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat)
    (l : List (Block St Unit)) (d : St) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (r : St × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft (B.b4 :: l) d rs c = .ok r) :
    ∃ R d' rs' cs c', rs = R :: rs' ∧ c = cs ++ c' ∧
      B.b4.step ft d [R] (cs ++ c') = .ok (d', cs.length) ∧ foldBlocks ft l d' rs' c' = .ok r := by
  obtain ⟨d', k, _, hs, hf⟩ := foldBlocks_cons_ok ft B.b4 l d rs c r h
  obtain ⟨R, hr, _, _, hlen, _⟩ := B.back4 hU ft d d' _ c k hs
  rw [hr] at hs
  refine ⟨R, d', _, c.take k, c.drop k, cons_of_take hr, (List.take_append_drop k c).symm, ?_, hf⟩
  rw [List.take_append_drop, hlen]
  exact hs

/-- The sending of o_omega and o_sp off the front of a fold. -/
theorem Eight.peel5 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat)
    (l : List (Block St Unit)) (d : St) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (r : St × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft (B.b5 :: l) d rs c = .ok r) :
    ∃ Ra Rb d' rs', rs = Ra :: Rb :: rs' ∧ B.b5.step ft d [Ra, Rb] c = .ok (d', 0) ∧
      foldBlocks ft l d' rs' c = .ok r := by
  obtain ⟨d', k, _, hs, hf⟩ := foldBlocks_cons_ok ft B.b5 l d rs c r h
  obtain ⟨Ra, Rb, hr, rfl, _⟩ := B.back5 hU ft d d' _ c k hs
  rw [hr] at hs
  rw [List.drop_zero] at hf
  exact ⟨Ra, Rb, d', _, cons2_of_take hr, hs, hf⟩

/-- The joinings off the front of a fold. -/
theorem Eight.peel6 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat)
    (l : List (Block St Unit)) (d : St) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (r : St × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft (B.b6 :: l) d rs c = .ok r) :
    ∃ d', B.b6.step ft d [] c = .ok (d', 0) ∧ foldBlocks ft l d' rs c = .ok r := by
  obtain ⟨_, _, _, _, _, e6, _⟩ :=
    blocks_rounds P sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hU
  obtain ⟨d', k, _, hs, hf⟩ := foldBlocks_cons_ok ft B.b6 l d rs c r h
  obtain ⟨hr, rfl, _⟩ := B.back6 hU ft d d' _ c k hs
  rw [hr] at hs
  rw [List.drop_zero, e6] at hf
  exact ⟨d', hs, hf⟩

/-- "LIN zeta" off the front of a fold. -/
theorem Eight.peel7 (B : Eight P) (hU : withU P.S = some sentU) (ft : Nat)
    (l : List (Block St Unit)) (d : St) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (r : St × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft (B.b7 :: l) d rs c = .ok r) :
    ∃ R d' rs', rs = R :: rs' ∧ B.b7.step ft d [R] c = .ok (d', 0) ∧
      foldBlocks ft l d' rs' c = .ok r := by
  obtain ⟨d', k, _, hs, hf⟩ := foldBlocks_cons_ok ft B.b7 l d rs c r h
  obtain ⟨R, hr, rfl, _⟩ := B.back7 hU ft d d' _ c k hs
  rw [hr] at hs
  rw [List.drop_zero] at hf
  exact ⟨R, d', _, cons_of_take hr, hs, hf⟩

/-- "SPLIT" off the front of a fold. -/
theorem Eight.peel8 (B : Eight P) (hU : withU P.S = some sentU)
    (hS : P.S.sharedSplitNeeded = true) (ft : Nat) (l : List (Block St Unit)) (d : St)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (B.b8 :: l) d rs c = .ok r) :
    ∃ R d' rs', rs = R :: rs' ∧ B.b8.step ft d [R] c = .ok (d', 0) ∧
      foldBlocks ft l d' rs' c = .ok r := by
  obtain ⟨d', k, _, hs, hf⟩ := foldBlocks_cons_ok ft B.b8 l d rs c r h
  obtain ⟨R, hr, rfl, _⟩ := B.back8 hU hS ft d d' _ c k hs
  rw [hr] at hs
  rw [List.drop_zero] at hf
  exact ⟨R, d', _, cons_of_take hr, hs, hf⟩

/-- A fold over no sub-protocol returns what it is handed. -/
theorem fold_nil {ft : Nat} {s s' : St} {rs rs' : List Fmt.RoundView} {c c' : List OpenedColumn}
    (h : foldBlocks ft ([] : List (Block St Unit)) s rs c = .ok (s', rs', c')) :
    s = s' ∧ rs = rs' ∧ c = c' := by
  have e : (s, rs, c) = (s', rs', c') := Except.ok.inj h
  simpa using e

end Desc.K14.Honest

#print axioms Desc.K14.Honest.Eight.fronts
#print axioms Desc.K14.Honest.step_plain_back
#print axioms Desc.K14.Honest.Eight.back1
#print axioms Desc.K14.Honest.Eight.back2
#print axioms Desc.K14.Honest.Eight.back3
#print axioms Desc.K14.Honest.Eight.back4
#print axioms Desc.K14.Honest.Eight.back5
#print axioms Desc.K14.Honest.Eight.back6
#print axioms Desc.K14.Honest.Eight.back7
#print axioms Desc.K14.Honest.Eight.back8
#print axioms Desc.K14.Honest.Eight.sentU_back
#print axioms Desc.K14.Honest.Eight.sentO_back
#print axioms Desc.K14.Honest.Public8.to1
#print axioms Desc.K14.Honest.Public8.to2
#print axioms Desc.K14.Honest.Public8.to3
#print axioms Desc.K14.Honest.Public8.to4
#print axioms Desc.K14.Honest.Public8.to5
#print axioms Desc.K14.Honest.Public8.to6
#print axioms Desc.K14.Honest.Public8.to7
#print axioms Desc.K14.Honest.Public8.to8
#print axioms Desc.K14.Honest.cons_of_take
#print axioms Desc.K14.Honest.cons2_of_take
#print axioms Desc.K14.Honest.Eight.peel1
#print axioms Desc.K14.Honest.Eight.peel2
#print axioms Desc.K14.Honest.Eight.peel3
#print axioms Desc.K14.Honest.Eight.peel4
#print axioms Desc.K14.Honest.Eight.peel5
#print axioms Desc.K14.Honest.Eight.peel6
#print axioms Desc.K14.Honest.Eight.peel7
#print axioms Desc.K14.Honest.Eight.peel8
#print axioms Desc.K14.Honest.fold_nil
