-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PlayedTerm.lean: what the frame's play makes of a proximity test's
half is the term: the rounds as a view shows them are `testAll`'s rounds, at one family of coins, at
the whole list of challenges, at the front at which the play began; the tables sent are the
messages' tables. This is `played_term`. It is stated at every job J (`TestJob`, Test.lean in this
folder: what a caller supplies for its test), under the hypotheses below. The four theorems whose
names begin with `drawn_` say which challenge each round has, in the term and in the lists that it
is built of. Definitions and theorems.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean. Its play is `play`: it runs a
list of steps (`Step`: one round each) at a list of challenges ds from a state m between two rounds
(`Mid`), and returns an error or a pair y: the rounds as played (`Played`) and the state after them.
A part (`Part`, the frame) is the prover's side of a stretch of rounds, with one move for each. The
half is the test's two parts, `firstPart J` and `restPart J`, at the place `J.p.place` (`proverSideOfProximityTest`,
Parts.lean in this folder). Its steps are `rowSteps` (the frame) at these two parts, at the declared
rounds rs and at c: what the two parts are given (`RowCoins`). The term is `testAll J w fr C D`
(Test.lean), computed from the job, the prover's input w, a front fr, a family of coins C
(`TestCoins`) and the challenges D by the round's number; its field `rs` is its list of rounds
(`Fmt.RoundView`: items and a challenge). A front (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean) is what
the job's functions are given of the run before the test. The message of round number i is `msgAt`
(Parts.lean) at the term's arguments and i; it is taken from the term. A part's reader makes a
family of coins of what the part is given: `firstRd J` (HalfSteps.lean in this folder) is the first
part's, `restCoins J` (Parts.lean) the second's. The stages are the list `J.p.nums.stages`.

  `played_term`: under the hypotheses below, where `play` at the half's steps returns y:
    `roundsOf y.1` is the field `rs` of the term at the input `m.st.input`, the front `frontOf m`,
    the coins `restCoins J c.2.1` and the challenges `byNo ds`; the tables of the rounds in y.1 are,
    round by round, those of `msgAt` at the same arguments, each under `some`; and y.2 is m with ds
    appended to `st.heard` and to `loc`, and `roundsOf y.1` appended to `seen`; on the field
    `opened` of y.2 nothing is said
  `drawn_test`: a round at index i of the term's `rs` has the challenge D i
  `drawn_stages`, `drawn_fold`: the same for the field `rs` of `stagesAll` (the rounds from one
    stage on) and for `aFold` (one fold's rounds; both Johnson/Desc/K12/Honest/Stages.lean), where
    the first round has the number o: the challenge is D (o + i)
  `drawn_showRV'`: the challenges of the rounds of `showRV k q D` (a fold's rounds after its first;
    Johnson/Prover/Link/FoldSay.lean), in order, are the values of D at 0, 1 and so on below k
  `byNo ds`: a definition: the list ds as a function of the round's number; from the list's end on
    its value is the challenge of three empty lists and no digest
  `frontOf m`: a definition: the front at which a play from m begins: `m.st.heard`, `m.st.own` and
    `m.shown` (the list `m.seen` and the columns `m.opened`), each whole
  `frontBy_zero`: `frontBy m 0` (PlayLaw.lean in this folder) is `frontOf m`

By what. `played_term` joins four theorems. `half_steps` (HalfSteps.lean): step number i of the
half's steps has the move of the test's round number i, at the coins `coinsAtRound J c i`: the first
part's reader's below `firstLen`, the second's from there on. `play_test` (PlayLaw.lean): the items
and tables of each round as played are those of that round's `msgAt`, at that round's coins, and its
challenge is the list's. `msgAt_first` (CoinsAgree.lean in this folder): under `Agree` the messages
of the rounds below 2 + h + g are the same at both families of coins. `msgAt_vals` (Canon.lean in
this folder) and `drawn_test`: a message's items, converted by `Said.got`, and the round's challenge
are the term's round. `drawn_stages` calls `drawn_fold` and `length_aFold`
(Johnson/Desc/K12/Honest/Causal.lean); `drawn_fold` calls `drawn_showRV'`.

Hypotheses of `played_term`. hst: the stages are s :: t :: rest: two stages or more. hk: at the
first stage, `s.k` is h + g of `sgOf s`. hrs: rs, the declared rounds with their oracle messages,
has `firstLen` + `restLen` elements: as many as the two parts have moves. hplay: `play` at the
half's steps, ds, the stored rounds `back` and m returns y. hA: the two parts' readers agree
(`Agree`, CoinsAgree.lean), at `m.st.input`, `frontOf m` and s: the two families are `firstRd J c.1`
and `restCoins J c.2.1`. hN: the term, at the arguments named at `played_term`, has as many rounds
as rs. The steps' name, the value v, rs, c, ds, `back` and m are free parameters.

Limits. `Agree` (hA), the two counts (hrs, hN) and k = h + g at the first stage (hk) are hypotheses:
none of them is proved here. At the two parts' readers `Agree` has no value that meets it in the
library yet; the two files that the limits of CoinsAgree.lean name for it treat only a job whose
fresh table has come earlier (`J.fresh` is `some _`). That `play` returns (hplay) is a hypothesis
too. Nothing on the columns that are read, on a decision, on completeness, on soundness or on what
is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.HalfSteps
import Johnson.Desc.ProofFile.Honest.K12.CoinsAgree
import Johnson.Desc.ProofFile.Honest.K12.Canon

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {V W X : Type}

theorem drawn_showRV' : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    (showRV k q D).map (·.drawn) = (List.range k).map D
  | 0, _, _ => rfl
  | k + 1, q, D => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show D 0 :: (showRV k _ fun n => D (n + 1)).map (·.drawn) = _
    rw [drawn_showRV' k _ fun n => D (n + 1)]
    rfl

/-- Round number i of a fold (`aFold`) has the challenge D (o + i). -/
theorem drawn_fold (K : BCoins) (j : ℕ) (cur : Fmt.M1.Stage) (o : ℕ) (P : PS) (row : GroupRow)
    (D : ℕ → Fmt.Drawn) (i : ℕ) (r : Fmt.RoundView) (h : (aFold K j cur o P row D)[i]? = some r) :
    r.drawn = D (o + i) := by
  have e1 : (aFold K j cur o P row D).map (·.drawn) =
      (List.range (1 + ((sgOf cur).h + (sgOf cur).g))).map fun i => D (o + i) := by
    unfold aFold foldShown
    rw [List.map_cons, drawn_showRV', Nat.add_comm 1, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    rfl
  have e2 := congrArg (·[i]?) e1
  simp only [List.getElem?_map, h, Option.map_some] at e2
  cases hr : (List.range (1 + ((sgOf cur).h + (sgOf cur).g)))[i]? with
  | none =>
    rw [hr] at e2
    cases e2
  | some n =>
    rw [hr] at e2
    obtain rfl : n = i := by
      have hi : i < (List.range (1 + ((sgOf cur).h + (sgOf cur).g))).length :=
        (List.getElem?_eq_some_iff.1 hr).1
      rw [List.getElem?_eq_getElem hi, List.getElem_range] at hr
      exact (Option.some.inj hr).symm
    exact Option.some.inj e2

/-- Round number i of the field `rs` of `stagesAll` has the challenge D (o + i). -/
theorem drawn_stages (p : P12) (K : BCoins) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn) (i : ℕ) (r : Fmt.RoundView),
    (stagesAll p K rest j cur l o t P trees D).rs[i]? = some r → r.drawn = D (o + i)
  | [], j, cur, _, o, t, P, _, D, i, r, h => by
    match i, h with
    | 0, h => exact (Option.some.inj h) ▸ rfl
    | 1, h => exact (Option.some.inj h) ▸ rfl
    | n + 2, h => cases h
  | next :: rest, j, cur, l, o, t, P, trees, D, i, r, h => by
    simp only [stagesAll] at h
    have hl := length_aFold K j cur o P (rowOf t) D
    rw [List.append_assoc, List.getElem?_append] at h
    split at h
    · exact drawn_fold K j cur o P (rowOf t) D i r h
    · rename_i hi
      rw [hl] at hi h
      rw [List.getElem?_append] at h
      split at h
      · rename_i hi2
        have hi3 : i - (1 + ((sgOf cur).h + (sgOf cur).g)) < 2 := hi2
        obtain ⟨q, hq⟩ : ∃ q, i = 1 + ((sgOf cur).h + (sgOf cur).g) + q :=
          ⟨i - (1 + ((sgOf cur).h + (sgOf cur).g)), by omega⟩
        subst hq
        rw [Nat.add_sub_cancel_left] at h hi3
        match q, hi3, h with
        | 0, _, h =>
          rw [← Option.some.inj h]
          show D (o + 1 + ((sgOf cur).h + (sgOf cur).g)) = _
          congr 1
          omega
        | 1, _, h =>
          rw [← Option.some.inj h]
          show D (o + 2 + ((sgOf cur).h + (sgOf cur).g)) = _
          congr 1
          omega
      · rename_i hi2
        have hi3 : ¬ i - (1 + ((sgOf cur).h + (sgOf cur).g)) < 2 := hi2
        have k := drawn_stages p K rest (j + 1) next _ _ _ _ _ D _ r h
        rw [k]
        congr 1
        show o + ((sgOf cur).h + (sgOf cur).g) + 3 +
          (i - (1 + ((sgOf cur).h + (sgOf cur).g)) - 2) = _
        omega

/-- Round number i of the test's term (the field `rs` of `testAll`) has the challenge D i. -/
theorem drawn_test (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (i : ℕ) (r : Fmt.RoundView) (h : (testAll J w fr C D).rs[i]? = some r) : r.drawn = D i := by
  unfold testAll at h
  split at h
  · cases h
  · cases i with
    | zero => exact (Option.some.inj h) ▸ rfl
    | succ n =>
      have k := drawn_stages _ _ _ _ _ _ _ _ _ _ D n r h
      rw [k, Nat.add_comm]

/-- A list of challenges as a function of the round's number. From the list's end on: the challenge
of three empty lists and no digest. -/
def byNo (ds : List Fmt.Drawn) (n : ℕ) : Fmt.Drawn := ds.getD n ⟨[], [], [], none⟩

/-- The front at which a play from m begins: the challenges heard, what the parts pass on, the list
`seen` and the columns `opened`, as they are in m. -/
def frontOf (m : Mid W X) : Front X := ⟨m.st.heard, m.st.own, m.shown⟩

theorem frontBy_zero (m : Mid W X) : frontBy m 0 = frontOf m := by
  simp [frontBy, frontOf, Seen.front, Mid.shown]

/-- **What the play makes of the half is the term.** Where `play` at the two parts' steps returns y:
`roundsOf y.1` is the field `rs` of `testAll`, the tables in y.1 are those of `msgAt`, and y.2 is m
with the challenges ds and the played rounds appended. The hypotheses, one by one, are in the file's
head. -/
theorem played_term (J : TestJob W X) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g) (name : String)
    (v : Option V) (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle))
    (hrs : rs.length = firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (c : RowCoins [(firstPart J : Part V W X), restPart J]) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (y : List Played × Mid W X)
    (hplay : play (rowSteps name J.p.place v [(firstPart J : Part V W X), restPart J] 0 rs c) ds
      back m = .ok y)
    (hA : Agree J m.st.input (frontOf m) s (firstRd J c.1) (restCoins J c.2.1))
    (hN : (testAll J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds)).rs.length = rs.length) :
    roundsOf y.1 = (testAll J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds)).rs ∧
      y.1.map (·.tables) = (List.range rs.length).map (fun i =>
        (msgAt J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds) i).tables.map some) ∧
      y.2.st = { m.st with heard := m.st.heard ++ ds } ∧ y.2.seen = m.seen ++ roundsOf y.1 ∧
      y.2.loc = m.loc ++ ds := by
  obtain ⟨hl, hm⟩ := half_steps J s t rest hst name v rs hrs c
  obtain ⟨p1, p2, p3, p4⟩ := play_test J (coinsAtRound J c) (byNo ds) _ 0 ds back m y
    (fun i h => by rw [Nat.zero_add]; exact hm i h) hplay
    ⟨Nat.zero_le _, Nat.zero_le _, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
    (fun n h => by
      rw [Nat.zero_add]
      unfold byNo
      rw [List.getD_eq_getElem _ _ h])
  rw [hl, frontBy_zero] at p1
  have hmsg : ∀ i, msgAt J m.st.input (frontOf m) (coinsAtRound J c (0 + i)) (byNo ds) (0 + i) =
      msgAt J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds) i := fun i => by
    rw [Nat.zero_add]
    unfold coinsAtRound
    split
    · rename_i hi
      refine msgAt_first J _ _ _ _ _ s t rest hst hA i ?_
      rw [hst] at hi
      have : firstLen (s :: t :: rest) = 2 + s.k := rfl
      omega
    · rfl
  have p1' : y.1.map shownOf = (List.range rs.length).map fun i =>
      shownAt (msgAt J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds) i) (byNo ds i) := by
    rw [p1]
    refine List.map_congr_left fun i _ => ?_
    show shownAt (msgAt J m.st.input (frontOf m) (coinsAtRound J c (0 + i)) (byNo ds) (0 + i))
      (byNo ds (0 + i)) = _
    rw [hmsg i, Nat.zero_add]
  refine ⟨?_, ?_, p2, p3, p4⟩
  · have e : roundsOf y.1 = (y.1.map shownOf).map fun x => ⟨x.1, x.2.2⟩ := by
      unfold roundsOf
      rw [List.map_map]
      rfl
    rw [e, p1', List.map_map]
    refine List.ext_getElem? fun i => ?_
    rw [List.getElem?_map]
    by_cases hi : i < rs.length
    · rw [List.getElem?_range hi]
      have hi' :
          i < (testAll J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds)).rs.length := by
        rw [hN]
        exact hi
      have hr := List.getElem?_eq_getElem hi'
      rw [hr]
      show some (⟨(msgAt J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds) i).vals.map
        Said.got, byNo ds i⟩ : Fmt.RoundView) = _
      rw [msgAt_vals J _ _ _ _ i _ hr, ← drawn_test J _ _ _ _ i _ hr]
    · rw [List.getElem?_eq_none (by rw [List.length_range]; omega),
        List.getElem?_eq_none (by rw [hN]; omega)]
      rfl
  · have e : y.1.map (·.tables) = (y.1.map shownOf).map fun x => x.2.1 := by
      rw [List.map_map]
      rfl
    rw [e, p1', List.map_map]
    rfl

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.drawn_showRV'
#print axioms ProofFile.Honest.K12.drawn_fold
#print axioms ProofFile.Honest.K12.drawn_stages
#print axioms ProofFile.Honest.K12.drawn_test
#print axioms ProofFile.Honest.K12.frontBy_zero
#print axioms ProofFile.Honest.K12.played_term
#print axioms ProofFile.Honest.K12.byNo
#print axioms ProofFile.Honest.K12.frontOf
