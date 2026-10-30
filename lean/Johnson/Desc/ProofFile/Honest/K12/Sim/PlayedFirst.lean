-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/PlayedFirst.lean: where the frame's own play of a proximity
test's first part leaves a run: the play returns; the state has heard the part's challenges; and the
rounds that are shown are, item by item, those that the text makes: "BAT", which shows nothing, and
the first fold's rounds (`aFold`, Johnson/Desc/K12/Honest/Stages.lean) at the coins that the part is
handed. This is `first_played`, under two hypotheses. It is stated at every job and all challenges
that meet them, and at every name, address, value that the second stop may read, state from which
the part is played and coins that the part is given. Sim/OnFromPlay.lean calls `first_played` and
`aFold_coins`. One definition, and theorems.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean. Its play is `play`: it runs a
list of steps (`Step`: one round each) at a list of challenges ds, from a state m between two rounds
(`Mid`), and returns an error or a pair y: the rounds as played, and the state after them. Where the
play leaves a run is that state, `y.2`. The fields of m: `st` is the prover's state (`State`:
`input`; `heard`, the challenges heard so far; `own`, what the parts pass on to each other); `loc`
is the list of the challenges heard so far that the stops may read; `seen` is the list of the rounds
shown so far that a part may read (`Fmt.RoundView`: the items `vals` and the challenge `drawn`). A part
(`Part`) is the prover's side of a stretch of a sub-protocol's rounds: one move (`Move`) for each
round, and two stops. `Part.steps` makes the part's steps from a name, an address ad (`Addr`), the
declared rounds, a value v, if any, that the second stop may read, and the coins c that the part is
given. Files named without a folder, and the folder Sim/, are in Johnson/Desc/ProofFile/Honest/K12/.
A job J (`TestJob`, Test.lean) is what a caller supplies for its test; `J.p.nums.stages` is the
test's list of stages and `J.laid` (Test.lean) the list of its declared rounds. The text, also
called the term, is `testAll J w fr K D` (Test.lean), of type `BOut`
(Johnson/Prover/Link/BodyAll.lean); its field `rs` is the list of the test's rounds. There w is the
input, fr the front (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes the test), K the
coins that the term reads (`TestCoins`, Test.lean) and D the sampled challenges, by the round's
number in the test. Round 0 is "BAT". The first part (`firstPart`, Parts.lean) has the test's first
`firstLen` (Parts.lean) rounds: at two stages or more these are 2 + k rounds, with the first stage's
k: "BAT" and the first fold. `firstRd J c` (HalfSteps.lean) is what the part's moves read of c, as
`TestCoins`. `msgAt J w fr K D i` (Parts.lean) is the message of round number i, cut out of the
term; `sendingOf` (Sim/Sims.lean) makes the same cut out of any `BOut`. `sgOf s`
(Johnson/Desc/K12/Law/ChainOf.lean) is a stage s in the library's form: h as in s, and g := k - h.
The letters are `BCoins` (BodyAll.lean): the random values that the definitions and theorems of
Johnson/Prover/Link/ take as a parameter. Its field `W` gives, for a stage's form and number, the
coefficients of the fold's own polynomial: the argument W of `foldShown`
(Johnson/Desc/K12/Honest/Fold.lean), of which `aFold` is an instance. `coinsOf` (Coins.lean) makes a
`BCoins` from a list of stages and two families of coins. The prover's state at a stage is `PS`
(Johnson/Prover/Link/BodyState.lean); `μOf` (BodyState.lean) reads its fields `tabM` and `tabZ`, the
two tables' messages.

  `first_played`: the statement. Under the two hypotheses below, `play` returns `.ok y` at the steps
    of `firstPart J` over the first `firstLen` entries of `J.laid`, at the challenges ds, with no
    stored round to fall back on, from m. `y.2.st` is `m.st` with ds appended to `heard`; `y.2.loc`
    is `m.loc` with ds appended; `y.2.seen` is `m.seen`, then the round with no item and the
    challenge D 0, then `aFold`. The arguments of `aFold`: `coinsOf` at the stages and at the fields
    `hide` and `rest` of `firstRd J c`; the stage's number 0 and the stage s; 1, the number of the
    fold's first round; the state `J.first` (Test.lean) at `m.st.input`, `frontBy m 0`
    (PlayLaw.lean) and `firstRd J c`; `rowOf` (BodyAll.lean) of `J.recB` (Test.lean: the state after
    the batching) at the same input and front and at D 0; and D
  `rounds_prefix`: the first rounds of a text's output, said and shown again, are these rounds. For
    O of type `BOut` whose `rs` is A followed by Bs, where every round of A meets `Fixed` and the
    challenges of A are D 0, D 1, ... in order: take, for each i below the length of A, the round
    with the items of `sendingOf O (dep i) i`, converted by `Said.got`, and the challenge D i. This
    list is A. dep is a free parameter: `sendingOf` reads it for the tables only
  `first_seen`: so for the term's first rounds. Where the stages are s :: next :: rest and
    `s.k = (sgOf s).h + (sgOf s).g`: take, for each i below `firstLen`, the round with the items of
    `msgAt J w fr K D i`, converted by `Said.got`, and the challenge D i. This list is the round
    with no item and the challenge D 0, followed by `aFold` at the arguments listed under
    `first_played`, with w, fr and K for `m.st.input`, `frontBy m 0` and `firstRd J c`. At every w,
    fr, K and D
  `Fixed r`: a definition, of a round r: `(r.vals.filterMap saidOf).map Said.got` is `r.vals`
  `foldShown_fixed`: every round of `foldShown` meets `Fixed`, at all arguments
  `showRV_drawn`, `foldShown_drawn`: the challenges of the rounds of `showRV k q D`
    (Johnson/Prover/Link/FoldSay.lean) are D i for i below k, in order; those of
    `foldShown s v μ Wc D` are D i for i below 1 + (s.h + s.g), in order
  `aFold_coins`: of the letters a fold's rounds read its own polynomial's coefficients, and of the
    prover's state the two tables' messages. (That the coefficients read the coins 0 … 2k alone:
    `hideAt_congr`, …/K12/AgreeBook.lean.) As Lean has it: if K and K' have the same
    `W (sgOf cur) j`, and P and P' the same `μOf (sgOf cur)`, then `aFold K j cur o P row D` is
    `aFold K' j cur o P' row D`. In `hideAt_congr`, k is the number of variables; `coinsOf` calls
    `hideAt` (Coins.lean) at s.h + s.g

Why there is something to prove. A move says typed field elements (`saidOf`, …/K12/Parts.lean), and
the frame shows them as words again (`Said.got`, …/Honest/Frame.lean): so a run shows the word of
the element of the text's word. On the fold's items that is the text's own word: `back_of_canon`,
`canon_fold` (…/K12/Canon.lean, which has it for every round of the term): called. In Lean's names:
the term holds each item as words (`Fmt.ItemValue`); `msgAt` reads it by `saidOf` as an item of a message
(`Said`, the frame); `Step.tell` (the frame) converts that item to words by `Said.got`.

By what. `first_played` joins, as `shows_first` (Sim/ShowsFirst.lean) does, `first_moves` and
`steps_at` (HalfSteps.lean), `first_quiet` and `part_quiet` (HalfReturns.lean), `fits_all`
(FitsAll.lean), `play_returns` (PlayReturns.lean) and `play_test` (PlayLaw.lean); then it rewrites
by `first_seen`. The hypothesis `Heard` (PlayLaw.lean) of the last two is taken at 0 rounds, where
it holds at every m. The proof takes `J.laid` for `laidOf J.p` (Johnson/Desc/K12/Law/ReadsK.lean),
which is defined by the same term. `first_seen` is `rounds_prefix` at the term, which `testAll_cut`
(Sim/Shows.lean) cuts after the first fold, with `length_aFold`
(Johnson/Desc/K12/Honest/Causal.lean), `foldShown_fixed` and `foldShown_drawn`; that `msgAt` is
`sendingOf` at the term and at `depthAt` (Test.lean) holds by unfolding. `foldShown_fixed` is
`back_of_canon` at `canon_fold`. `aFold_coins` unfolds `aFold`.

Hypotheses of `first_played`. T: `FirstTies J s next rest D ds` (Sim/ShowsFirst.lean), a structure
of six fields: the job's stages are s :: next :: rest (`stages`) · `laidOf J.p` has at least
`firstLen` entries (`enough`) · the declared rounds ask the sorts that the term shows (`sorts`) ·
each declared oracle message has the depth and the width of the tree that the term sends (`tables`)
· ds has `firstLen` entries (`len`) · entry number n of ds is D n (`own`). hk:
`s.k = (sgOf s).h + (sgOf s).g`; since g is k - h in the natural numbers, this says h ≤ k at the
stage s.

Limits.
- `FirstTies` (Sim/ShowsFirst.lean) is a hypothesis; so is h ≤ k at the first stage. Neither is
  proved at any job in this file.
- One part, played alone, from any state. m is a free parameter: no hypothesis says that a run
  reaches it.
- Nothing on what comes before the part: the front `frontBy m 0` is read off m as it is.
- name, ad and v are free parameters: nothing ties ad to the test's place `J.p.place`.
- `first_played` states nothing on `y.1`, the rounds as played. The list `seen` holds items in the
  clear and challenges: so nothing is stated on a table, also where the first fold sends its own
  table (`J.fresh` is `none`).
- The job's functions for the state on entry to the test and for the first stage's tables are the
  caller's: nothing here compares them with anything, and the right sides of `first_played` and
  `first_seen` are computed from them. Where a `decide` function rejects inside `J.recB`, the state
  before it is kept; where the state that `J.recB` returns passes on no claim, `rowOf` gives the
  empty row. Both theorems hold there too.
- `firstRd` gives 0 for the field `rest` of the term's coins and, where `J.fresh` names a part, 0
  for the field `tails`; the right side of `first_played` is written at these values. That the
  fold's rounds read neither field is not stated here: `aFold_coins` is on `BCoins` and `PS`, not on
  `TestCoins`.
- `aFold_coins` is an equation between two values of `aFold`. Its two hypotheses have to be shown by
  whoever calls it; cur, j, o, row and D are the same on both sides.
- No property is claimed; nothing here speaks of a law or of a simulator. A law is here a
  probability distribution.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ShowsFirst
import Johnson.Desc.K12.Honest.Causal
import Johnson.Desc.ProofFile.Honest.K12.Canon

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {V W X : Type}

/-! ## 1 A fold's rounds, said and shown again -/

/-- A round r whose items are unchanged by reading and writing: `saidOf` (Parts.lean) reads each as
an item of a message, `Said.got` (the frame) converts that item to words, and the list is `r.vals`
again. -/
def Fixed (r : Fmt.RoundView) : Prop := (r.vals.filterMap saidOf).map Said.got = r.vals

theorem foldShown_fixed (s : Sg) (v μ : s.cIn.J → GE) (Wc : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) : ∀ r ∈ foldShown s v μ Wc D, Fixed r :=
  fun r h => back_of_canon r.vals (canon_fold s v μ Wc D r h)

theorem showRV_drawn : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    (showRV k q D).map (·.drawn) = (List.range k).map D
  | 0, _, _ => rfl
  | k + 1, q, D => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show D 0 :: (showRV k (fun i => q (Sum.inr i)) fun n => D (n + 1)).map (·.drawn) = _
    rw [showRV_drawn k]
    rfl

theorem foldShown_drawn (s : Sg) (v μ : s.cIn.J → GE) (Wc : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) :
    (foldShown s v μ Wc D).map (·.drawn) = (List.range (1 + (s.h + s.g))).map D := by
  unfold foldShown
  rw [List.map_cons, showRV_drawn, Nat.add_comm 1, List.range_succ_eq_map, List.map_cons,
    List.map_map]
  rfl

/-- The first rounds of a text's output, said and shown again. O: the output. A: its first rounds.
Said: cut out of O by `sendingOf` (Sim/Sims.lean), which reads each item by `saidOf`. Shown again:
converted by `Said.got`, and paired with the challenge D i. Where every round of A meets `Fixed`
(hF) and the challenges of A are those of D from number 0 on (hD), the list is A. -/
theorem rounds_prefix (O : BOut) (A Bs : List Fmt.RoundView) (hO : O.rs = A ++ Bs)
    (hF : ∀ r ∈ A, Fixed r) (D : ℕ → Fmt.Drawn)
    (hD : A.map (·.drawn) = (List.range A.length).map D) (dep : ℕ → Option ℕ) :
    (List.range A.length).map (fun i =>
      (⟨(sendingOf O (dep i) i).vals.map Said.got, D i⟩ : Fmt.RoundView)) = A := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  have e1 : (sendingOf O (dep i) i).vals = A[i].vals.filterMap saidOf := by
    unfold sendingOf
    simp only [hO, List.getElem?_append_left h2, List.getElem?_eq_getElem h2, Option.map_some,
      Option.getD_some]
  have e2 : D i = A[i].drawn := by
    have := congrArg (fun l => l[i]?) hD
    simpa [List.getElem?_map, List.getElem?_eq_getElem h2, List.getElem?_range h2] using this.symm
  rw [e1, hF _ (List.getElem_mem h2), e2]

/-! ## 2 The term's first rounds; the play -/

/-- **The term's first rounds, said and shown again, are the text's.** The left side: for each i
below `firstLen`, the items of `msgAt J w fr K D i`, converted by `Said.got`, with the challenge
`D i`. The right side: "BAT", with no item, and the first fold's rounds `aFold`. hk says h ≤ k at
the stage s. -/
theorem first_seen (J : TestJob W X) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g) (w : W)
    (fr : Front X) (K : TestCoins) (D : ℕ → Fmt.Drawn) :
    (List.range (firstLen J.p.nums.stages)).map (fun i =>
      (⟨(msgAt J w fr K D i).vals.map Said.got, D i⟩ : Fmt.RoundView)) =
      ⟨[], D 0⟩ :: aFold (coinsOf (s :: next :: rest) K.hide K.rest) 0 s 1 (J.first w fr K)
        (rowOf (J.recB w fr (D 0))) D := by
  have hn : firstLen J.p.nums.stages = 2 + s.k := by rw [hst]; rfl
  have hlen : ((⟨[], D 0⟩ : Fmt.RoundView) :: aFold (coinsOf (s :: next :: rest) K.hide K.rest) 0 s 1
      (J.first w fr K) (rowOf (J.recB w fr (D 0))) D).length = firstLen J.p.nums.stages := by
    rw [List.length_cons, length_aFold, hn, hk]
    omega
  rw [← hlen]
  refine rounds_prefix (testAll J w fr K D) _ (restOf J w fr K D s next rest).rs
    (by rw [testAll_cut J w fr K D s next rest hst]; rfl) (fun r hr => ?_) D ?_ (depthAt J)
  · rcases List.mem_cons.1 hr with rfl | h2
    · rfl
    · exact foldShown_fixed _ _ _ _ _ r h2
  · rw [hlen, hn, hk, List.map_cons]
    show D 0 :: (foldShown (sgOf s) _ _ _ fun n => D (1 + n)).map (·.drawn) = _
    rw [foldShown_drawn, show 2 + ((sgOf s).h + (sgOf s).g) = (1 + ((sgOf s).h + (sgOf s).g)) + 1 by
      omega, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg _ (List.map_congr_left fun n _ => ?_)
    show D (1 + n) = D (n + 1)
    rw [Nat.add_comm]

/-- **Where the play of the first part leaves the run.** The play returns a pair y; `y.2` is m with
ds appended to `st.heard` and to `loc`, and with "BAT" (no item) and the first fold's rounds `aFold`
appended to `seen`. T: the hypotheses on the test's parameters and on the challenges
(Sim/ShowsFirst.lean). hk says h ≤ k at the first stage. Nothing is stated on `y.1`. -/
theorem first_played (J : TestJob W X) (name : String) (ad : Addr) (v : Option V)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (m : Mid W X) (D : ℕ → Fmt.Drawn)
    (ds : List Fmt.Drawn) (T : FirstTies J s next rest D ds)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (c : (firstPart J : Part V W X).Coins) :
    ∃ y, play ((firstPart J : Part V W X).steps name ad (J.laid.take (firstLen J.p.nums.stages)) v
        c) ds [] m = .ok y ∧
      y.2.st = { m.st with heard := m.st.heard ++ ds } ∧
      y.2.seen = m.seen ++ ⟨[], D 0⟩ ::
        aFold (coinsOf (s :: next :: rest) (firstRd J c).hide (firstRd J c).rest) 0 s 1
          (J.first m.st.input (frontBy m 0) (firstRd J c))
          (rowOf (J.recB m.st.input (frontBy m 0) (D 0))) D ∧
      y.2.loc = m.loc ++ ds := by
  have hrs : (J.laid.take (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    rw [List.length_take]
    exact Nat.min_eq_left T.enough
  obtain ⟨hl, hm⟩ := steps_at J (firstPart J : Part V W X) (firstRd J) 0
    (firstLen J.p.nums.stages) (first_moves J) name ad (J.laid.take (firstLen J.p.nums.stages)) hrs
    v c
  have hq := part_quiet (firstPart J : Part V W X) (first_quiet J).1 (first_quiet J).2 name ad
    (J.laid.take (firstLen J.p.nums.stages)) v c
  have hfit : ∀ i (h : i < ((firstPart J : Part V W X).steps name ad
      (J.laid.take (firstLen J.p.nums.stages)) v c).length),
      (msgAt J m.st.input (frontBy m 0) (firstRd J c) D (0 + i)).fits
        (((firstPart J : Part V W X).steps name ad (J.laid.take (firstLen J.p.nums.stages)) v
          c)[i]).decl
        (((firstPart J : Part V W X).steps name ad (J.laid.take (firstLen J.p.nums.stages)) v
          c)[i]).oracles = true := by
    intro i h
    have hi : i < firstLen J.p.nums.stages := hl ▸ h
    have hd : (laidOf J.p)[0 + i]? =
        some ((J.laid.take (firstLen J.p.nums.stages))[i]'(by rw [hrs]; exact hi)) := by
      show J.laid[0 + i]? = _
      rw [Nat.zero_add, ← List.getElem?_take_of_lt hi, List.getElem?_eq_getElem]
    have := fits_all J m.st.input (frontBy m 0) (firstRd J c) D s (next :: rest) T.stages T.sorts
      T.tables (0 + i) _ hd
    simpa [Part.steps, List.getElem_zip] using this
  have hH : Heard m 0 D := ⟨Nat.zero_le _, Nat.zero_le _, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  have hown : ∀ n (h : n < ds.length), ds[n] = D (0 + n) := fun n h => by
    rw [Nat.zero_add]
    exact T.own n h
  obtain ⟨y, hy⟩ := play_returns J (fun _ => firstRd J c) D _ 0 ds [] m hm hq hfit hH
    (T.len.trans hl.symm) hown
  obtain ⟨hp, h1, h2, h3⟩ := play_test J (fun _ => firstRd J c) D _ 0 ds [] m y hm hy hH hown
  rw [hl] at hp
  refine ⟨y, hy, h1, ?_, h3⟩
  rw [h2, ← first_seen J s next rest T.stages hk]
  refine congrArg _ ?_
  have e : roundsOf y.1 = (y.1.map shownOf).map fun t => (⟨t.1, t.2.2⟩ : Fmt.RoundView) := by
    unfold roundsOf
    rw [List.map_map]
    rfl
  rw [e, hp, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show (⟨(msgAt J m.st.input (frontBy m 0) (firstRd J c) D (0 + i)).vals.map Said.got, D (0 + i)⟩ :
    Fmt.RoundView) = _
  rw [Nat.zero_add]

/-! ## 3 What a fold's rounds read of the letters and of the state -/

theorem aFold_coins (K K' : BCoins) (j : ℕ) (cur : Fmt.M1.Stage) (o : ℕ) (P P' : PS)
    (row : GroupRow) (D : ℕ → Fmt.Drawn) (hW : K.W (sgOf cur) j = K'.W (sgOf cur) j)
    (hμ : μOf (sgOf cur) P = μOf (sgOf cur) P') :
    aFold K j cur o P row D = aFold K' j cur o P' row D := by
  unfold aFold
  rw [hW, hμ]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.foldShown_fixed
#print axioms ProofFile.Honest.K12.showRV_drawn
#print axioms ProofFile.Honest.K12.foldShown_drawn
#print axioms ProofFile.Honest.K12.rounds_prefix
#print axioms ProofFile.Honest.K12.first_seen
#print axioms ProofFile.Honest.K12.first_played
#print axioms ProofFile.Honest.K12.aFold_coins
#print axioms ProofFile.Honest.K12.Fixed
