-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/OnFromPlay.lean: five of the eight clauses of `OnFree`
(Sim/ExactFree.lean) follow from the frame's own play of the first part. The theorem is
`onFree_of_play`; it has hypotheses of its own, listed below, among them `Agree`. `OnFree` is the
condition at the second part's entry under which `exact_free` (Sim/ExactFree.lean) is stated, at a
state on entry that is made of the plan's public part, not shown to be the verifier's. General in
the job J and in m₀, the state of the run before the test; also in the simulators' job Js, in K,
chain, o, pb, mem and front, and in the coins c that the first part is given. The three other
clauses are hypotheses, stated at the test's entry (`AtEntry`). One structure and three theorems
with their proofs. No property is claimed.

Terms. The test is a proximity test (`KindName.K12`). …/K12/ is Johnson/Desc/ProofFile/Honest/K12/,
and Sim/ is a folder in it. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean with
Honest/Side.lean. Its play (`play`) runs a list of steps, one round each, at a list of challenges,
from a state of a chain's run between two rounds (`Mid`); it returns an error or a pair y, and y.2
is the state after these rounds. Of such a state m, `m.st` holds the input and the challenges heard,
`m.seen` the rounds shown, and `m.opened` the columns handed, if any. A part (`Part`) is the
prover's side of some rounds in a row. A job J (`TestJob`, …/K12/Test.lean) is what a caller
supplies for its test; the simulators' job Js (`SimJob`, Sim/Sims.lean) is what a caller says of its
test to the simulators. The two jobs' letters for the state are their fields `rec₀`. The first part
(`firstPart J`, …/K12/Parts.lean) has the test's first `firstLen` rounds: at two stages or more,
"BAT" and the first fold. The second part has all the others. The first and the second member are
`firstMember J Js` and `restMember J Js` (Sim/Row.lean): a part with its number, its declared rounds
and a term of type `Sim`. The frame's own premises at a member are the hypotheses inside
`ExactMember` (Honest/Small/Field.lean). The test's entry is m₀, from which the first part is
played; the second part's entry is y.2. "In front" speaks of the parameter front, a `Before`
(Frame.lean): a list of rounds, each with its items, its listed columns and its challenge.
`front.seen` gives these rounds in the form of `m.seen`, and the first part's rounds as shown in
front are the last `firstLen` of them (`lastSeen`, Sim/Sims.lean). What the front lists of a tree is
what `Before.treeCols` (Side.lean) returns: pairs of a position and a column. The parameter fr of
`AtEntry` has another type, `Front` (Johnson/Desc/ProofFile/Honest/Sum.lean): what the functions of
J are given of the run before the test. D gives the challenges by the round's number in the test,
from 0; ds is the list of the first part's challenges. The text is `aFold`
(Johnson/Desc/K12/Honest/Stages.lean), which computes a fold's rounds. mem gives the stretches of
coins that the second part carries, by number; the carried coins are `carriedCoins J mem`
(Sim/Row.lean). A book (`ProverCoinCounts`, Frame.lean) is public data, among them which stretches of one part's
coins another part is given too; by it the frame lends the parts their coins (`lendRow`). s is the
first stage; k is its field `k`, and h and g are those of `sgOf s`
(Johnson/Desc/K12/Law/ChainOf.lean), where g is k - h. A place of a file is the place of a test in
one of the files that the library describes. A member of a condition is a choice of values at which
it holds. What is asked is a hypothesis, and so is a premise.

  `onFree_of_play`: the statement; the play keeps the input. In Lean: under the hypotheses below
    there is a y such that `play` of the first part's steps, at ds and from m₀, returns y;
    `y.2.st.input` is `m₀.st.input`; and, where `y.2.seen = front.seen`,
    `OnFree J Js K chain o pb mem y.2 front` holds
  `AtEntry J Js K chain o pb mem w fr D front`: a structure of three propositions: the three clauses
    that are left, `door`, `asks` and `tree`. The parameters w, fr and D are in the place of what
    `OnFree` computes from a state m: `m.st.input`, `restFront J m` and `heardIn J m` (Sim/Row.lean)
  `take_behind`, `drop_behind`: for lists a and b, where b has n entries: `a ++ b` without its last
    n entries is a; the last n entries of `a ++ b` are b

The five: `le`, `leS`: the run has heard and shown the first part's rounds · `heardFit`: its
challenges have the declared form: the frame's own premise at the first member · `heard`: they are
those that are shown in front · `fold`: the first fold's rounds, as shown in front, are those that
the text makes at the carried coins. The play shows them at the spent run (`first_played`,
Sim/PlayedFirst.lean); that the two are one is asked as `Agree` (…/K12/CoinsAgree.lean), which holds
at the coins that the frame lends, from a test on the book (`agree_of_ties`, …/K12/AgreeBook.lean:
not called here). In Lean: `le` and `leS` say that y.2 has heard at least `firstLen` challenges and
has shown at least as many rounds. `first_played` has the rounds at `firstRd J c`
(…/K12/HalfSteps.lean), which is what the first part's moves read of c. The field `hide` of
`firstRd J c` is taken from the stretch that the part spends (`spentRun`, …/K12/Parts.lean) only
where the first fold's fresh table has come earlier (`J.fresh` is `some _`); where the fold sends
the table itself, it is taken from the part's own coins. `agree_of_ties` is stated only where the
table has come earlier. Next to the test on the book (`tiesB`) it has three hypotheses: the lending
returns, k = h + g at the first stage, and a clause on the job's rows. It concludes `Agree` at
`restCoins` (…/K12/Parts.lean) of the lent coins, not at `carriedCoins J mem`; nothing in this file
passes from the one to the other.

The three that are left are the fields of `AtEntry`, at the entry's own values: the input w, the
front fr as the first part's moves build it, and D. `onFree_of_play` takes them as `m₀.st.input`,
`frontBy m₀ 0` (…/K12/PlayLaw.lean) and D. `door`: the two jobs' letters for the verifier's state
agree · `asks`: the state's shape and the prover's data · `tree`: one tree in front; the front lists
it; what it lists is the tree's. In Lean: `door` says that `J.rec₀ w fr` is `Js.rec₀ pb` at front
without its last `firstLen` rounds (`Before.cut`, Sim/Sims.lean). No statement that this state is
the verifier's. `asks` says that there are Dp, cc and R, with `Dp.ts` of length 1, at which
`ShapeAsks` and `DataAsks` (…/K12/PlanB.lean) hold at w, fr, the carried coins and D, the first also
at the table of codes K. `tree` says that `J.trees₀`, at w, fr, mem and the first stage's state at
the carried coins (`J.first`, …/K12/Test.lean), returns one tree, of the first stage's depth, with
the columns colR; that `front.treeCols` at the source of the opening o (`srcOf chain o.2`,
Frame.lean) returns `some cols`; and that each pair in cols has the column of colR at its position.

By what. `first_played` (Sim/PlayedFirst.lean) gives y, its state and the rounds that it has shown.
With `take_behind`, `drop_behind`, `frontBy_zero` (…/K12/PlayedTerm.lean), `length_aFold`
(Johnson/Desc/K12/Honest/Causal.lean) and the frame's authors' `play_opened` (Honest/Gap.lean:
`play` leaves the columns handed as they are) the proof derives four equations: `restFront J y.2` is
`frontBy m₀ 0`; the last `firstLen` challenges that y.2 has heard are ds; `heardIn J y.2` is D below
`firstLen`; the last `firstLen` rounds of `front.seen` are "BAT" and `aFold` at `firstRd J c`. Then
`heard` follows by `foldShown_drawn` (Sim/PlayedFirst.lean); `fold` by `aFold_coins`
(Sim/PlayedFirst.lean), from the fields `hide` and `table` of `Agree`, and by `aFold_congr`
(Causal.lean); `asks` by `shapeAsks_congr` and `dataAsks_congr` (Sim/PlanCausal.lean); `door` and
`tree` by rewriting. The field `tails` of `Agree` is not used.

Hypotheses. `onFree_of_play` has five, and a sixth inside its conclusion:
  `T : FirstTies J s next rest D ds` (Sim/ShowsFirst.lean): on the test's parameters and on the
    challenges. Among its fields: the list of stages is s :: next :: rest; ds has `firstLen`
    entries; entry number n of ds is D n
  `hk`: k = h + g at the first stage, that is h ≤ k
  `hfit`: ds has the form that the first `firstLen` declared rounds declare (`drawsFit`,
    Frame.lean). The declared rounds are `laidOf J.p` (Johnson/Desc/K12/Law/ReadsK.lean), defined by
    the same term as `J.laid`, from which `firstMember` takes its rounds
  `Ag`: `Agree` at `m₀.st.input`, `frontBy m₀ 0` and s, between `firstRd J c` and
    `carriedCoins J mem`
  `E`: `AtEntry` at `m₀.st.input`, `frontBy m₀ 0`, D and front
  `y.2.seen = front.seen`, a hypothesis inside the conclusion, before `OnFree`

Limits.
- `FirstTies`, h ≤ k at the first stage, `Agree` and "what is shown in front is what the run has
  shown" (the frame's own premise at the second member) are asked. So is the declared form of the
  first part's challenges (`hfit`).
- Whether a run meets `AtEntry` at any place of a file is not shown.
- No member of `AtEntry` is given by name.
- `J.rec₀` and `Js.rec₀` are fields of free parameters, and `door` compares them with each other
  only. No statement that this state is the verifier's.
- By type the three clauses of `AtEntry` read the input w; `asks` and `tree` also read mem, the
  coins that the second part carries.
- `Agree` is proved here at no coins. Where the first fold sends its own table, the theorem that is
  cited for it does not apply (see "The five"). Where the table has come earlier, that theorem ends
  at `restCoins`, not at `carriedCoins`; `agree_carried` (Sim/OnFromLent.lean) goes from the one to
  the other, and `onFree_of_lent` (same file) joins the three. Its test on the book (`tiesB`) is
  evaluated in TiesAtKey.lean, at the key file's book. No value at which all hypotheses of
  `onFree_of_play` hold together is given by name.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFree
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedFirst
import Johnson.Desc.ProofFile.Honest.K12.CoinsAgree
import Johnson.Desc.ProofFile.Honest.Gap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {V W X Pb : Type}

theorem take_behind {α : Type} (a b : List α) (n : ℕ) (h : b.length = n) :
    (a ++ b).take ((a ++ b).length - n) = a := by
  rw [List.length_append, h, Nat.add_sub_cancel, List.take_left']
  rfl

theorem drop_behind {α : Type} (a b : List α) (n : ℕ) (h : b.length = n) :
    (a ++ b).drop ((a ++ b).length - n) = b := by
  rw [List.length_append, h, Nat.add_sub_cancel, List.drop_left']
  rfl

/-- The three clauses of `OnFree` that `onFree_of_play` takes as hypotheses, stated at the test's
entry. w: the input. fr: the front (`Front`); `onFree_of_play` takes it as the first part's moves
build it. D: the challenges by the round's number in the test. `door` compares the two jobs' fields
`rec₀`. No statement that this state is the verifier's. -/
structure AtEntry (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (o : Fmt.Shape × Fmt.TreeSource) (pb : Pb) (mem : ℕ → Stretch) (w : W) (fr : Front X)
    (D : ℕ → Fmt.Drawn) (front : Before) : Prop where
  door : J.rec₀ w fr = Js.rec₀ pb (front.cut (firstLen J.p.nums.stages))
  asks : ∃ Dp cc R, Dp.ts.length = 1 ∧ ShapeAsks J w fr (carriedCoins J mem) D K Dp ∧
    DataAsks J w fr (carriedCoins J mem) D Dp cc R
  tree : ∃ colR cols, J.trees₀ w fr mem (J.first w fr (carriedCoins J mem)) =
      [((sgOf J.s₀).C.a, colR)] ∧
    front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2 = some cols ∧
    ∀ q ∈ cols, q.2 = colR q.1

/-- **Where the play of the first part ends, `OnFree` follows from the three.** The three are the
fields of `AtEntry`. The play returns a pair y and keeps the input, and `OnFree` is concluded at the
state y.2, where `y.2.seen = front.seen`. The hypotheses T, hk, hfit, Ag and E are described in the
file's head. -/
theorem onFree_of_play (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (o : Fmt.Shape × Fmt.TreeSource) (pb : Pb) (mem : ℕ → Stretch) (name : String) (ad : Addr)
    (v : Option V) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (m₀ : Mid W X)
    (D : ℕ → Fmt.Drawn) (ds : List Fmt.Drawn) (T : FirstTies J s next rest D ds)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (c : (firstPart J : Part V W X).Coins)
    (hfit : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1)) ds = true)
    (Ag : Agree J m₀.st.input (frontBy m₀ 0) s (firstRd J c) (carriedCoins J mem))
    (front : Before)
    (E : AtEntry J Js K chain o pb mem m₀.st.input (frontBy m₀ 0) D front) :
    ∃ y, play ((firstPart J : Part V W X).steps name ad (J.laid.take (firstLen J.p.nums.stages)) v
        c) ds [] m₀ = .ok y ∧ y.2.st.input = m₀.st.input ∧
      (y.2.seen = front.seen → OnFree J Js K chain o pb mem y.2 front) := by
  obtain ⟨y, hy, h1, h2, -⟩ := first_played J name ad v s next rest m₀ D ds T hk c
  refine ⟨y, hy, by rw [h1], fun hseen => ?_⟩
  have hn : firstLen J.p.nums.stages = 2 + s.k := by rw [T.stages]; rfl
  have hs0 : J.s₀ = s := by unfold TestJob.s₀; rw [T.stages]; rfl
  have hA : stA J.p = s := by unfold stA; rw [T.stages]; rfl
  have hlenA : ((⟨[], D 0⟩ : Fmt.RoundView) ::
      aFold (coinsOf (s :: next :: rest) (firstRd J c).hide (firstRd J c).rest) 0 s 1
        (J.first m₀.st.input (frontBy m₀ 0) (firstRd J c))
        (rowOf (J.recB m₀.st.input (frontBy m₀ 0) (D 0))) D).length =
      firstLen J.p.nums.stages := by
    rw [List.length_cons, length_aFold, hn, hk]
    omega
  have hin : y.2.st.input = m₀.st.input := by rw [h1]
  have hheard : y.2.st.heard = m₀.st.heard ++ ds := by rw [h1]
  have hown : y.2.st.own = m₀.st.own := by rw [h1]
  -- the `Front` that the second part's moves build (`restFront`) is the one at the test's entry
  have hop : y.2.opened = m₀.opened := ProofFile.Honest.play_opened _ _ _ _ _ hy
  have hfr : restFront J y.2 = frontBy m₀ 0 := by
    unfold restFront
    rw [frontBy_zero]
    simp only [frontOf, Mid.shown, Seen.front, hheard, hown, h2, hop, take_behind _ _ _ T.len,
      take_behind _ _ _ hlenA] <;> rfl
  have hlat : y.2.st.lately (firstLen J.p.nums.stages) = ds := by
    unfold State.lately
    rw [hheard, drop_behind _ _ _ T.len]
  have hD : ∀ i, i < firstLen J.p.nums.stages → heardIn J y.2 i = D i := fun i hi => by
    unfold heardIn
    rw [hlat, List.getD_eq_getElem _ _ (by rw [T.len]; exact hi)]
    exact T.own i _
  have hlast : lastSeen front (firstLen J.p.nums.stages) = ⟨[], D 0⟩ ::
      aFold (coinsOf (s :: next :: rest) (firstRd J c).hide (firstRd J c).rest) 0 s 1
        (J.first m₀.st.input (frontBy m₀ 0) (firstRd J c))
        (rowOf (J.recB m₀.st.input (frontBy m₀ 0) (D 0))) D := by
    unfold lastSeen
    rw [← hseen, h2, drop_behind _ _ _ hlenA]
  have hag : ∀ n, n < 1 + (1 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g)) →
      D n = heardIn J y.2 n := fun n hn' => by
    rw [hA] at hn'
    exact (hD n (by rw [hn, hk]; omega)).symm
  obtain ⟨Dp, cc, R, hT, Sh, Dt⟩ := E.asks
  obtain ⟨colR, cols, htr, hl, hq⟩ := E.tree
  refine
    { le := by rw [hheard, List.length_append, T.len]; omega
      leS := by rw [h2, List.length_append, hlenA]; omega
      heardFit := by rw [hlat]; exact hfit
      heard := ?_
      door := by rw [hin, hfr]; exact E.door
      fold := ?_
      asks := ⟨Dp, cc, R, hT, by rw [hin, hfr]; exact shapeAsks_congr J _ _ _ D _ hag Sh,
        by rw [hin, hfr]; exact dataAsks_congr J _ _ _ D _ hag Dt⟩
      tree := ⟨colR, cols, by unfold rowsAt; rw [hin, hfr]; exact htr, hl, hq⟩ }
  · -- the challenges that the shown rounds bear are those heard
    rw [hlast, hlat, List.map_cons]
    show D 0 :: (foldShown (sgOf s) _ _ _ fun n => D (1 + n)).map (·.drawn) = ds
    rw [foldShown_drawn]
    refine List.ext_getElem (by simp [T.len, hn, hk]; omega) fun i h3 h4 => ?_
    rw [T.own i h4]
    cases i with
    | zero => rfl
    | succ j => simp [Nat.add_comm]
  · rw [hlast, List.tail_cons]
    unfold rowsAt
    rw [hin, hfr, hD 0 (by rw [hn]; omega), hs0, T.stages]
    refine (aFold_coins (coinsOf (s :: next :: rest) (firstRd J c).hide (firstRd J c).rest)
      (coinsOf (s :: next :: rest) (carriedCoins J mem).hide fun _ => 0) 0 s 1 _ _ _ D Ag.hide
      Ag.table).trans ?_
    exact aFold_congr _ _ _ _ _ _ _ _ fun n hn' => (hD n (by rw [hn, hk]; omega)).symm

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.take_behind
#print axioms ProofFile.Honest.K12.drop_behind
#print axioms ProofFile.Honest.K12.onFree_of_play
#print axioms ProofFile.Honest.K12.AtEntry
