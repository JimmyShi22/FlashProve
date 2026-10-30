-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/OnFromLent.lean: at the coins that the frame lends to the row
of a proximity test's two parts, where the frame's own play of the first part ends, the condition
`OnFree` (Sim/ExactFree.lean) follows from three clauses at the test's entry (`AtEntry`,
Sim/OnFromPlay.lean). Where the first fold's fresh table has come earlier. General in the book, the
run's coins, the job and where the run stands. The theorem is `onFree_of_lent`; next to the three
clauses it has the hypotheses that are listed below. It is also general in the simulators' job Js
and in K, chain, o, pb, front, name, ad and v. `OnFree` is the condition at the second part's entry
under which `exact_free` (Sim/ExactFree.lean) is stated, at a state on entry that is made of the
plan's public part, not shown to be the verifier's. Two theorems with their proofs.

Terms. …/K12/ is Johnson/Desc/ProofFile/Honest/K12/, and Sim/ is a folder in it. The frame is
Johnson/Desc/ProofFile/Honest/Frame.lean. A part (`Part`, the frame) is the prover's side of some
rounds in a row. A job J (`TestJob`, …/K12/Test.lean) is what a caller supplies for its proximity
test. `onFree_of_lent` writes it out as ⟨p, ms, some f, r, ro, tr⟩: p has the test's place `p.place`
and its list of stages `p.nums.stages`; ms lists the job's members, the group's oracle messages;
`some f` is the field `fresh` and says that the first fold's fresh table has come earlier; r, ro and
tr are the fields `rec₀`, `rows₀` and `trees₀`. All six are free parameters. The simulators' job Js
(`SimJob`, Sim/Sims.lean) is what a caller says of its test to the simulators. The two jobs' letters
at the door are their fields `rec₀`. The first part is `firstPart J`, with the test's first
`firstLen` rounds, and the second part is `restPart J`, with all the others (…/K12/Parts.lean); the
row is the list of the two. A book Bk (`ProverCoinCounts`, the frame) is public data; an entry of it (`Ahead`)
is a block of one part's coins that one other part is given too, marked as spent or as carried. By
the book, `lendRow` (the frame) gives the parts of a row their coins or returns an error; lent coins
are what it gives. look gives, by address, the coins that the chain may be given: the run's coins
enter by this free parameter only. rows, a table of the parts' own counts, is a free parameter too.
c (`RowCoins`, the frame) is what `lendRow` returns: `c.1` is for the first part and `c.2.1` for the
second, each with the part's own coins, the blocks that it spends and the blocks that it carries
(`Handed`, the frame). A stretch (`Stretch`, …/K12/Coins.lean) is a run of coins, read by number,
and `stretches _ c.2.1.2.2` gives the stretches that the second part carries, by number. A part's
reader makes of what the part is given the coins that its moves read, a `TestCoins`
(…/K12/Test.lean; fields `hide`, `tails`, `mem`, `rest`): `firstRd J` (…/K12/HalfSteps.lean) and
`restCoins J` (…/K12/Parts.lean). `carriedCoins J mem` (Sim/Row.lean) is a `TestCoins` made of the
carried stretches mem, with 0 in the field `rest`. `Agree` (…/K12/CoinsAgree.lean) is a structure of
three clauses on two values of `TestCoins`: `hide`, `table` and `tails`. `play` (the frame) runs a
list of steps, one round each, at a list of challenges, from a state of a chain's run between two
rounds (`Mid`); it returns an error or a pair y, and y.2 is the state after these rounds. m₀ is the
state from which the first part is played: it is the test's entry, and "where the run stands" speaks
of it. The second part's entry is y.2. w is the prover's input, and fr is a front (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean): what the job's functions are given of the run before the
test. `frontBy m₀ 0` (…/K12/PlayLaw.lean) is the front read off m₀. The parameter front has another
type, `Before` (the frame), and `front.seen` gives its rounds in the form of `m₀.seen`. ds is the
list of the first part's challenges; D gives the test's challenges by the round's number, counted
from 0. The parameter s is the first stage; k is its field `k`, and h and g are those of `sgOf s`
(Johnson/Desc/K12/Law/ChainOf.lean), where g is k - h. A place of a file is the place of a test in
one of the files that the library describes. What is asked is a hypothesis. In "No member is given
by name", a member is a choice of values at which the hypotheses hold together.

  `onFree_of_lent`: the statement. In Lean: under the hypotheses below there is a y such that `play`
    of the first part's steps at the coins `c.1`, at ds and from m₀, returns y; `y.2.st.input` is
    `m₀.st.input`; and, where `y.2.seen = front.seen`, `OnFree` holds at J, Js, K, chain, o, pb, the
    stretches that the second part carries, y.2 and front
  `agree_carried`: what the second part's moves read of lent coins and what `carriedCoins` lays
    agree with the first part's reader alike: the two differ in the part's own coins alone. In Lean:
    from `Agree J w fr s K₁ (restCoins J c)` follows
    `Agree J w fr s K₁ (carriedCoins J (stretches _ c.2.2))`. Only this direction is stated, and
    there is no other hypothesis. The two values of `TestCoins` differ in the fourth field, `rest`,
    only, and none of the three clauses of `Agree` reads that field. The theorem holds at every job
    J, at every K₁ of type `TestCoins`, which need not come from the first part's reader, and at all
    coins c of the second part's type, lent or not

By what. `onFree_of_play` (Sim/OnFromPlay.lean) asks that the two parts' readers agree on what the
first fold reads. At lent coins that is `agree_of_ties` (…/K12/AgreeBook.lean): called: from a test
with code on the book's entries (`tiesB`) and a clause on the job's text. In Lean: as it is called
here, `onFree_of_play` asks `Agree` between `firstRd J c.1` and `carriedCoins J` at the stretches
that the second part carries. `tiesB` is a definition that returns a `Bool`, and the clause on the
job's text is `hrows`. `agree_of_ties` has two more hypotheses, that the lending returns and that
k = h + g at the first stage, and it concludes `Agree` between `firstRd J c.1` and
`restCoins J c.2.1`; `agree_carried` goes from there to `carriedCoins`. So `onFree_of_lent` is
`agree_of_ties`, then `agree_carried`, then `onFree_of_play`, after `J.s₀ = s`, which follows from
the field `stages` of `FirstTies`. `agree_carried` passes on the three fields of its hypothesis.

Hypotheses. `onFree_of_lent` has seven, and an eighth inside its conclusion:
  `hl`: `lendRow Bk rows look p.place` at the row of the two parts, from part number 0 on, returns c
  `hT`: `tiesB Bk p.place ms.length = true`: the test on the book's entries passes at the test's
    place and the number of the job's members
  `T : FirstTies J s next rest D ds` (Sim/ShowsFirst.lean): on the test's parameters and on the
    challenges. Among its fields: the list of stages is s :: next :: rest; ds has `firstLen`
    entries; entry number n of ds is D n
  `hk`: k = h + g at the first stage, that is h ≤ k
  `hrows`: at `m₀.st.input` and `frontBy m₀ 0`, `μOf (sgOf s)` (Johnson/Prover/Link/BodyState.lean)
    of what ro returns is the same at any two families of stretches that agree at every number below
    `ms.length`
  `hfit`: ds has the form that the first `firstLen` declared rounds declare (`drawsFit`, the frame).
    The declared rounds are `laidOf p` (Johnson/Desc/K12/Law/ReadsK.lean)
  `E`: `AtEntry J Js K chain o pb` at the stretches that the second part carries, `m₀.st.input`,
    `frontBy m₀ 0`, D and front. Its clauses `door`, `asks` and `tree` are described in the head of
    Sim/OnFromPlay.lean
  `y.2.seen = front.seen`, a hypothesis inside the conclusion, before `OnFree`

Limits.
- Asked: the lending returns · `tiesB` · "the first stage's message reads of the members' stretches
  those of the job's members alone" · `FirstTies` · h ≤ k at the first stage · the first part's
  challenges have the declared form · and `AtEntry`: the two jobs' letters at the door agree; the
  state's shape and the prover's data; one tree, listed, and what is listed is the tree's. So is
  `y.2.seen = front.seen`, inside the conclusion.
- Whether a run meets `AtEntry` at any place of a file is not shown.
- No member is given by name.
- The case in which the first fold sends its own table is not treated: the job is written with
  `some f`, and `agree_of_ties` is stated there only.
- r, the job's field `rec₀`, is a free parameter, and `Js.rec₀` is a field of one; `door` compares
  them with each other only. No statement that this state is the verifier's.
- By type the three clauses of `AtEntry` read the input; `asks` and `tree` also read the stretches
  that the second part carries, which are taken from c here. `hrows` reads the input too.
- The play is that of the first part's steps only; name, ad and v are free parameters. It is not
  joined here with a play of the row or of a chain.
- No property is claimed. Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.OnFromPlay
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {V W X Pb : Type}

/-- The second part's reader and `carriedCoins` differ in the part's own coins alone. In Lean:
`restCoins J c` and `carriedCoins J (stretches _ c.2.2)` differ in the field `rest` only, which no
clause of `Agree` reads. So `Agree` between any K₁ and the first gives `Agree` between K₁ and the
second. -/
theorem agree_carried (J : TestJob W X) (w : W) (fr : Front X) (s : Fmt.M1.Stage) (K₁ : TestCoins)
    (c : (restPart J : Part V W X).Coins) (h : Agree J w fr s K₁ (restCoins J c)) :
    Agree J w fr s K₁ (carriedCoins J (stretches _ c.2.2)) :=
  ⟨h.hide, h.table, h.tails⟩

/-- **At lent coins, where the play of the first part ends, `OnFree` follows from the three.** The
three are the fields of `AtEntry` (Sim/OnFromPlay.lean). The play returns a pair y and keeps the
input, and `OnFree` is concluded at the state y.2, where `y.2.seen = front.seen`. The hypotheses hl,
hT, T, hk, hrows, hfit and E are described in the file's head. -/
theorem onFree_of_lent (p : P12) (ms : List (Addr × ℕ × Due)) (f : Addr × ℕ)
    (r : W → Front X → T12) (ro : W → Front X → (ℕ → Stretch) → PS)
    (tr : W → Front X → (ℕ → Stretch) → PS → List Tree) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (o : Fmt.Shape × Fmt.TreeSource) (pb : Pb) (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart ⟨p, ms, some f, r, ro, tr⟩ : Part V W X),
      restPart ⟨p, ms, some f, r, ro, tr⟩])
    (hl : lendRow Bk rows look p.place [(firstPart ⟨p, ms, some f, r, ro, tr⟩ : Part V W X),
      restPart ⟨p, ms, some f, r, ro, tr⟩] 0 = .ok c)
    (hT : tiesB Bk p.place ms.length = true) (name : String) (ad : Addr) (v : Option V)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (m₀ : Mid W X) (D : ℕ → Fmt.Drawn)
    (ds : List Fmt.Drawn)
    (T : FirstTies (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X) s next rest D ds)
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < ms.length → mem t = mem' t) →
      μOf (sgOf s) (ro m₀.st.input (frontBy m₀ 0) mem) =
        μOf (sgOf s) (ro m₀.st.input (frontBy m₀ 0) mem'))
    (hfit : drawsFit (((laidOf p).take (firstLen p.nums.stages)).map (·.1)) ds = true)
    (front : Before)
    (E : AtEntry (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X) Js K chain o pb
      (stretches _ c.2.1.2.2) m₀.st.input (frontBy m₀ 0) D front) :
    ∃ y, play ((firstPart ⟨p, ms, some f, r, ro, tr⟩ : Part V W X).steps name ad
        ((⟨p, ms, some f, r, ro, tr⟩ : TestJob W X).laid.take (firstLen p.nums.stages)) v c.1) ds []
        m₀ = .ok y ∧ y.2.st.input = m₀.st.input ∧
      (y.2.seen = front.seen → OnFree (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X) Js K chain o pb
        (stretches _ c.2.1.2.2) y.2 front) := by
  have hs0 : (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X).s₀ = s := by
    have := T.stages
    show p.nums.stages.headD default = s
    rw [show p.nums.stages = s :: next :: rest from this]
    rfl
  have Ag := agree_of_ties p ms f r ro tr Bk rows look c hl m₀.st.input (frontBy m₀ 0) hT
    (by rw [hs0]; exact hk) (by rw [hs0]; exact hrows)
  rw [hs0] at Ag
  exact onFree_of_play _ Js K chain o pb _ name ad v s next rest m₀ D ds T hk c.1 hfit
    (agree_carried _ _ _ _ _ c.2.1 Ag) front E

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.agree_carried
#print axioms ProofFile.Honest.K12.onFree_of_lent
