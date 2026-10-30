-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ShowsFirst.lean: what the frame's own play makes of a
proximity test's first part, played alone at its own rounds (`Side.shows`,
Johnson/Desc/ProofFile/Honest/Side.lean), is what is shown of the term's first rounds (`testAll`,
…/K12/Test.lean). An equation (`shows_first`), under one structure of hypotheses (`FirstTies`).
Under these hypotheses a statement on `Side.shows` at the first member can be rewritten as one on
`testAll`: Sim/ExactFirst.lean does so. It holds at every job and challenges that meet `FirstTies`,
and at every side, face, state from which the part is played, coins that the part is given and
positions to be read.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean, and `play` there runs a list of
rounds at given challenges. A part (`Part`, the frame) is the prover's side of a stretch of a
sub-protocol's rounds: one move (`Move`) for each round, and two stops (`bad`, `hid`). A member
(`Member`, Honest/Side.lean) is a part with its number, its declared rounds and a term of type
`Sim`. A side σ (`Side`, Honest/Side.lean) is a sub-protocol with a list of parts, each paired with
a term of type `Sim`; a face φ (`Face`, the frame) says how a chain's parts are given their input.
The state m (`Mid`, the frame) is that of a chain's run between two rounds. Files named without a
folder, and the folder Sim/, are in Johnson/Desc/ProofFile/Honest/K12/. A job J (`TestJob`,
Test.lean) is what a caller supplies for its test. `J.p` (`P12`, Johnson/Desc/K12/Frame.lean) holds
the test's parameters, among them its place and its list of stages; `laidOf J.p`
(Johnson/Desc/K12/Law/ReadsK.lean) is the place's declared rounds, each with its oracle messages.
The term is `testAll J w fr K D`, of type `BOut` (Johnson/Prover/Link/BodyAll.lean): the test's
rounds, for each round the written column of the tree that it sends, and the groups of columns that
the rounds' openings are given. There w is the input, fr the front (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes the test), K the coins that the term reads
(`TestCoins`, Test.lean) and D the sampled challenges, by the round's number in the test. Round 0 is
"BAT". The first part (`firstPart`, Parts.lean) has the test's first `firstLen` (Parts.lean) rounds:
at two stages or more, "BAT" and the first fold. `firstMember J Js` (Sim/Row.lean) is the first
member, written out. The first fresh table is the first fold's; the job's field `fresh` names the
part that sent it, or is `none`: the fold sends it itself.

  `shows_first`: the statement, whoever sends the first fresh table. Under `FirstTies`, `Side.shows`
    at `firstMember J Js` returns `some` of the list `shownFrom` (Sim/Sims.lean) at the term: for
    each i below `firstLen`, the message that `sendingOf` (Sim/Sims.lean) cuts out of the term at
    round number i, with the depth, if any, that `depthAt` (Test.lean) gives for that round, as
    `shownAs` (Sim/Sims.lean) shows it at entry number i of asks, or at no position where asks has
    no such entry. The term is taken at the input of m, at the front that `frontBy` (PlayLaw.lean)
    reads off m at 0, at the coins `firstRd J c` (HalfSteps.lean) and at D
  `FirstTies`: a structure: the hypotheses of `shows_first`, on the test's parameters and on the
    challenges; field by field in its docstring

By what. That the part's moves are those of the rounds from 0 on, that its steps hold them, that no
stop of it speaks, that every message fits what its round states, that the play returns, and what a
play that has returned has shown are this folder's parent's (`first_moves`, `steps_at`,
HalfSteps.lean · `first_quiet`, `part_quiet`, HalfReturns.lean · `fits_all`, FitsAll.lean ·
`play_returns`, PlayReturns.lean · `play_test`, PlayLaw.lean): called. `shows_first` joins these at
one part, as `shows_rest` (Sim/Shows.lean) does at the second part, with `shown_of_played`
(Sim/Shows.lean) and `msgAt_eq` (Sim/Sims.lean). The hypothesis `Heard` (PlayLaw.lean) of
`play_returns` and `play_test` is taken at 0 rounds, where it holds at every m. The member's rounds
are `J.laid` (Test.lean) up to `firstLen`; the proof takes `J.laid` for `laidOf J.p`, which is
defined by the same term.

Limits.
- `FirstTies` is asked: two stages or more · the place has at least as many declared rounds as the
  part has moves · the declared rounds ask the sorts that the term shows · each declared oracle
  message has the depth and the width of the tree that the term sends · as many challenges as
  rounds. Its fields, in this order: `stages` · `enough` · `sorts` · `tables` · `len`. The field
  `own` adds: the challenges are those of D from number 0 on. `FirstTies` is proved at no job in
  this file.
- σ is a free parameter: `Side.shows` reads of it the sub-protocol's name and place only, and
  nothing ties that place to `J.p.place`. That `firstMember J Js` is a member of σ is neither a
  hypothesis nor proved.
- The job's functions for the state on entry to the test, for the first stage's tables and for the
  trees that the first round of positions opens are the caller's: nothing here compares them with
  anything.
- `FirstTies` has no clause that compares h and k of the first stage. The term reads the hiding
  polynomial's coefficients by `hideAt` (Coins.lean) at h + (k - h) variables (Test.lean;
  Coins.lean): at the numbers 0 to 2 (h + (k - h)) of the field `hide` of its coins. Where the fold
  sends its own table, `firstRd` (HalfSteps.lean) gives the whole range of the part's own coins as
  `hide`, and the same range from number 2 k + 1 on as `tails` (`tailsIn`, Parts.lean); `restCoins`
  (Parts.lean) does the same with the range that the second part carries. So where h > k the numbers
  2 k + 1 to 2 h are read both as coefficients and as tails. `exact_first` (Sim/ExactFirst.lean) and
  `exact_first_own` (Sim/ExactFirstOwn.lean), which call `shows_first`, have h ≤ k at the first
  stage among their hypotheses: the field `form` of `FirstPub` and of `FirstPubOwn` is
  `formPubB J.p = true`, whose first conjunct it is (FormPubAt.lean).
- `firstRd` gives 0 for the field `rest` of the term's coins and, where `J.fresh` names a part, 0
  for the field `tails`. That the term's first `firstLen` rounds read neither field there is not
  stated here.
- No property is claimed; nothing here speaks of a law or of a simulator. `Js` (`SimJob`,
  Sim/Sims.lean) is a free parameter: it enters through the member's field `sim` only, which
  `Side.shows` does not read.
- At the level of oracle messages: no root, salt or hash.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Shows
import Johnson.Desc.ProofFile.Honest.K12.HalfReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {S Cl V W X Pb : Type}

/-- The hypotheses of `shows_first`: on the test's parameters and on the challenges. D: the test's
challenges, by the round's number in the test. ds: the challenges of the first part's rounds.
`stages`: the list of stages is s :: next :: rest, so two stages or more. `enough`: the place's
declared rounds, `laidOf J.p` (Johnson/Desc/K12/Law/ReadsK.lean), are at least `firstLen` rounds.
`sorts`: the items of all these rounds, the roots apart (`asked`,
Johnson/Prover/Link/BodySorts.lean), are none for "BAT" and then those of `bodyItems`
(Johnson/Prover/Link/LinkItems.lean). `tables`: `tablesFitB` (FitsAll.lean) passes. `len`, `own`: ds
has `firstLen` entries, and entry number n is D n. -/
structure FirstTies (J : TestJob W X) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (D : ℕ → Fmt.Drawn) (ds : List Fmt.Drawn) : Prop where
  stages : J.p.nums.stages = s :: next :: rest
  enough : firstLen J.p.nums.stages ≤ (laidOf J.p).length
  sorts : (laidOf J.p).map asked = [] :: bodyItems s (next :: rest)
  tables : tablesFitB J = true
  len : ds.length = firstLen J.p.nums.stages
  own : ∀ n (h : n < ds.length), ds[n] = D n

/-- **What the first part shows, played alone.** Under `FirstTies`, at every face φ, side σ, `Js`,
state m, coins c and positions asks, `Side.shows` at `firstMember J Js` returns `some` of
`shownFrom` (Sim/Sims.lean) at `testAll`, over the first `firstLen` rounds, with the depths of
`depthAt`. `testAll` is at the input of m, at the front that `frontBy` reads off m at 0, at the
coins `firstRd J c` and at D. -/
theorem shows_first (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (m : Mid W X) (D : ℕ → Fmt.Drawn)
    (ds : List Fmt.Drawn) (T : FirstTies J s next rest D ds)
    (c : (firstMember J Js : Member V W X Pb).part.Coins) (asks : List (List (List ℕ))) :
    σ.shows φ (firstMember J Js) c m ds asks =
      some (shownFrom (testAll J m.st.input (frontBy m 0) (firstRd J c) D) (depthAt J)
        (firstLen J.p.nums.stages) asks) := by
  have hrs : (J.laid.take (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    rw [List.length_take]
    exact Nat.min_eq_left T.enough
  obtain ⟨hl, hm⟩ := steps_at J (firstPart J : Part V W X) (firstRd J) 0
    (firstLen J.p.nums.stages) (first_moves J) σ.block.name ⟨σ.block.place, 0⟩
    (J.laid.take (firstLen J.p.nums.stages)) hrs (φ.sees m.st.input) c
  have hq := part_quiet (firstPart J : Part V W X) (first_quiet J).1 (first_quiet J).2
    σ.block.name ⟨σ.block.place, 0⟩ (J.laid.take (firstLen J.p.nums.stages)) (φ.sees m.st.input) c
  have hfit : ∀ i (h : i < ((firstPart J : Part V W X).steps σ.block.name ⟨σ.block.place, 0⟩
      (J.laid.take (firstLen J.p.nums.stages)) (φ.sees m.st.input) c).length),
      (msgAt J m.st.input (frontBy m 0) (firstRd J c) D (0 + i)).fits
        (((firstPart J : Part V W X).steps σ.block.name ⟨σ.block.place, 0⟩
          (J.laid.take (firstLen J.p.nums.stages)) (φ.sees m.st.input) c)[i]).decl
        (((firstPart J : Part V W X).steps σ.block.name ⟨σ.block.place, 0⟩
          (J.laid.take (firstLen J.p.nums.stages)) (φ.sees m.st.input) c)[i]).oracles = true := by
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
  have hp := (play_test J (fun _ => firstRd J c) D _ 0 ds [] m y hm hy hH hown).1
  rw [hl] at hp
  show ((play ((firstPart J : Part V W X).steps σ.block.name ⟨σ.block.place, 0⟩
    (J.laid.take (firstLen J.p.nums.stages)) (φ.sees m.st.input) c) ds [] m).toOption.map
      fun y => _root_.ProofFile.Honest.shownOf y.1 asks) = _
  rw [hy]
  show some (_root_.ProofFile.Honest.shownOf y.1 asks) = _
  rw [shown_of_played y.1 _ _ _ hp asks]
  unfold shownFrom
  refine congrArg some (List.map_congr_left fun i _ => ?_)
  rw [Nat.zero_add, msgAt_eq]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.shows_first
#print axioms ProofFile.Honest.K12.FirstTies
