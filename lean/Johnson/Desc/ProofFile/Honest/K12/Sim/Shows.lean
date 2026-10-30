-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/Shows.lean: what the frame's own play makes of a proximity
test's second part, played alone at its own rounds (`Side.shows`,
Johnson/Desc/ProofFile/Honest/Side.lean), is what is shown of the text from the first switch on
(`restText`, Sim/Text.lean). Equations, one definition and one structure of hypotheses (`PlayTies`).
Under these hypotheses a statement on `Side.shows` at the second member can be rewritten as one on
`restText`. General in the job, the side, the face, the coins that the part is given and the
positions asked; the state of the run and the challenges are bound by `PlayTies`.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean, and `play` there runs a list of
rounds at given challenges. A part (`Part`, the frame) is the prover's side of a stretch of a
sub-protocol's rounds: one move (`Move`) for each round, and two stops (`bad`, `hid`). A member
(`Member`, Honest/Side.lean) is a part with its number, its declared rounds and a term of type
`Sim`. A side σ (`Side`, Honest/Side.lean) is a sub-protocol with a list of parts; a face φ (`Face`,
the frame) says how a chain's parts are given their input. m (`Mid`, the frame) is the state of a
chain's run between two rounds. A round as played (`Played`, the frame) has its items in the clear
(`vals`) and, for each root, the table if a prover's side sent it (`tables`). Files named without a
folder, and the folder Sim/, are in Johnson/Desc/ProofFile/Honest/K12/. A job J (`TestJob`,
Test.lean) is what a caller supplies for its test; `J.p` holds the test's parameters, among them its
place and its list of stages. The term is `testAll J w fr K D` (Test.lean), of type `BOut`
(Johnson/Prover/Link/BodyAll.lean): the test's rounds (`rs`), for each round the written column of
the tree that it sends (`tr`), and the groups of columns that the rounds' openings are given (`gs`).
There w is the input, fr the front (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes
the test), K the coins that the term reads (`TestCoins`) and D the sampled challenges, by the
round's number in the test. Round 0 is "BAT". A stage that is not the last has a fold and then a
switch. The first part (`firstPart`, Parts.lean) has the test's first `firstLen` rounds, the second
part (`restPart`) all the others: at two stages or more, "BAT" with the first fold, and then
`restLen` (HalfSteps.lean) rounds. `restMember J Js` (Sim/Row.lean) is the second member, written
out. `msgAt` (Parts.lean) is the message (`Sending`, the frame) of one round of the term.

  `shows_rest`: the statement. Under `PlayTies`, `Side.shows` at `restMember J Js` returns `some` of
    the list `shownFrom` (Sim/Sims.lean) at `restOf`: for each i below `restLen`, the message that
    `sendingOf` (Sim/Sims.lean) cuts out of `restOf` at its round number i, with the depth that
    `depthAt` (Test.lean) gives for the test's round number `firstLen` + i, as `shownAs`
    (Sim/Sims.lean) shows it at entry number i of asks. `restOf` is taken at the input of m, at the
    front that `frontBy` (PlayLaw.lean) reads off m at `firstLen`, at the coins `restCoins J c`
    (Parts.lean) and at D
  `shown_of_played`: rounds as played whose items and tables are given messages' are shown as these
    messages are. In Lean: if round number i of ps has the items and the tables of the message
    `Xs i` and the challenge `Ds i`, for the n rounds of ps (`shownOf`, `shownAt`, PlayLaw.lean),
    then the frame's `shownOf` (Honest/Side.lean) of ps at asks is, round by round, `shownAs (Xs i)`
    at entry number i of asks, or at no position where asks has no such entry
  `restOf`: a definition: `restText` at the arguments that `testAll` gives to `stagesAll`
    (Johnson/Desc/K12/Honest/Stages.lean) for the job J, at the list of stages s :: next :: rest,
    and at the state after the first fold that the first fold's rounds leave (`aRec1`, `aFold`, the
    same file)
  `testAll_cut`: where the job's list of stages is s :: next :: rest, the term is "BAT", the first
    fold's rounds and then `restOf`, in each of the three fields of `BOut`; where `J.fresh` is
    `none`, with the column `freshCol` (Test.lean) at the fold's first round
  `sending_cut`: there, and where k = h + g at the first stage: the message of the test's round
    number `firstLen` + i is cut out of `restOf` at its round number i, by `sendingOf`
  `PlayTies`: a structure: the hypotheses of `shows_rest`, on the test's parameters and on the state
    of the run before the second part; field by field in its docstring

By what. That the part's moves are those of consecutive rounds, that its steps hold them, that no
stop of it speaks (by its text), that every message fits what its round states, that the play
returns, and what a play that has returned has shown are this folder's parent's (`rest_moves`,
`steps_at`, HalfSteps.lean · `fits_all`, FitsAll.lean · `play_returns`, PlayReturns.lean ·
`play_test`, PlayLaw.lean): called. The part's text is `restPart` (Parts.lean), whose fields `bad`
and `hid` are written as `none` at all arguments. `shows_rest` joins these at one part, with
`shown_of_played` and `sending_cut`. The term's rounds are cut after the first fold: `testAll_cut`
by `stagesAll_cut` (Sim/Text.lean); `sending_cut` by `testAll_cut`, `msgAt_eq` (Sim/Sims.lean) and
`length_aFold` (Johnson/Desc/K12/Honest/Causal.lean).

Limits.
- `PlayTies` is asked: two stages or more · k = h + g at the first stage · the member's rounds are
  the place's declared rounds from `firstLen` on, as many as the part has moves · the declared
  rounds ask the sorts that the term shows · each declared oracle message has the depth and the
  width of the tree that the term sends · the run has heard the test's first rounds' challenges · as
  many challenges as rounds. Its fields, in this order: `stages` · `k` · `laid`, `count` · `sorts` ·
  `tables` · `heard` · `len`. The field `own` adds: the challenges are those of D from number
  `firstLen` on. `PlayTies` is proved at no job in this file.
- The field `laid` shuts out no job: `J.laid` (Test.lean) and `laidOf J.p`
  (Johnson/Desc/K12/Law/ReadsK.lean) are defined by the same term, so it holds at every J. That the
  member's rounds are `J.laid` from `firstLen` on is the text of `restMember` (Sim/Row.lean), not a
  hypothesis.
- `shownFrom` reads the fields `rs` and `tr` of `restOf`, not `gs`; `Side.shows` holds, besides the
  rounds' items, only columns of tables that this part sent. So the columns of `J.trees₀` that `gs`
  holds are on neither side of the equation.
- σ is a free parameter: `Side.shows` reads of it the sub-protocol's name and place only, and
  nothing ties that place to `J.p.place`. That `restMember J Js` is a member of σ is neither a
  hypothesis nor proved.
- The job's fields `rec₀` (the state on entry to the test), `rows₀` and `trees₀` are the caller's
  functions: nothing here compares them with anything.
- No property is claimed; nothing here speaks of a law or of a simulator. `Js` (`SimJob`,
  Sim/Sims.lean) is a free parameter: it enters through the member's field `sim` only, which
  `Side.shows` does not read.
- At the level of oracle messages: no root, salt or hash.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Row
import Johnson.Desc.ProofFile.Honest.K12.HalfSteps
import Johnson.Desc.ProofFile.Honest.K12.FitsAll
import Johnson.Desc.ProofFile.Honest.K12.PlayReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {S Cl V W X Pb : Type}

/-! ## 1 From rounds as played to what is shown -/

/-- Rounds as played whose items and tables are given messages' are shown as these messages are.
Hypothesis h: ps has n rounds, and round number i has the items in the clear and the tables of the
message `Xs i`, and the challenge `Ds i` (`shownOf`, `shownAt`, PlayLaw.lean). Then the frame's
`shownOf` (Honest/Side.lean) of ps at asks is, round by round, `shownAs (Xs i)` (Sim/Sims.lean) at
entry number i of asks; where asks has no such entry, at no position. -/
theorem shown_of_played (ps : List Played) (n : ℕ) (Xs : ℕ → Sending) (Ds : ℕ → Fmt.Drawn)
    (h : ps.map shownOf = (List.range n).map fun i => shownAt (Xs i) (Ds i))
    (asks : List (List (List ℕ))) :
    _root_.ProofFile.Honest.shownOf ps asks =
      (List.range n).map fun i => shownAs (Xs i) ((asks[i]?).getD []) := by
  have hl : ps.length = n := by
    have := congrArg List.length h
    simpa using this
  refine List.ext_getElem (by simp [_root_.ProofFile.Honest.shownOf, hl]) fun i h1 h2 => ?_
  have hi : i < ps.length := by simpa [_root_.ProofFile.Honest.shownOf] using h1
  have e : shownOf ps[i] = shownAt (Xs i) (Ds i) := by
    have := congrArg (fun l => l[i]?) h
    simpa [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_range (hl ▸ hi)] using this
  have e1 : ps[i].vals = (Xs i).vals.map Said.got := congrArg (·.1) e
  have e2 : ps[i].tables = (Xs i).tables.map some := congrArg (·.2.1) e
  simp only [_root_.ProofFile.Honest.shownOf, List.getElem_map, List.getElem_zipIdx, List.getElem_range,
    Nat.zero_add, e1, e2, shownAs, List.zipIdx_map, List.map_map]
  rfl

/-! ## 2 The whole term's rounds, cut after the first fold -/

section Cut
variable (J : TestJob W X) (w : W) (fr : Front X) (K : TestCoins) (D : ℕ → Fmt.Drawn)
  (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)

/-- The text from the first switch on (`restText`, Sim/Text.lean) at a job's own arguments: those
that `testAll` (Test.lean) gives to `stagesAll` where the job's list of stages is s :: next :: rest.
They are the parameters `J.p`; the coins `coinsOf` (Coins.lean) at that list, `K.hide` and `K.rest`;
the declared rounds after "BAT"; 1, the number of the first fold's first round; the first stage's
state `J.first`; the trees `J.trees₀`. The state after the first fold is `aRec1` at the state after
the batching (`J.recB`) and at the first fold's rounds (`aFold`). -/
def restOf : BOut :=
  restText J.p (coinsOf (s :: next :: rest) K.hide K.rest) s next rest (J.laid.drop 1) 1
    (aRec1 J.p 0 s (J.laid.drop 1) (J.recB w fr (D 0))
      (aFold (coinsOf (s :: next :: rest) K.hide K.rest) 0 s 1 (J.first w fr K)
        (rowOf (J.recB w fr (D 0))) D))
    (J.first w fr K) (J.trees₀ w fr K.mem (J.first w fr K)) D

/-- The whole term (`testAll`) at a list of two stages or more: "BAT", the first fold's rounds
(`aFold`), and the text from the first switch on (`restOf`). In the field `tr`, "BAT" and the fold's
rounds have a column without words; but where `J.fresh` is `none`, the fold's first round has
`freshCol`. The groups are those of `restOf`. -/
theorem testAll_cut (hst : J.p.nums.stages = s :: next :: rest) :
    testAll J w fr K D =
      ⟨⟨[], D 0⟩ :: (aFold (coinsOf (s :: next :: rest) K.hide K.rest) 0 s 1 (J.first w fr K)
          (rowOf (J.recB w fr (D 0))) D ++ (restOf J w fr K D s next rest).rs),
        (fun _ => []) :: (if J.fresh.isNone then
          ((aFold (coinsOf (s :: next :: rest) K.hide K.rest) 0 s 1 (J.first w fr K)
            (rowOf (J.recB w fr (D 0))) D).map (fun _ _ => []) ++
              (restOf J w fr K D s next rest).tr).set 0 (freshCol (sgOf s) (J.first w fr K))
          else (aFold (coinsOf (s :: next :: rest) K.hide K.rest) 0 s 1 (J.first w fr K)
            (rowOf (J.recB w fr (D 0))) D).map (fun _ _ => []) ++
              (restOf J w fr K D s next rest).tr),
        (restOf J w fr K D s next rest).gs⟩ := by
  unfold testAll restOf
  simp only [hst, stagesAll_cut]

/-- The message of the test's round number `firstLen` + i (`msgAt`, Parts.lean) is what `sendingOf`
(Sim/Sims.lean) cuts out of `restOf` at its round number i, with the depth that `depthAt` gives for
round number `firstLen` + i. Hypotheses: two stages or more; k = h + g at the first stage. -/
theorem sending_cut (hst : J.p.nums.stages = s :: next :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (i : ℕ) :
    msgAt J w fr K D (firstLen J.p.nums.stages + i) =
      sendingOf (restOf J w fr K D s next rest) (depthAt J (firstLen J.p.nums.stages + i)) i := by
  have hn : firstLen J.p.nums.stages = 2 + s.k := by rw [hst]; rfl
  have hlen : (aFold (coinsOf (s :: next :: rest) K.hide K.rest) 0 s 1 (J.first w fr K)
      (rowOf (J.recB w fr (D 0))) D).length = 1 + s.k := by
    rw [length_aFold, hk]
  have a1 : ∀ (x : Fmt.RoundView) (A C : List Fmt.RoundView), A.length = 1 + s.k →
      (x :: (A ++ C))[2 + s.k + i]? = C[i]? := fun x A C hA => by
    rw [show 2 + s.k + i = (1 + s.k + i) + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_append_right (by omega), hA]
    congr 1
    omega
  have a2 : ∀ (x : ℕ → List UInt64) (A C : List (ℕ → List UInt64)) (y : ℕ → List UInt64)
      (b : Bool), A.length = 1 + s.k →
      (x :: (if b = true then (A ++ C).set 0 y else A ++ C)).getD (2 + s.k + i) (fun _ => []) =
        C.getD i fun _ => [] := by
    intro x A C y b hA
    have e : ∀ L : List (ℕ → List UInt64), L[1 + s.k + i]? = (A ++ C)[1 + s.k + i]? →
        (x :: L).getD (2 + s.k + i) (fun _ => []) = C.getD i fun _ => [] := by
      intro L hL
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        show 2 + s.k + i = (1 + s.k + i) + 1 by omega, List.getElem?_cons_succ, hL,
        List.getElem?_append_right (by omega), hA]
      congr 2
      omega
    cases b with
    | false => exact e _ rfl
    | true => exact e _ (List.getElem?_set_ne (by omega))
  rw [msgAt_eq, testAll_cut J w fr K D s next rest hst, hn]
  unfold sendingOf
  simp only
  rw [a1 _ _ _ hlen, a2 _ _ _ _ _ (by rw [List.length_map]; exact hlen)]

end Cut

/-! ## 3 The part, played alone -/

/-- The hypotheses of `shows_rest`: on the test's parameters, and on the state m of the run before
the second part. D: the test's challenges, by the round's number in the test. ds: the challenges of
the second part's rounds. `stages`: the list of stages is s :: next :: rest, so two stages or more.
`k`: k = h + g at the first stage (`sgOf`). `laid`: the job's declared rounds are `laidOf J.p`
(Johnson/Desc/K12/Law/ReadsK.lean); the two are defined by the same term, so this holds at every
job. `count`: these are `firstLen` + `restLen` rounds. `sorts`: their
items, the roots apart (`asked`, Johnson/Prover/Link/BodySorts.lean), are none for "BAT" and then
those of `bodyItems` (Johnson/Prover/Link/LinkItems.lean). `tables`: `tablesFitB` (FitsAll.lean)
passes. `heard`: `Heard` (PlayLaw.lean) at `firstLen`: m has heard at least `firstLen` challenges,
the last `firstLen` of which are D 0, D 1 and so on, and it holds at least `firstLen` shown rounds.
`len`, `own`: ds has `restLen` entries, and entry number n is D (`firstLen` + n). -/
structure PlayTies (J : TestJob W X) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (m : Mid W X) (D : ℕ → Fmt.Drawn) (ds : List Fmt.Drawn) : Prop where
  stages : J.p.nums.stages = s :: next :: rest
  k : s.k = (sgOf s).h + (sgOf s).g
  laid : J.laid = laidOf J.p
  count : (laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages
  sorts : (laidOf J.p).map asked = [] :: bodyItems s (next :: rest)
  tables : tablesFitB J = true
  heard : Heard m (firstLen J.p.nums.stages) D
  len : ds.length = restLen J.p.nums.stages
  own : ∀ n (h : n < ds.length), ds[n] = D (firstLen J.p.nums.stages + n)

/-- **What the second part shows, played alone.** Under `PlayTies`, at every face φ, side σ, `Js`,
coins c and positions asks, `Side.shows` at `restMember J Js` returns `some` of `shownFrom`
(Sim/Sims.lean) at `restOf`, over `restLen` rounds, with the depths of `depthAt` from round number
`firstLen` on. `restOf` is at the input of m, at the front that `frontBy` reads off m at `firstLen`,
at the coins `restCoins J c` and at D. -/
theorem shows_rest (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (m : Mid W X) (D : ℕ → Fmt.Drawn)
    (ds : List Fmt.Drawn) (T : PlayTies J s next rest m D ds)
    (c : (restMember J Js : Member V W X Pb).part.Coins) (asks : List (List (List ℕ))) :
    σ.shows φ (restMember J Js) c m ds asks =
      some (shownFrom
        (restOf J m.st.input (frontBy m (firstLen J.p.nums.stages)) (restCoins J c) D s next rest)
        (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks) := by
  have hrs : (J.laid.drop (firstLen J.p.nums.stages)).length = restLen J.p.nums.stages := by
    rw [T.laid, List.length_drop, T.count]
    omega
  obtain ⟨hl, hm⟩ := steps_at J (restPart J : Part V W X) (restCoins J)
    (firstLen J.p.nums.stages) (restLen J.p.nums.stages) (rest_moves J s next rest T.stages)
    σ.block.name ⟨σ.block.place, 1⟩ (J.laid.drop (firstLen J.p.nums.stages)) hrs
    (φ.sees m.st.input) c
  have hq : ∀ st ∈ (restPart J : Part V W X).steps σ.block.name ⟨σ.block.place, 1⟩
      (J.laid.drop (firstLen J.p.nums.stages)) (φ.sees m.st.input) c,
      (∀ f o, st.bad f o = none) ∧ ∀ f o, st.hid f o = none := by
    intro st hst
    unfold Part.steps at hst
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hst
    refine ⟨fun _ _ => rfl, fun f o => ?_⟩
    show ((φ.sees m.st.input).bind fun u => (restPart J : Part V W X).hid u f o) = none
    cases φ.sees m.st.input with
    | none => rfl
    | some u => rfl
  have hfit : ∀ i (h : i < ((restPart J : Part V W X).steps σ.block.name ⟨σ.block.place, 1⟩
      (J.laid.drop (firstLen J.p.nums.stages)) (φ.sees m.st.input) c).length),
      (msgAt J m.st.input (frontBy m (firstLen J.p.nums.stages)) (restCoins J c) D
        (firstLen J.p.nums.stages + i)).fits
        (((restPart J : Part V W X).steps σ.block.name ⟨σ.block.place, 1⟩
          (J.laid.drop (firstLen J.p.nums.stages)) (φ.sees m.st.input) c)[i]).decl
        (((restPart J : Part V W X).steps σ.block.name ⟨σ.block.place, 1⟩
          (J.laid.drop (firstLen J.p.nums.stages)) (φ.sees m.st.input) c)[i]).oracles = true := by
    intro i h
    have hi : i < restLen J.p.nums.stages := hl ▸ h
    have hd : (laidOf J.p)[firstLen J.p.nums.stages + i]? =
        some ((J.laid.drop (firstLen J.p.nums.stages))[i]'(by rw [hrs]; exact hi)) := by
      rw [← T.laid, ← List.getElem?_drop, List.getElem?_eq_getElem]
    have := fits_all J m.st.input (frontBy m (firstLen J.p.nums.stages)) (restCoins J c) D s
      (next :: rest) T.stages T.sorts T.tables (firstLen J.p.nums.stages + i) _ hd
    simpa [Part.steps, List.getElem_zip] using this
  obtain ⟨y, hy⟩ := play_returns J (fun _ => restCoins J c) D _ (firstLen J.p.nums.stages) ds []
    m hm hq hfit T.heard (T.len.trans hl.symm) T.own
  have hp := (play_test J (fun _ => restCoins J c) D _ (firstLen J.p.nums.stages) ds [] m y hm hy
    T.heard T.own).1
  rw [hl] at hp
  show ((play ((restPart J : Part V W X).steps σ.block.name ⟨σ.block.place, 1⟩
    (J.laid.drop (firstLen J.p.nums.stages)) (φ.sees m.st.input) c) ds [] m).toOption.map
      fun y => _root_.ProofFile.Honest.shownOf y.1 asks) = _
  rw [hy]
  show some (_root_.ProofFile.Honest.shownOf y.1 asks) = _
  rw [shown_of_played y.1 _ _ _ hp asks]
  unfold shownFrom
  refine congrArg some (List.map_congr_left fun i _ => ?_)
  rw [sending_cut J _ _ _ D s next rest T.stages T.k i]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.shown_of_played
#print axioms ProofFile.Honest.K12.testAll_cut
#print axioms ProofFile.Honest.K12.sending_cut
#print axioms ProofFile.Honest.K12.shows_rest
#print axioms ProofFile.Honest.K12.restOf
#print axioms ProofFile.Honest.K12.PlayTies
