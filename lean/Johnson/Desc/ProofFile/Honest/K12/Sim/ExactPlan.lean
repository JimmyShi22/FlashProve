-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ExactPlan.lean: the frame's own sentence `exact` at a
proximity test's second member (`ExactMember`, Johnson/Desc/ProofFile/Honest/Small/Field.lean), at a
written `On` that reads none of the part's own challenges but in one clause, and at a written `bud`.
It is stated at a state on entry that is made of the plan's public part, not shown to be the
verifier's. Conditional on public ties. No property is claimed: whether a chain's run meets `OnPlan`
at any place is not shown. General in the face φ (`Face`), the side σ, the two jobs J and Js, the
table of codes K and the numbers chain and firstTree. Sim/ExactFree.lean and Sim/ExactAtKR.lean call
`exact_plan`. Definitions, statements and proofs.

Terms. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean with Honest/Side.lean. `exact` is a
field of its structure `Good`, and `ExactMember` is that field's text at one member. A side (`Side`)
has a sub-protocol and a list of the prover's parts (`Part`), each paired with a term of type `Sim`.
A member (`Member`) is one part with its number in the list, its declared rounds and that term. `On`
and `bud` are parameters of `Good`: a condition at a part's start, and which positions may be read
at given challenges. m (`Mid`) is the state of a chain's run between two rounds. The front
(`Before`) is what a part's simulator is given of the run before its part. A place (`P12`) holds the
numbers of a proximity test, among them its list of stages (`Fmt.M1.Stage`). A job J (`TestJob`,
…/K12/Test.lean) is what a caller supplies for its test, and the simulators' job Js (`SimJob`,
Sim/Sims.lean) is what a caller says of its test to the simulators. A job's letter is one of its
fields. The test's door is its entry, and each job's letter for the state there is its field `rec₀`.
The public ties are the fields of `PubTies`. The text is the Lean function that computes the test's
rounds (`testAll`, …/K12/Test.lean). The first part has the round "BAT" and the first fold's rounds
(`firstLen`), the second part all the others (`restLen`). The second member is `restMember J Js`
(Sim/Row.lean). ds is the list of the second part's own challenges, and same is the clause `same` of
`Asked` (Sim/Exact.lean).

  `exact_plan`: the statement: under `PubTies J Js K`: `ExactMember φ σ chain firstTree` at `On` :=
    `onPlan φ J Js K chain firstTree`, at `bud` := `budOpened J.p.nums.stages` and at the member
    `restMember J Js`; at a state on entry that is made of the plan's public part, not shown to be
    the verifier's
  `PubTies J Js K`: a structure: the hypotheses on public numbers and on the two jobs' public
    fields, listed under "Hypotheses"
  `OnPlan J Js K chain firstTree pb mem m front`: a structure: the hypotheses at the second part's
    entry, in eight clauses, each described at its field
  `onPlan`: a definition: `OnPlan` in the type of the frame's `On`. At a member whose number is not
    1 it asks nothing
  `budOpened`: a definition: `bud`: the positions asked of a tree are among those that the next
    reading round samples
  `laterOf`: a definition: the part's challenges by the round's number in the test; at a number
    below `firstLen` it gives what it gives at `firstLen`
  `same_of_ties`: `partEntry J mem m = Js.entry pb front` (Sim/Row.lean, Sim/Sims.lean), which is
    the clause same, from `Js.p = J.p` and the clauses `heard`, `door` and `fold` of `OnPlan`
  `openedTr_congr`: two families of challenges that agree from the next stage's first round on give
    the same list `openedTr` (Sim/CoreText.lean)
  `drawsFit_append`, `drawsFit_length`: on the frame's test `drawsFit`: it passes at two lists of
    declared rounds appended and their challenges appended if it passes at each; where it passes,
    there are as many challenges as declared rounds. The namespace `ProofFile.Honest` has lemmas of the
    same two short names: `drawsFit_length` (Johnson/Desc/ProofFile/Honest/Law/Along.lean) with the
    same statement, and `drawsFit_append` (Cut.lean in the same folder) with another: an equation of
    `drawsFit` at two lists appended with the two tests at the challenges cut in two

By what. `exact_rest` (Sim/Exact.lean), whose hypothesis is the structure `Asked` at the part's own
challenges ds. `exact_plan` proves the fields of `Asked` from `PubTies`, `OnPlan`, `budOpened` and
the hypotheses of `ExactMember`:
  The field `behind` comes from `behind_of_plan` (Sim/PlanLaw.lean), which takes `planB` and the
    three structures `ShapeAsks`, `FormAsks` and `DataAsks` (…/K12/PlanB.lean) at all the test's
    challenges (`drawnAll J m ds`, Sim/Exact.lean).
  The challenges' form (`FormAsks`) is no hypothesis: it follows from `drawsFit`, which
    `ExactMember` has as a hypothesis, and from "the first part's challenges, as heard, have the
    declared form" (`formAsks_of_draws`, …/K12/FormDraws.lean; `formPub_of_B`,
    …/K12/FormPubAt.lean).
  The sizes (the field `fits`) follow from the test on the place's public numbers and `drawsFit`
    (`reach_gives`, `counts_of_drawsFit`, Sim/Reach.lean).
  The state's shape and the prover's data (`ShapeAsks`, `DataAsks`) are hypotheses at the first
    part's challenges only (`shapeAsks_congr`, `dataAsks_congr`, Sim/PlanCausal.lean).
  In the place of the clause same stands a stronger pair, moved to the test's door: same follows
    from it (`same_of_ties`): `door`: the two jobs' letters for the verifier's state at the test's
    door agree · `fold`: the first fold's rounds, as shown in front, are those that the text makes
    at the carried coins.

Hypotheses. `exact_plan` has one, `PubTies J Js K`. Its eight fields:
  `place`: the two jobs have the same place: `Js.p = J.p`
  `own`: `Js.own` is `J.fresh.isNone`: the flag of Js is true just where J names no sender of the
    first fold's fresh table
  `reach`: `reachB J.p` passes (Sim/Reach.lean): three stages or more; the place's numbers say that
    the first fold sends no table of its own; h ≤ k after the first stage; the first reading round
    is declared to open one tree, of the first stage's depth; the sizes at the declared counts
  `plan`: `planB J.p K 1` passes (…/K12/PlanB.lean): a test on the place and the table of codes,
    here at one tree that the first switch opens
  `form`: `formPubB J.p` passes (…/K12/FormPubAt.lean): four clauses on the place
  `count`: the place has as many declared rounds (`laidOf`) as `firstLen` and `restLen` add up to
  `rounds`: `restLen` is 2 + `lenFrom` (…/K12/TermLen.lean) from the second stage on
  `tables`: `tablesFitB J` passes (…/K12/FitsAll.lean): round by round, the declared oracle messages
    have the depths and widths that `depthAt` and `widthsOf` give from the stages and
    `J.fresh.isNone`

Limits.
- It is stated at a state on entry that is made of the plan's public part, not shown to be the
  verifier's: `J.rec₀` is a field of the free parameter J, and no clause compares it with a
  verifier's state: `door` compares it with `Js.rec₀`, and `ShapeAsks` and `DataAsks` have clauses
  on it.
- What still reads ds in `OnPlan`: the clause `cols`: "at every list ds at which the front holds a
  column for every read that the part's rounds make, the listed column is the text's own tree's at
  the positions that the first reading round opens". It follows from the frame's premise
  `Before.holds` and a clause without ds ("what is listed is the tree's"): Sim/ExactFree.lean.
- same is not narrowed to what the text reads of the state.
- What, by reading, keeps an honest run from meeting same at the proof file's main test
  (Sim/Row.lean's head) stands in `door` now, and keeps it from meeting `door` there: by the same
  reading; no theorem.
- `OnPlan` has no value that meets it in the library. The library builds it from `OnFree` only
  (`onPlan_of_free`, Sim/ExactFree.lean). The statements that conclude `OnFree` take three of its
  clauses as premises, and where `ShapeAsks` and `DataAsks` are concluded together under the
  library's head it is at two trees, where `OnFree` asks one (the limits of Sim/ExactFree.lean name
  the statements): by reading the files that name them.
- `OnPlan` asks the prover's data (`DataAsks`), which reads the input and another part's coins, and
  the state's shape behind the first fold, which hangs by type on the rows.
- `bud` is a premise: a narrower one says less: `budOpened` is narrower than `budRest`
  (Sim/Row.lean): at the last tree it lets through the base case's positions alone, where `budRest`
  lets any r points through; that `budOpened` gives `budRest` is by reading: no theorem.
- One tree in front.
- Three stages or more; the first fresh table has come earlier. That is asked of the place
  (`ownMask` is false: `reachB`) and of the job's state on entry (its field `mask` is `some`:
  `ShapeAsks.came`, …/K12/PlanB.lean). Of the job's own field `fresh` it is not asked: no hypothesis
  is `J.fresh.isNone = false` or `TestJob.freshFits` (…/K12/Test.lean), and `own` only makes the two
  jobs say the same. Sim/ExactAtKR.lean and Sim/ExactFreeKR.lean have `J.fresh.isNone = false` as a
  hypothesis.
- The second member alone: nothing on the first, on `fresh`, on a lent run of coins.
- An honest verifier; fixed challenges.
- σ is a free parameter, and `restMember J Js` is the member as written out: that a side has it
  among its members is not stated here (`members_of_seat`, Sim/ExactSide.lean).
- The hypotheses on public numbers are proved at one of the library's nine closed places, the key
  file's test on the ranges (Sim/ExactAtKR.lean, Sim/ExactFreeKR.lean), where J and Js are free
  parameters too; at the two others where `reachB` says "true" they are not evaluated. The counts
  nine and two: by reading Sim/ReachAt.lean.
- At the level of oracle messages: no root, salt or hash. Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Exact
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlanLaw
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlanCausal
import Johnson.Desc.ProofFile.Honest.K12.Sim.Reach
import Johnson.Desc.ProofFile.Honest.K12.FormPubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (FitsBody openedAt qNext oNext)
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

/-! ## 1 Helpers -/

theorem drawsFit_append : ∀ (l₁ l₂ : List Fmt.DeclaredRound) (d₁ d₂ : List Fmt.Drawn),
    drawsFit l₁ d₁ = true → drawsFit l₂ d₂ = true → drawsFit (l₁ ++ l₂) (d₁ ++ d₂) = true
  | [], _, [], _, _, h => h
  | [], _, _ :: _, _, h, _ => by simp [drawsFit] at h
  | _ :: _, _, [], _, h, _ => by simp [drawsFit] at h
  | a :: l₁, l₂, b :: d₁, d₂, h, h' => by
    simp only [drawsFit, Bool.and_eq_true] at h
    simp only [List.cons_append, drawsFit, Bool.and_eq_true]
    exact ⟨h.1, drawsFit_append l₁ l₂ d₁ d₂ h.2 h'⟩

theorem drawsFit_length : ∀ (l : List Fmt.DeclaredRound) (d : List Fmt.Drawn),
    drawsFit l d = true → d.length = l.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [drawsFit] at h
  | _ :: _, [], h => by simp [drawsFit] at h
  | _ :: l, _ :: d, h => by
    simp only [drawsFit, Bool.and_eq_true] at h
    simp only [List.length_cons, drawsFit_length l d h.2]

/-- The positions at which a sent tree is opened (`openedTr`, Sim/CoreText.lean) read the challenges
from the next stage on: two families that agree from round number `oNext cur o` on give the same
list. -/
theorem openedTr_congr (D D' : ℕ → Fmt.Drawn) : ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage)
    (o i : ℕ), (∀ n, oNext cur o ≤ n → D n = D' n) →
    openedTr D rest cur o i = openedTr D' rest cur o i
  | [], _, _, _, _ => rfl
  | next :: rest, cur, o, i, h => by
    unfold openedTr
    have e : qNext rest.isEmpty cur next o D = qNext rest.isEmpty cur next o D' := by
      unfold qNext
      rw [h _ (by omega), h _ (by omega)]
    rw [e, openedTr_congr D D' rest next (oNext cur o) _ fun n hn => h n (by
      unfold oNext at hn ⊢
      omega)]

/-! ## 2 The hypotheses -/

/-- The hypotheses on public numbers and on the two jobs' public fields. K: the table of codes. -/
structure PubTies (J : TestJob W X) (Js : SimJob Pb) (K : Codes) : Prop where
  place : Js.p = J.p
  own : Js.own = J.fresh.isNone
  reach : reachB J.p = true
  plan : planB J.p K 1 = true
  form : formPubB J.p = true
  count : (laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages
  rounds : restLen J.p.nums.stages = 2 + lenFrom (stN J.p) (J.p.nums.stages.drop 2)
  tables : tablesFitB J = true

/-- The hypotheses at the second part's entry. pb: the input's public part. mem: the stretches that
the part carries, by number. chain, firstTree: as the frame's `Before.holds` takes them. -/
structure OnPlan (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain firstTree : ℕ) (pb : Pb)
    (mem : ℕ → Stretch) (m : Mid W X) (front : Before) : Prop where
  /-- the run has heard at least as many challenges as the first part has rounds; `leS`: it has
  shown at least as many rounds -/
  le : firstLen J.p.nums.stages ≤ m.st.heard.length
  leS : firstLen J.p.nums.stages ≤ m.seen.length
  /-- the first part's challenges, as heard, have the declared form -/
  heardFit : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
    (m.st.lately (firstLen J.p.nums.stages)) = true
  /-- and are those that are shown in front -/
  heard : (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
    m.st.lately (firstLen J.p.nums.stages)
  /-- the two jobs' letters for the verifier's state at the test's door agree. The letters are the
  fields `rec₀` of J and of Js. No statement that this state is the verifier's. -/
  door : J.rec₀ m.st.input (restFront J m) = Js.rec₀ pb (front.cut (firstLen J.p.nums.stages))
  /-- the first fold's rounds, as shown in front, are those that the text makes -/
  fold : (lastSeen front (firstLen J.p.nums.stages)).tail =
    aFold (coinsOf J.p.nums.stages (carriedCoins J mem).hide fun _ => 0) 0 J.s₀ 1 (rowsAt J mem m)
      (rowOf (J.recB m.st.input (restFront J m) (heardIn J m 0))) (heardIn J m)
  /-- the state's shape and the prover's data, at the first part's challenges -/
  asks : ∃ Dp cc R, Dp.ts.length = 1 ∧
    ShapeAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc R
  /-- one tree in front, of the first stage's depth, on both sides; at every list of the part's
  challenges at which the front holds what the part's rounds read, the listed column is the tree's
  at the positions that the first reading round opens -/
  cols : ∃ colR colF, J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m) =
      [((sgOf J.s₀).C.a, colR)] ∧ Js.trees₀ front = [((sgOf J.s₀).C.a, colF)] ∧
    ∀ ds, front.holds chain firstTree ((J.laid.drop (firstLen J.p.nums.stages)).map (·.1)) ds =
        true →
      ∀ x ∈ Fmt.listOf (openedAt (drawnAll J m ds) (J.p.nums.stages.drop 1) J.s₀ 1),
        colR x = colF x

/-- `OnPlan` in the type of the frame's `On`: at a member whose number is not 1 it asks nothing. -/
def onPlan (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain firstTree : ℕ)
    (u : Member V W X Pb) (ca : CsAll u.part.carries) (m : Mid W X) (front : Before) : Prop :=
  u.number = 1 → OnPlan J Js K chain firstTree (φ.pub m.st.input) (stretches _ ca) m front

/-- The second part's challenges by the round's number in the test; `noDraw` beyond the list. At a
number i below `firstLen stages` the subtraction is cut off at 0, and the value is the one at
`firstLen stages`: the list's first challenge, not `noDraw`, where the list is not empty. -/
def laterOf (stages : List Fmt.M1.Stage) (ds : List Fmt.Drawn) (i : ℕ) : Fmt.Drawn :=
  ds.getD (i - firstLen stages) noDraw

/-- bud: at the second part: the positions asked of a tree are among those that the next reading
round samples. At every other number n it asks nothing. -/
def budOpened (stages : List Fmt.M1.Stage) (n : ℕ) (ds : List Fmt.Drawn)
    (asks : List (List (List ℕ))) : Prop :=
  n = 1 → ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
    q ∈ openedTr (laterOf stages ds) (stages.drop 1) (stages.headD default) 1
      (1 + ((sgOf (stages.headD default)).h + (sgOf (stages.headD default)).g) + i)

/-! ## 3 The clause `same`, from `door` and `fold` -/

/-- The verifier's state behind the first fold as the part's text makes it is the simulators'. In
Lean: `partEntry J mem m = Js.entry pb front`, from `Js.p = J.p` and the clauses `heard`, `door` and
`fold` of `OnPlan`. No statement that this state is the verifier's. -/
theorem same_of_ties {J : TestJob W X} {Js : SimJob Pb} {pb : Pb} {mem : ℕ → Stretch} {m : Mid W X}
    {front : Before} (hp : Js.p = J.p)
    (heard : (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
      m.st.lately (firstLen J.p.nums.stages))
    (hrec : J.rec₀ m.st.input (restFront J m) = Js.rec₀ pb (front.cut (firstLen J.p.nums.stages)))
    (hfold : (lastSeen front (firstLen J.p.nums.stages)).tail =
      aFold (coinsOf J.p.nums.stages (carriedCoins J mem).hide fun _ => 0) 0 J.s₀ 1
        (rowsAt J mem m) (rowOf (J.recB m.st.input (restFront J m) (heardIn J m 0)))
        (heardIn J m)) :
    partEntry J mem m = Js.entry pb front := by
  have hs : Js.stages = J.p.nums.stages := by unfold SimJob.stages; rw [hp]
  have h0 : ((lastSeen front (firstLen J.p.nums.stages)).map (·.drawn)).headD noDraw =
      heardIn J m 0 := by
    rw [heard]
    unfold heardIn
    cases m.st.lately (firstLen J.p.nums.stages) <;> rfl
  have hB : Js.recB pb (front.cut (firstLen J.p.nums.stages)) (heardIn J m 0) =
      J.recB m.st.input (restFront J m) (heardIn J m 0) := by
    unfold SimJob.recB TestJob.recB SimJob.laid TestJob.laid
    rw [hrec, hp]
  unfold partEntry SimJob.entry
  simp only [hs, h0, hB, hfold]
  unfold SimJob.s₀ TestJob.s₀ SimJob.laid TestJob.laid
  rw [hp]

/-! ## 4 The statement -/

/-- **The frame's sentence at the second member.** It is stated at a state on entry that is made of
the plan's public part, not shown to be the verifier's. Under `PubTies`, at `On` := `onPlan` and
`bud` := `budOpened`. -/
theorem exact_plan (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (K : Codes) (chain firstTree : ℕ) (T : PubTies J Js K) :
    ExactMember φ σ chain firstTree (onPlan φ J Js K chain firstTree)
      (budOpened J.p.nums.stages) (restMember J Js) := by
  refine exact_rest φ σ J Js chain firstTree _ _ fun ca m front ds asks hOn _ hfit hbud hholds => ?_
  have O : OnPlan J Js K chain firstTree (φ.pub m.st.input) (stretches _ ca) m front := hOn rfl
  obtain ⟨a, next, nx', rest', hst, -, hlow, -, hsz⟩ := reach_gives J.p T.reach
  obtain ⟨Dp, cc, R, hT, Sh, Dt⟩ := O.asks
  obtain ⟨colR, colF, htr, hls, hcols⟩ := O.cols
  have hA : stA J.p = a := by unfold stA; rw [hst]; rfl
  have hN : stN J.p = next := by unfold stN; rw [hst]; rfl
  have hs0 : J.s₀ = a := by unfold TestJob.s₀; rw [hst]; rfl
  have FP := formPub_of_B J.p a next (nx' :: rest') hst T.form
  have hk : a.k = (sgOf a).h + (sgOf a).g := by
    have := FP.hk
    show a.k = a.h + (a.k - a.h)
    omega
  have hn : firstLen J.p.nums.stages = 2 + a.k := by rw [hst]; rfl
  have hlat : (m.st.lately (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    have := O.le
    simp only [State.lately, List.length_drop]
    omega
  -- all the test's challenges as one list, and by number
  have hall : drawsFit ((laidOf J.p).map (·.1)) (m.st.lately (firstLen J.p.nums.stages) ++ ds) =
      true := by
    have e : (laidOf J.p).map (·.1) = ((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1) ++
        ((laidOf J.p).drop (firstLen J.p.nums.stages)).map (·.1) := by
      rw [← List.map_append, List.take_append_drop]
    rw [e]
    exact drawsFit_append _ _ _ _ O.heardFit hfit
  have hby : byNo (m.st.lately (firstLen J.p.nums.stages) ++ ds) = drawnAll J m ds := by
    funext i
    unfold byNo drawnAll heardIn
    by_cases c : i < firstLen J.p.nums.stages
    · rw [if_pos c, List.getD_append _ _ _ _ (by rw [hlat]; exact c)]
      rfl
    · rw [if_neg c, List.getD_append_right _ _ _ _ (by rw [hlat]; omega), hlat]
      rfl
  have hfront : ∀ n, n < 1 + (1 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g)) →
      heardIn J m n = drawnAll J m ds n := fun n hn' => by
    unfold drawnAll
    rw [if_pos (by rw [hn, hk]; rw [hA] at hn'; omega)]
  have F : FormAsks J m.st.input (restFront J m) (carriedCoins J (stretches _ ca))
      (drawnAll J m ds) := by
    rw [← hby]
    exact formAsks_of_draws J _ _ _ _ a next (nx' :: rest') hst FP hall
  have hcnt : ∀ i, (drawnAll J m ds i).poss.length = declared J.p i := fun i => by
    have h := counts_of_drawsFit _ _ hall i
    rw [List.getElem?_map, Option.map_map] at h
    rw [← hby]
    exact h
  have hlen : ds.length = restLen J.p.nums.stages := by
    have h := drawsFit_length _ _ hfit
    rw [h, List.length_map]
    show ((laidOf J.p).drop _).length = _
    rw [List.length_drop, T.count]
    omega
  rw [hs0] at htr hls hcols
  refine ⟨a, next, nx', rest', colR, colF,
    { place := T.place, own := T.own
      play := ⟨hst, hk, rfl, T.count, FP.sorts, T.tables,
        ⟨O.le, O.leS, fun n hn' => by
          unfold drawnAll
          rw [if_pos hn']
          rfl⟩, hlen, fun n hn' => by
          unfold drawnAll
          rw [if_neg (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hn']⟩
      count := by
        have h := T.rounds
        have e : J.p.nums.stages.drop 2 = nx' :: rest' := by rw [hst]; rfl
        rw [hN, e] at h
        exact h
      behind := fun c => behind_of_plan J m.st.input (restFront J m)
        (carriedCoins J (stretches _ ca)) (drawnAll J m ds) K Dp cc R (by rw [hT]; exact T.plan)
        (shapeAsks_congr J _ _ _ _ _ hfront Sh) F (dataAsks_congr J _ _ _ _ _ hfront Dt) a next nx'
        rest' hst colR htr c
      tree := htr, listed := hls
      cols := by
        have := hcols ds hholds
        rw [hst] at this
        exact this
      fits := hsz _ hcnt, low := hlow
      asks := fun i q hq => by
        have := hbud rfl i q hq
        rw [hst] at this
        rw [openedTr_congr (drawnAll J m ds) (laterOf (a :: next :: nx' :: rest') ds) _ _ _ _
          fun n hn' => by
            unfold oNext at hn'
            unfold drawnAll laterOf
            rw [if_neg (by rw [hn, hk]; omega), hst]]
        exact this
      heard := O.heard
      same := same_of_ties T.place O.heard O.door O.fold }⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.drawsFit_append
#print axioms ProofFile.Honest.K12.drawsFit_length
#print axioms ProofFile.Honest.K12.openedTr_congr
#print axioms ProofFile.Honest.K12.same_of_ties
#print axioms ProofFile.Honest.K12.exact_plan
#print axioms ProofFile.Honest.K12.PubTies
#print axioms ProofFile.Honest.K12.OnPlan
#print axioms ProofFile.Honest.K12.onPlan
#print axioms ProofFile.Honest.K12.laterOf
#print axioms ProofFile.Honest.K12.budOpened
