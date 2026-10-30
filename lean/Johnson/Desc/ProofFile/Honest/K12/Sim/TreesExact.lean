-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesExact.lean: the frame's own sentence `exact` at a
proximity test's second member (`ExactMember`, Johnson/Desc/ProofFile/Honest/Small/Field.lean;
`restMember`, Sim/Row.lean; `restSim`, Sim/Sims.lean) where the first round of positions opens a
list of trees, each of its own depth. As Sim/Exact.lean, Sim/ExactPlan.lean and Sim/ExactFree.lean,
which ask one tree of the first stage's depth. Conditional on public ties and on a written
condition. No property is claimed: whether a chain's run meets the condition at any place is not
shown.

  `AskedT`, `entry_eq_trees`, `tells_rest_trees`, `exact_rest_trees`   at every condition and bound
                 that give what is listed in `AskedT`
  `PubTiesT`, `OnPlanT`, `onPlanT`, `exact_plan_trees`   at a written condition that reads the
                 part's own challenges in one clause
  `groups_of_trees`   two lists of trees of the same depths, with the same columns at the sampled
                 positions in each tree's own range, give an opening the same groups
  `OpenTies`, `OnFreeT`, `onFreeT`, `onPlan_of_free_trees`, `exact_free_trees`   at a written
                 condition no clause of which speaks of the part's own challenges

What turns against the elder three. `OpenTie`'s clause on the depth goes: each tree is read in its
own range. `PubTies.reach` is `reachTB` (Sim/TreesReach.lean); `PubTies.plan` is `planB` at the
number of trees. `asks` is at that number. `tree` becomes `trees`: in that clause the columns `cols`
are bound by an equation to the front's own reader (`Before.treeCols ... = some cols`): no bare
"there is". `Asked`'s clauses on the one tree become `AskedT.groups`, and `OnPlan.cols` becomes
`OnPlanT.groups`. No theorem ties this file to the three files named above.

By what. `core_inv_trees` (Sim/TreesLaw.lean), `behind_of_plan_trees` (Sim/TreesPlan.lean),
`reach_gives_trees` (Sim/TreesReach.lean); `shows_rest`, `same_of_ties`, `cols_of_holds` and the
other lemmas of the elder files are general in the trees and are called.

Limits.
- The case where the first fold's fresh table came earlier alone. Where the first fold sends its own
  fresh table `exact_rest_trees`, `exact_plan_trees` and `exact_free_trees` hold emptily: the
  invariant of the later stages is `BodyInv` at `PlanAll` (Johnson/Prover/Link/BodyInv.lean,
  BodyCloseB.lean), whose `PlanFrom` (FormStepPlan.lean) asks `ownMask = false` at every stage, so
  no state meets it at such a place. `exact_rest_trees` names neither case, yet its `AskedT.behind`
  is that invariant; `PubTiesT` cannot be met there either (`reachTB`, `planB`).
- That invariant can be met only where the claim's form has no written-out factor: in front of a
  stage that is not the last `BodyInv` asks `FormInv`, whose field `plain`
  (Johnson/Prover/Link/FormInv.lean) says so; by the library's own heads the key file's and the
  proof file's tests take in rows with such factors (FormRow.lean, BodyInv.lean, Limits).
  `ShapeAsks.plainRows` (PlanB.lean) asks the like at the door.
- At a state on entry that is made of the plan's public part, not shown to be the verifier's: here
  it is the job's field `rec₀`, which the clause door sets equal to the simulators' job's at the
  input's public part and the front. The clause compares whole states.
- Shown at no job that is played. It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of halves
  with a guard in front. The parts and their random values are defined in Test.lean, Parts.lean and
  Coins.lean of Johnson/Desc/ProofFile/Honest/K12/; what they send is that folder's own `testAll`;
  how far it is tied to the library's `bodyAll` (Johnson/Prover/Link/BodyAll.lean) is said in the
  limits of Test.lean.
- The second member alone: nothing on the first, on the fresh table's owner, on a lent run of random
  values. The carried values are fixed in the equation.
- The clauses door, fold, asks and trees of the condition read the input, the rows, carried values
  and other parts' random values, and they are not shown of a run: a sentence under such a
  condition says nothing of a run until these are theorems, and no later law may take the condition
  as a hypothesis on a run and then speak of the random values as sampled uniformly.
- "No clause speaks of the part's own challenges" is true by type. In a run the front itself moves
  with these challenges: it lists the columns at all positions that are read in the whole run. So
  the clauses on the front are to be shown at every list of them all the same; what is won is the
  condition's type.
- The side σ is free, and `restMember J Js` is the member as written out: that a seated side has it
  is not shown here. An honest verifier; fixed challenges; one part. At the level of oracle
  messages: no root, salt or hash.
- The bound on the positions, `budOpened` (Sim/ExactPlan.lean), is a premise; a narrower bound says
  less, and by reading it is narrower than `budRest` (Sim/Row.lean): no theorem.
- Three stages or more. The first opening's columns are not among what the second member shows: they
  stand in the condition. No member of `OnFreeT` is given. Nothing on completeness, soundness or
  hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesPlan
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesReach
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (FitsBody qNext oNext)
open ProofFile.Honest.Small (ExactMember)

attribute [local instance] csNonempty

variable {S Cl V W X Pb : Type}

/-! ## 1 The frame's sentence, at every On and bud that give what is asked -/

/-- **What is asked**: `Asked` (Sim/Exact.lean) with its three clauses on one tree (tree, listed,
cols) turned into one on the first opening's groups, at the two jobs' own lists of trees. -/
structure AskedT (J : TestJob W X) (Js : SimJob Pb) (pb : Pb) (mem : ℕ → Stretch) (m : Mid W X)
    (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (s next nx' : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage) : Prop where
  place : Js.p = J.p
  own : Js.own = J.fresh.isNone
  play : PlayTies J s next (nx' :: rest') m (drawnAll J m ds) ds
  count : restLen J.p.nums.stages = 2 + lenFrom next (nx' :: rest')
  behind : ∀ c : ℕ → GE, BehindFirstT J.p s next (nx' :: rest') (laidS J.p)
    (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J mem m)
    (carriedCoins J mem).hide (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m))
    (drawnAll J m ds) c
  groups : aGroups s 1 (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m))
      (drawnAll J m ds) = aGroups s 1 (Js.trees₀ front) (drawnAll J m ds)
  fits : FitsBody (drawnAll J m ds) (next :: nx' :: rest') s 1
  low : ∀ st ∈ next :: nx' :: rest', st.h ≤ st.k
  asks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
    q ∈ openedTr (drawnAll J m ds) (next :: nx' :: rest') s 1 (1 + ((sgOf s).h + (sgOf s).g) + i)
  heard : (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
    m.st.lately (firstLen J.p.nums.stages)
  same : partEntry J mem m = Js.entry pb front

section At
variable {J : TestJob W X} {Js : SimJob Pb} {pb : Pb} {mem : ℕ → Stretch} {m : Mid W X}
  {front : Before} {ds : List Fmt.Drawn} {asks : List (List (List ℕ))}
  {s next nx' : Fmt.M1.Stage} {rest' : List Fmt.M1.Stage}

/-- The state behind the first fold, in the law's letters. -/
theorem entry_eq_trees (A : AskedT J Js pb mem m front ds asks s next nx' rest') :
    partEntry J mem m =
      entryOf J.p s (laidS J.p) (J.recB m.st.input (restFront J m) (drawnAll J m ds 0))
        (rowsAt J mem m) (hideW (carriedCoins J mem).hide) (drawnAll J m ds) := by
  have hs : J.s₀ = s := by
    unfold TestJob.s₀
    rw [A.play.stages]
    rfl
  have hn : firstLen J.p.nums.stages = 2 + s.k := by rw [A.play.stages]; rfl
  have h0 : drawnAll J m ds 0 = heardIn J m 0 := by
    unfold drawnAll
    rw [if_pos (by omega)]
  unfold partEntry entryOf
  simp only
  rw [hs, h0, A.play.laid]
  refine congrArg _ ?_
  exact aFold_congr _ _ _ _ _ _ _ _ fun n hn' => by
    unfold drawnAll
    rw [if_pos (by rw [hn, A.play.k]; omega)]

/-- **What the simulator yields.** -/
theorem tells_rest_trees (A : AskedT J Js pb mem m front ds asks s next nx' rest')
    (c : Cs (restSim Js).takes) :
    (restSim Js).tell pb front ds asks c =
      some (zeroOwnT J.p s next (nx' :: rest') (laidS J.p)
        (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J mem m)
        (carriedCoins J mem).hide (Js.trees₀ front) (drawnAll J m ds)
        (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks
        (stretchOf c).e) := by
  have hst : Js.stages = s :: next :: nx' :: rest' := by
    unfold SimJob.stages
    rw [A.place, A.play.stages]
  have hl : Js.laid = laidOf J.p := by
    rw [← A.play.laid]
    unfold SimJob.laid TestJob.laid
    rw [A.place]
  have hD : (fun i => if i < firstLen Js.stages then
      ((lastSeen front (firstLen Js.stages)).map (·.drawn)).getD i noDraw
      else ds.getD (i - firstLen Js.stages) noDraw) = drawnAll J m ds := by
    have e : Js.stages = J.p.nums.stages := by rw [hst, A.play.stages]
    funext i
    rw [e, A.heard]
    rfl
  have hdep : ∀ i, Js.depthAt i = depthAt J i := fun i => by
    unfold SimJob.depthAt depthAt
    rw [A.own, A.place]
  unfold restSim
  simp only [hD]
  unfold restZeroText
  simp only [hst, Option.map_some]
  have hlen : ∀ x : ℕ → GE, (zeroText Js.p s next (nx' :: rest') (Js.laid.drop 1)
      (Js.entry pb front) (Js.trees₀ front) x (drawnAll J m ds)).rs.length =
      restLen J.p.nums.stages := fun x => by
    rw [A.count]
    simp only [zeroText, zeroTextK, restText, List.length_set, List.length_append, length_stages,
      aSwitch, List.length_cons, List.length_nil]
  rw [hlen]
  unfold zeroOwnT
  rw [← entry_eq_trees A, A.same, A.place, hl]
  have e2 : firstLen (s :: next :: nx' :: rest') = firstLen J.p.nums.stages := by
    rw [A.play.stages]
  simp only [hdep, e2]
  rfl

end At

/-- **The frame's sentence at the second member**, at every On and bud that give what is asked. -/
theorem exact_rest_trees (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop)
    (hA : ∀ (ca : CsAll (restMember J Js : Member V W X Pb).part.carries) m front ds asks,
      On (restMember J Js) ca m front → m.seen = front.seen →
      drawsFit ((restMember J Js : Member V W X Pb).rounds.map (·.1)) ds = true →
      bud 1 ds asks →
      front.holds chain firstTree ((restMember J Js : Member V W X Pb).rounds.map (·.1)) ds = true →
      ∃ s next nx' rest', AskedT J Js (φ.pub m.st.input) (stretches _ ca) m front ds asks
        s next nx' rest') :
    ExactMember φ σ chain firstTree On bud (restMember J Js) := by
  intro ca m front ds asks hOn hseen hfit hbud hholds _
  obtain ⟨s, next, nx', rest', A⟩ := hA ca m front ds asks hOn hseen hfit hbud hholds
  have hlaw := core_inv_trees J.p s next nx' rest' (laidS J.p)
    (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
    (carriedCoins J (stretches _ ca)).hide
    (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (rowsAt J (stretches _ ca) m))
    (Js.trees₀ front) (drawnAll J m ds)
    (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks A.fits A.low
    A.groups (fun c => A.behind (stretchOf c).e) A.asks
  have hd : (⟨0, dueRest J.p.nums.stages⟩ : Due) = ⟨0, dueFrom s (next :: nx' :: rest')⟩ := by
    rw [A.play.stages]
    rfl
  have hd' : (restSim Js).takes = ⟨0, dueFrom s (next :: nx' :: rest')⟩ := by
    show (⟨0, dueRest Js.stages⟩ : Due) = _
    unfold SimJob.stages
    rw [A.place, A.play.stages]
    rfl
  -- the left side
  have hL : (fun c : Cs (restMember J Js : Member V W X Pb).part.takes ×
      CsAll (restMember J Js : Member V W X Pb).part.spends =>
      σ.shows φ (restMember J Js) (c.1, c.2, ca) m ds asks) =
      (fun c : Cs ⟨0, dueRest J.p.nums.stages⟩ => some (realOwnT J.p s next (nx' :: rest')
        (laidS J.p) (J.recB m.st.input (restFront J m) (drawnAll J m ds 0))
        (rowsAt J (stretches _ ca) m) (carriedCoins J (stretches _ ca)).hide
        (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (rowsAt J (stretches _ ca) m))
        (drawnAll J m ds)
        (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks
        (stretchOf c).e)) ∘ Prod.fst := by
    funext c
    rw [shows_rest φ σ J Js s next (nx' :: rest') m (drawnAll J m ds) ds A.play (c.1, c.2, ca)
      asks]
    show some (shownFrom (restOf J m.st.input (restFront J m) (restCoins J (c.1, c.2, ca))
      (drawnAll J m ds) s next (nx' :: rest')) _ _ asks) =
      some (realOwnT _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    unfold restOf realOwnT
    rw [A.play.laid]
    rfl
  have hR : (fun c : Cs (restMember J Js : Member V W X Pb).sim.takes =>
      (restMember J Js : Member V W X Pb).tells φ c m.st.input front ds asks) =
      fun c : Cs (restSim Js).takes => some (zeroOwnT J.p s next (nx' :: rest') (laidS J.p)
        (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
        (carriedCoins J (stretches _ ca)).hide (Js.trees₀ front) (drawnAll J m ds)
        (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks
        (stretchOf c).e) := funext fun c => tells_rest_trees A c
  rw [hL, hR]
  refine (PMF.map_comp Prod.fst _ _).symm.trans ?_
  haveI : Nonempty (CsAll (restMember J Js : Member V W X Pb).part.spends) := ⟨default⟩
  haveI : Nonempty (Cs (restMember J Js : Member V W X Pb).part.takes ×
      CsAll (restMember J Js : Member V W X Pb).part.spends) := ⟨(default, default)⟩
  have hfst : (Prob.unif (Cs (restMember J Js : Member V W X Pb).part.takes ×
      CsAll (restMember J Js : Member V W X Pb).part.spends)).map Prod.fst =
      Prob.unif (Cs ⟨0, dueRest J.p.nums.stages⟩) := Prob.map_fst_unif
  refine (congrArg (PMF.map _) hfst).trans ?_
  have h2 := congrArg (PMF.map some) hlaw
  rw [PMF.map_comp, PMF.map_comp] at h2
  exact (map_stretch hd fun x => some (realOwnT J.p s next (nx' :: rest') (laidS J.p)
      (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
      (carriedCoins J (stretches _ ca)).hide
      (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (rowsAt J (stretches _ ca) m))
      (drawnAll J m ds)
      (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks x)).trans
    (h2.trans (map_stretch hd' fun x => some (zeroOwnT J.p s next (nx' :: rest') (laidS J.p)
      (J.recB m.st.input (restFront J m) (drawnAll J m ds 0)) (rowsAt J (stretches _ ca) m)
      (carriedCoins J (stretches _ ca)).hide (Js.trees₀ front) (drawnAll J m ds)
      (fun i => depthAt J (firstLen J.p.nums.stages + i)) (restLen J.p.nums.stages) asks
      x)).symm)

/-! ## 2 At a written On that reads the part's own challenges in one clause -/

/-- **Public ties**: `PubTies` (Sim/ExactPlan.lean) with `reachTB` for `reachB`, and the plan's half
at nT trees. -/
structure PubTiesT (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (nT : ℕ) : Prop where
  place : Js.p = J.p
  own : Js.own = J.fresh.isNone
  reach : reachTB J.p = true
  plan : planB J.p K nT = true
  form : formPubB J.p = true
  count : (laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages
  rounds : restLen J.p.nums.stages = 2 + lenFrom (stN J.p) (J.p.nums.stages.drop 2)
  tables : tablesFitB J = true

/-- `OnPlan` (Sim/ExactPlan.lean) at nT first trees. -/
structure OnPlanT (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (nT chain firstTree : ℕ) (pb : Pb)
    (mem : ℕ → Stretch) (m : Mid W X) (front : Before) : Prop where
  le : firstLen J.p.nums.stages ≤ m.st.heard.length
  leS : firstLen J.p.nums.stages ≤ m.seen.length
  heardFit : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
    (m.st.lately (firstLen J.p.nums.stages)) = true
  heard : (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
    m.st.lately (firstLen J.p.nums.stages)
  door : J.rec₀ m.st.input (restFront J m) = Js.rec₀ pb (front.cut (firstLen J.p.nums.stages))
  fold : (lastSeen front (firstLen J.p.nums.stages)).tail =
    aFold (coinsOf J.p.nums.stages (carriedCoins J mem).hide fun _ => 0) 0 J.s₀ 1 (rowsAt J mem m)
      (rowOf (J.recB m.st.input (restFront J m) (heardIn J m 0))) (heardIn J m)
  asks : ∃ Dp cc R, Dp.ts.length = nT ∧
    ShapeAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc R
  /-- at every list of the part's challenges at which the front holds what the part's rounds read,
  the two jobs' trees give the first opening the same groups -/
  groups : ∀ ds, front.holds chain firstTree ((J.laid.drop (firstLen J.p.nums.stages)).map (·.1))
        ds = true →
    aGroups J.s₀ 1 (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m)) (drawnAll J m ds) =
      aGroups J.s₀ 1 (Js.trees₀ front) (drawnAll J m ds)

/-- The same as the frame's `On`: nothing at the first part. -/
def onPlanT (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : Codes)
    (nT chain firstTree : ℕ) (u : Member V W X Pb) (ca : CsAll u.part.carries) (m : Mid W X)
    (front : Before) : Prop :=
  u.number = 1 → OnPlanT J Js K nT chain firstTree (φ.pub m.st.input) (stretches _ ca) m front

theorem exact_plan_trees (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : Codes) (nT chain firstTree : ℕ) (T : PubTiesT J Js K nT) :
    ExactMember φ σ chain firstTree (onPlanT φ J Js K nT chain firstTree)
      (budOpened J.p.nums.stages) (restMember J Js) := by
  refine exact_rest_trees φ σ J Js chain firstTree _ _
    fun ca m front ds asks hOn _ hfit hbud hholds => ?_
  have O : OnPlanT J Js K nT chain firstTree (φ.pub m.st.input) (stretches _ ca) m front := hOn rfl
  obtain ⟨a, next, nx', rest', hst, -, hlow, hsz⟩ := reach_gives_trees J.p T.reach
  obtain ⟨Dp, cc, R, hT, Sh, Dt⟩ := O.asks
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
  have hgr := O.groups ds hholds
  rw [hs0] at hgr
  refine ⟨a, next, nx', rest',
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
      behind := fun c => behind_of_plan_trees J m.st.input (restFront J m)
        (carriedCoins J (stretches _ ca)) (drawnAll J m ds) K Dp cc R (by rw [hT]; exact T.plan)
        (shapeAsks_congr J _ _ _ _ _ hfront Sh) F (dataAsks_congr J _ _ _ _ _ hfront Dt) a next nx'
        rest' hst c
      groups := hgr
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

/-! ## 3 At a written On no clause of which speaks of the part's own challenges -/

/-- Two lists of trees give an opening the same groups, where they have the same depths and, tree
by tree, the same columns at the sampled positions in that tree's own range. -/
theorem groups_of_trees (poss : List ℕ) (A B : List Tree) (hd : A.map (·.1) = B.map (·.1))
    (hc : ∀ (i : ℕ) (T U : Tree), A[i]? = some T → B[i]? = some U →
      ∀ x ∈ Fmt.listOf (poss.map (· % 2 ^ T.1)), T.2 x = U.2 x) :
    groupsAt A poss = groupsAt B poss := by
  unfold groupsAt
  refine List.ext_getElem? fun i => ?_
  have hi : (A[i]?).map (·.1) = (B[i]?).map (·.1) := by
    rw [← List.getElem?_map, ← List.getElem?_map, hd]
  rw [List.getElem?_map, List.getElem?_map]
  cases hT : A[i]? with
  | none =>
    cases hU : B[i]? with
    | none => rfl
    | some U =>
      rw [hT, hU] at hi
      cases hi
  | some T =>
    cases hU : B[i]? with
    | none =>
      rw [hT, hU] at hi
      cases hi
    | some U =>
      rw [hT, hU] at hi
      have e : T.1 = U.1 := Option.some.inj hi
      show some (groupAt T.1 poss T.2) = some (groupAt U.1 poss U.2)
      refine congrArg some ?_
      unfold groupAt
      rw [← e]
      exact List.map_congr_left fun x hx => by rw [hc i T U hT hU x hx]

/-- **Public**: the part's round number 1 is declared to open the trees os, in this order; the
simulators' job names these trees, each at its declared depth. -/
structure OpenTies (J : TestJob W X) (Js : SimJob Pb) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) : Prop where
  decl : ∃ d, (J.laid.drop (firstLen J.p.nums.stages))[1]? = some d ∧ d.1.opens = os
  opens : Js.opens = os.map fun o => ((srcOf chain o.2).1, (srcOf chain o.2).2, o.1.a)

/-- `OnFree` (Sim/ExactFree.lean) at a list of first trees, each of its own depth. -/
structure OnFreeT (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (pb : Pb) (mem : ℕ → Stretch) (m : Mid W X)
    (front : Before) : Prop where
  le : firstLen J.p.nums.stages ≤ m.st.heard.length
  leS : firstLen J.p.nums.stages ≤ m.seen.length
  heardFit : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
    (m.st.lately (firstLen J.p.nums.stages)) = true
  heard : (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
    m.st.lately (firstLen J.p.nums.stages)
  door : J.rec₀ m.st.input (restFront J m) = Js.rec₀ pb (front.cut (firstLen J.p.nums.stages))
  fold : (lastSeen front (firstLen J.p.nums.stages)).tail =
    aFold (coinsOf J.p.nums.stages (carriedCoins J mem).hide fun _ => 0) 0 J.s₀ 1 (rowsAt J mem m)
      (rowOf (J.recB m.st.input (restFront J m) (heardIn J m 0))) (heardIn J m)
  asks : ∃ Dp cc R, Dp.ts.length = os.length ∧
    ShapeAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc R
  /-- the job's trees have the declared depths, in the declared order; the front lists each; what
  the front lists of a tree is that tree's -/
  trees : (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m)).map (·.1) =
      os.map (·.1.a) ∧
    ∀ (i : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (T : Tree), os[i]? = some o →
      (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m))[i]? = some T →
      ∃ cols, front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2 = some cols ∧
        ∀ q ∈ cols, q.2 = T.2 q.1

/-- The same as the frame's `On`: nothing at the first part. -/
def onFreeT (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (u : Member V W X Pb) (ca : CsAll u.part.carries)
    (m : Mid W X) (front : Before) : Prop :=
  u.number = 1 → OnFreeT J Js K chain os (φ.pub m.st.input) (stretches _ ca) m front

/-- It gives the condition of section 2. -/
theorem onPlan_of_free_trees {J : TestJob W X} {Js : SimJob Pb} {K : Codes} {chain : ℕ}
    {os : List (Fmt.Shape × Fmt.TreeSource)} {pb : Pb} {mem : ℕ → Stretch} {m : Mid W X}
    {front : Before} (firstTree : ℕ) (T : OpenTies J Js chain os) (a next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = a :: next :: rest)
    (hk : a.k = (sgOf a).h + (sgOf a).g) (O : OnFreeT J Js K chain os pb mem m front) :
    OnPlanT J Js K os.length chain firstTree pb mem m front := by
  obtain ⟨d, hd, hop⟩ := T.decl
  have hs0 : J.s₀ = a := by unfold TestJob.s₀; rw [hst]; rfl
  have hn : firstLen J.p.nums.stages = 2 + a.k := by rw [hst]; rfl
  refine ⟨O.le, O.leS, O.heardFit, O.heard, O.door, O.fold, O.asks, fun ds hh => ?_⟩
  have e : (drawnAll J m ds (1 + 2 + ((sgOf J.s₀).h + (sgOf J.s₀).g))).poss =
      (ds.getD 1 noDraw).poss := by
    unfold drawnAll
    rw [hs0, if_neg (by rw [hn]; omega), hn]
    congr 2
    omega
  unfold aGroups
  rw [e]
  have hF : Js.trees₀ front = os.map fun o => (o.1.a, fun q =>
      (((front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2).getD []).lookup q).getD []) := by
    unfold SimJob.trees₀
    rw [T.opens, List.map_map]
    rfl
  rw [hF]
  refine groups_of_trees _ _ _ ?_ fun i Tr U hT hU x hx => ?_
  · rw [O.trees.1, List.map_map]
    rfl
  · rw [List.getElem?_map] at hU
    cases ho : os[i]? with
    | none =>
      rw [ho] at hU
      cases hU
    | some o =>
      rw [ho] at hU
      obtain rfl := Option.some.inj hU
      obtain ⟨cols, hl, hc⟩ := O.trees.2 i o Tr ho hT
      have hdep : Tr.1 = o.1.a := by
        have h1 := congrArg (·[i]?) O.trees.1
        simp only [List.getElem?_map, hT, ho, Option.map_some] at h1
        exact Option.some.inj h1
      rw [hdep] at hx
      show Tr.2 x = (((front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2).getD []).lookup
        x).getD []
      rw [hl]
      cases hR : ds[1]? with
      | none =>
        have : ds.getD 1 noDraw = noDraw := by rw [List.getD_eq_getElem?_getD, hR]; rfl
        rw [this] at hx
        simp [noDraw, Fmt.listOf] at hx
      | some R =>
        have : ds.getD 1 noDraw = R := by rw [List.getD_eq_getElem?_getD, hR]; rfl
        rw [this] at hx
        exact cols_of_holds front chain firstTree _ ds hh 1 d.1 R
          (by rw [List.getElem?_map, hd]; rfl) hR o (by rw [hop]; exact List.mem_of_getElem? ho)
          cols hl Tr.2 hc x hx

/-- **The frame's sentence at the second member, at a list of first trees, each of its own depth,
at a condition that reads none of the part's own challenges.** -/
theorem exact_free_trees (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : Codes) (chain firstTree : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource))
    (T : PubTiesT J Js K os.length) (To : OpenTies J Js chain os) :
    ExactMember φ σ chain firstTree (onFreeT φ J Js K chain os) (budOpened J.p.nums.stages)
      (restMember J Js) := by
  obtain ⟨a, next, nx', rest', hst, -, -, -⟩ := reach_gives_trees J.p T.reach
  have FP := formPub_of_B J.p a next (nx' :: rest') hst T.form
  have hk : a.k = (sgOf a).h + (sgOf a).g := by
    have := FP.hk
    show a.k = a.h + (a.k - a.h)
    omega
  intro ca m front ds asks hOn
  exact exact_plan_trees φ σ J Js K os.length chain firstTree T ca m front ds asks
    fun h1 => onPlan_of_free_trees firstTree To a next (nx' :: rest') hst hk (hOn h1)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.AskedT
#print axioms ProofFile.Honest.K12.entry_eq_trees
#print axioms ProofFile.Honest.K12.tells_rest_trees
#print axioms ProofFile.Honest.K12.exact_rest_trees
#print axioms ProofFile.Honest.K12.PubTiesT
#print axioms ProofFile.Honest.K12.OnPlanT
#print axioms ProofFile.Honest.K12.onPlanT
#print axioms ProofFile.Honest.K12.exact_plan_trees
#print axioms ProofFile.Honest.K12.groups_of_trees
#print axioms ProofFile.Honest.K12.OpenTies
#print axioms ProofFile.Honest.K12.OnFreeT
#print axioms ProofFile.Honest.K12.onFreeT
#print axioms ProofFile.Honest.K12.onPlan_of_free_trees
#print axioms ProofFile.Honest.K12.exact_free_trees
