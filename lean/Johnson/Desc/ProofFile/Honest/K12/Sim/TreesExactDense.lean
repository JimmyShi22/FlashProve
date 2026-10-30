-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesExactDense.lean: the "dense" twins of `OnPlanT`,
`onPlanT`, `exact_plan_trees`, `OnFreeT`, `onFreeT`, `onPlan_of_free_trees`, `exact_free_trees`
(TreesExact.lean in this folder).

What it is. The old statements and structures hold or take `ShapeAsks` (PlanB.lean in the folder
above), whose field `plainRows` asks that no open row and no sample row of the whole statement on
entry has a written-out variable (`stPlainB`, Johnson/Desc/Ground/Shape/Marks.lean). The twins hold
or take `ShapeAsksD` (PlanBDense.lean there), which asks `DenseRow` of the rows taken in at the
group under test. `PlainRow` (OnBytes/Slice/BlkPlain.lean) says that no tensor of a row has a
written-out variable. `DenseRow` (OnBytes/Slice/BlkProxDense.lean) allows such variables where every
tensor is in order and its slice lies inside its vector; it follows from `PlainRow`
(`denseRow_of_plain`). The rows meant are those that the proximity test takes in at the group under
test (`runRows`, OnBytes/Slice/BlkBegin.lean). Apart from that and from the twins' names, each
statement is the old one, letter for letter.

Why. The only place where the old chain spends its hypothesis is the field `dense` of the library's
`TestFront`, which `testFront_of` fills from `PlainRow` by `denseRow_of_plain`. So the weaker
hypothesis is enough. That a row taken in at the first chain's proximity test has written-out
variables is read off the description's text; no theorem in these files says so.

Main names. `OnPlanTD`, `onPlanTD_of`, `onPlanTD`, `exact_plan_trees_dense`, `OnFreeTD`,
`onFreeTD_of`, `onFreeTD`, `onPlan_of_free_trees_dense`, `exact_free_trees_dense`, `exactMember_on`,
`exact_free_trees_of_dense`.

By what. The proofs of the three twins that are theorems are the old proofs with the twins' names in
them. The four other theorems are new and short: `onPlanTD_of` and `onFreeTD_of` open the field
`asks` and call `shapeAsksD_of`; `exactMember_on` unfolds the sentence; `exact_free_trees_of_dense`
joins the last two with the twin.

Limits.
- These statements rest on this: in Johnson/Prover/Link/FormFirst.lean the structure
  `TestFront` has the field `dense`. With a field `plain` in its place,
  `testFront_of_dense` (Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean), on which all the twins
  rest, could not be proved.
- They do not reach the first chain's proximity test yet. The library proves the new hypothesis
  there, of the verifier's state (`taken_dense_entered`, Johnson/AtFull/Shape/TakenRowsDense.lean).
  These files do not show that the other hypotheses hold there: the other fields of `ShapeAsksD`
  (Johnson/Desc/ProofFile/Honest/K12/PlanBDense.lean), `planB`, and the hypotheses on the prover's
  data.
- `ShapeAsksD` is made from the old `ShapeAsks` (`shapeAsksD_of`), and so from the old mark
  `stPlainB`; and from `FrontAsksD`, the hypotheses on the front with the same new field, by
  `shapeAsksD_of_front` (ShapeAllDense.lean) and `shapeAsksD_of_two`, `shapeAsksD_of_form`,
  `shapeAsksD_of_draws` (ShapeOfTwoDense.lean); `FrontAsksD` is made by `frontAsksD_of_five`
  (FrontAtShapeDense.lean). These files lie in Johnson/Desc/ProofFile/Honest/K12/. Without a twin:
  `sorts_of_coreB` (SortsMember.lean) and `frontAsks_of_shape` (OneToAll.lean, not in the library
  yet).
- The state on entry is the job's own `rec₀`. It is not shown to be the verifier's.
- Only the case in which the fresh table has come earlier is served, as in the old statements.
- TreesExact.lean says among its limits that the invariant of the later stages can be met only where
  the claim's form has no written-out variable, since `FormInv` (Johnson/Prover/Link/FormInv.lean)
  has a field `plain`. That sentence does not fit FormInv.lean as it stands: there
  the field is `dense` and asks `DenseForm`.
- Nothing here is a statement on completeness, on soundness or on what a proof hides.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesExact
import Johnson.Desc.ProofFile.Honest.K12.PlanBDense
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesPlanDense
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlanCausalDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (FitsBody qNext oNext)
open ProofFile.Honest.Small (ExactMember)
attribute [local instance] csNonempty
variable {S Cl V W X Pb : Type}
/-- The twin of `OnPlanT` (TreesExact.lean): the field `asks` holds a `ShapeAsksD` in the place of a
`ShapeAsks`. All other fields are the old ones. It follows from the old structure (`onPlanTD_of`).
-/
structure OnPlanTD (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (nT chain firstTree : ℕ) (pb : Pb)
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
    ShapeAsksD J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc R
  groups : ∀ ds, front.holds chain firstTree ((J.laid.drop (firstLen J.p.nums.stages)).map (·.1))
        ds = true →
    aGroups J.s₀ 1 (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m)) (drawnAll J m ds) =
      aGroups J.s₀ 1 (Js.trees₀ front) (drawnAll J m ds)

/-- The old structure gives the new. -/
theorem onPlanTD_of {J : TestJob W X} {Js : SimJob Pb} {K : Codes} {nT chain firstTree : ℕ}
    {pb : Pb}
    {mem : ℕ → Stretch} {m : Mid W X} {front : Before}
    (h : OnPlanT J Js K nT chain firstTree pb mem m front) :
    OnPlanTD J Js K nT chain firstTree pb mem m front := by
  obtain ⟨Dp, cc, R, e, Sh, A⟩ := h.asks
  exact ⟨h.le, h.leS, h.heardFit, h.heard, h.door, h.fold,
    ⟨Dp, cc, R, e, shapeAsksD_of _ _ _ _ _ Sh, A⟩, h.groups⟩

/-- The twin of `onPlanT` (TreesExact.lean): the condition at the second member, with `OnPlanTD`. -/
def onPlanTD (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : Codes)
    (nT chain firstTree : ℕ) (u : Member V W X Pb) (ca : CsAll u.part.carries) (m : Mid W X)
    (front : Before) : Prop :=
  u.number = 1 → OnPlanTD J Js K nT chain firstTree (φ.pub m.st.input) (stretches _ ca) m front

/-- The twin of `exact_plan_trees` (TreesExact.lean), at the condition `onPlanTD`. That condition
follows from the old one, and it stands in front of the arrow: so this statement says more than the
old one. -/
theorem exact_plan_trees_dense (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : Codes) (nT chain firstTree : ℕ) (T : PubTiesT J Js K nT) :
    ExactMember φ σ chain firstTree (onPlanTD φ J Js K nT chain firstTree)
      (budOpened J.p.nums.stages) (restMember J Js) := by
  refine exact_rest_trees φ σ J Js chain firstTree _ _
    fun ca m front ds asks hOn _ hfit hbud hholds => ?_
  have O : OnPlanTD J Js K nT chain firstTree (φ.pub m.st.input) (stretches _ ca) m front := hOn rfl
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
      behind := fun c => behind_of_plan_trees_dense J m.st.input (restFront J m)
        (carriedCoins J (stretches _ ca)) (drawnAll J m ds) K Dp cc R (by rw [hT]; exact T.plan)
        (shapeAsksD_congr J _ _ _ _ _ hfront Sh) F (dataAsks_congr J _ _ _ _ _ hfront Dt) a next nx'
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

/-- The twin of `OnFreeT` (TreesExact.lean): the field `asks` holds a `ShapeAsksD` in the place of a
`ShapeAsks`. All other fields are the old ones. It follows from the old structure (`onFreeTD_of`).
-/
structure OnFreeTD (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
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
    ShapeAsksD J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc R
  trees : (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m)).map (·.1) =
      os.map (·.1.a) ∧
    ∀ (i : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (T : Tree), os[i]? = some o →
      (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m))[i]? = some T →
      ∃ cols, front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2 = some cols ∧
        ∀ q ∈ cols, q.2 = T.2 q.1

/-- The old structure gives the new. -/
theorem onFreeTD_of {J : TestJob W X} {Js : SimJob Pb} {K : Codes} {chain : ℕ}
    {os : List (Fmt.Shape × Fmt.TreeSource)} {pb : Pb} {mem : ℕ → Stretch} {m : Mid W X}
    {front : Before} (h : OnFreeT J Js K chain os pb mem m front) :
    OnFreeTD J Js K chain os pb mem m front := by
  obtain ⟨Dp, cc, R, e, Sh, A⟩ := h.asks
  exact ⟨h.le, h.leS, h.heardFit, h.heard, h.door, h.fold,
    ⟨Dp, cc, R, e, shapeAsksD_of _ _ _ _ _ Sh, A⟩, h.trees⟩

/-- The twin of `onFreeT` (TreesExact.lean): the condition at the second member, with `OnFreeTD`. -/
def onFreeTD (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (u : Member V W X Pb) (ca : CsAll u.part.carries)
    (m : Mid W X) (front : Before) : Prop :=
  u.number = 1 → OnFreeTD J Js K chain os (φ.pub m.st.input) (stretches _ ca) m front

/-- The twin of `onPlan_of_free_trees` (TreesExact.lean): `OnFreeTD` gives `OnPlanTD`. -/
theorem onPlan_of_free_trees_dense {J : TestJob W X} {Js : SimJob Pb} {K : Codes} {chain : ℕ}
    {os : List (Fmt.Shape × Fmt.TreeSource)} {pb : Pb} {mem : ℕ → Stretch} {m : Mid W X}
    {front : Before} (firstTree : ℕ) (T : OpenTies J Js chain os) (a next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = a :: next :: rest)
    (hk : a.k = (sgOf a).h + (sgOf a).g) (O : OnFreeTD J Js K chain os pb mem m front) :
    OnPlanTD J Js K os.length chain firstTree pb mem m front := by
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

/-- The twin of `exact_free_trees` (TreesExact.lean), at the condition `onFreeTD`. That condition
follows from the old one, and it stands in front of the arrow: so this statement says more than the
old one (`exact_free_trees_of_dense` draws the old one from it). -/
theorem exact_free_trees_dense (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : Codes) (chain firstTree : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource))
    (T : PubTiesT J Js K os.length) (To : OpenTies J Js chain os) :
    ExactMember φ σ chain firstTree (onFreeTD φ J Js K chain os) (budOpened J.p.nums.stages)
      (restMember J Js) := by
  obtain ⟨a, next, nx', rest', hst, -, -, -⟩ := reach_gives_trees J.p T.reach
  have FP := formPub_of_B J.p a next (nx' :: rest') hst T.form
  have hk : a.k = (sgOf a).h + (sgOf a).g := by
    have := FP.hk
    show a.k = a.h + (a.k - a.h)
    omega
  intro ca m front ds asks hOn
  exact exact_plan_trees_dense φ σ J Js K os.length chain firstTree T ca m front ds asks
    fun h1 => onPlan_of_free_trees_dense firstTree To a next (nx' :: rest') hst hk (hOn h1)

/-- The frame's sentence at one member goes over to every condition that implies the old one at that
member: the condition stands in front of the arrow. -/
theorem exactMember_on {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {chain firstTree : ℕ}
    {On On' : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop} {u : Member V W X Pb}
    (h : ∀ ca m front, On' u ca m front → On u ca m front)
    (E : ExactMember φ σ chain firstTree On bud u) : ExactMember φ σ chain firstTree On' bud u :=
  fun ca m front ds asks hOn => E ca m front ds asks (h ca m front hOn)

/-- The old statement of `exact_free_trees` (TreesExact.lean), letter for letter, drawn from the
twin. -/
theorem exact_free_trees_of_dense (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : Codes) (chain firstTree : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource))
    (T : PubTiesT J Js K os.length) (To : OpenTies J Js chain os) :
    ExactMember φ σ chain firstTree (onFreeT φ J Js K chain os) (budOpened J.p.nums.stages)
      (restMember J Js) :=
  exactMember_on (fun _ _ _ h h1 => onFreeTD_of (h h1))
    (exact_free_trees_dense φ σ J Js K chain firstTree os T To)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.OnPlanTD
#print axioms ProofFile.Honest.K12.onPlanTD_of
#print axioms ProofFile.Honest.K12.onPlanTD
#print axioms ProofFile.Honest.K12.exact_plan_trees_dense
#print axioms ProofFile.Honest.K12.OnFreeTD
#print axioms ProofFile.Honest.K12.onFreeTD_of
#print axioms ProofFile.Honest.K12.onFreeTD
#print axioms ProofFile.Honest.K12.onPlan_of_free_trees_dense
#print axioms ProofFile.Honest.K12.exact_free_trees_dense
#print axioms ProofFile.Honest.K12.exactMember_on
#print axioms ProofFile.Honest.K12.exact_free_trees_of_dense
