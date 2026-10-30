-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at a proximity test whose first fold sends its own fresh table: the condition.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/Free.lean: `exact_rest_own` (SimO/Rest.lean) at a condition that reads the stand and the front, as the library's `exact_free_trees_dense` (Sim/TreesExactDense.lean) at the other arm of the first fold, and public ties that can be met there. The last claim comes from the library's `endOk_of_plan_own` (K12/Own/EndOkOwn.lean), at the place itself: at the job's own door, whose mask is none.

  `PublicTiesOwn`    the public ties: those of `PubTiesT`, with `planOB` (K12/Own/PlanOwn.lean) for `planB` and the place's flag; `reach` is asked at the renumbered place `renumP`, beside one tie: the two have the same numbers of positions by round. At `renumP` only what is drawn of the stages behind the first may be quoted: `reach` reads these, and `hsz` is used at them alone
  `shapeAsksO_congr` `ShapeAsksO` reads the challenges of the first fold alone
  `OnFreeOwn`        `OnFreeTD` at the stand and the front, with `ShapeAsksO` for `ShapeAsksD`
  `onFreeOwn`        the condition at the second member
  `groups_own`       the first opening's groups at the two jobs' trees are one, from `OpenTies` and the clause `trees`
  `askedOwn_of_free`   what the law asks, from the condition
  `exact_free_own`   **`ExactMember` at `restMember J Js`, at `onFreeOwn` and `budOpened`**

Limits. CONDITIONAL on `onFreeOwn`. No file shows it at a run. `ShapeAsksO` asks `stPlainB` of the whole statement on entry: there is no dense twin of it; that the rows there are plain is a premise. No property of the protocol is claimed: nothing on completeness, soundness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.Rest
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesExactDense
import Johnson.Desc.ProofFile.Honest.K12.Own.EndOkOwn

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
open ProofFile.Honest.K12.Own (ShapeAsksO planOB renumP endOk_of_plan_own)
attribute [local instance] csNonempty
variable {S Cl V W X Pb : Type}

/-- **The public ties.** -/
structure PublicTiesOwn (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (nT : ℕ) : Prop where
  place : Js.p = J.p
  own : Js.own = J.fresh.isNone
  flag : J.p.nums.ownMask = true
  reach : reachTB (renumP J.p) = true
  plan : planOB J.p K nT = true
  declared : ∀ i, declared (renumP J.p) i = declared J.p i
  form : formPubB J.p = true
  count : (laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages
  rounds : restLen J.p.nums.stages = 2 + lenFrom (stN J.p) (J.p.nums.stages.drop 2)
  tables : tablesFitB J = true

/-- `ShapeAsksO` reads the challenges of the first fold alone. -/
theorem shapeAsksO_congr (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D D' : ℕ → Fmt.Drawn)
    {K : Codes} {Dp : Plain}
    (h : ∀ n, n < 1 + (1 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g)) → D n = D' n)
    (S : ShapeAsksO J w fr C D K Dp) : ShapeAsksO J w fr C D' K Dp := by
  have e0 : D 0 = D' 0 := h 0 (by omega)
  have eT := tFold_congr J w fr C D D' h
  exact ⟨S.codes, S.door, S.noMask, S.tidy, S.plainRows, S.claims, by rw [← e0]; exact S.plain,
    by rw [← eT]; exact S.codes₁, by rw [← eT]; exact S.pub⟩

/-- **The condition at the stand and the front.** -/
structure OnFreeOwn (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
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
  trees : (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m)).map (·.1) =
      os.map (·.1.a) ∧
    ∀ (i : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (T : Tree), os[i]? = some o →
      (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m))[i]? = some T →
      ∃ cols, front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2 = some cols ∧
        ∀ q ∈ cols, q.2 = T.2 q.1
  asks : ∃ Dp cc R, Dp.ts.length = os.length ∧
    ShapeAsksO J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc R

/-- The condition at the second member. -/
def onFreeOwn (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (u : Member V W X Pb) (ca : CsAll u.part.carries)
    (m : Mid W X) (front : Before) : Prop :=
  u.number = 1 → OnFreeOwn J Js K chain os (φ.pub m.st.input) (stretches _ ca) m front

/-- The first opening's groups. -/
theorem groups_own {J : TestJob W X} {Js : SimJob Pb} {K : Codes} {chain : ℕ}
    {os : List (Fmt.Shape × Fmt.TreeSource)} {pb : Pb} {mem : ℕ → Stretch} {m : Mid W X}
    {front : Before} (firstTree : ℕ) (T : OpenTies J Js chain os) (a next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = a :: next :: rest)
    (hk : a.k = (sgOf a).h + (sgOf a).g) (O : OnFreeOwn J Js K chain os pb mem m front) :
    ∀ ds, front.holds chain firstTree ((J.laid.drop (firstLen J.p.nums.stages)).map (·.1)) ds = true →
      aGroups J.s₀ 1 (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m)) (drawnAll J m ds) =
        aGroups J.s₀ 1 (Js.trees₀ front) (drawnAll J m ds) := by
  obtain ⟨d, hd, hop⟩ := T.decl
  have hs0 : J.s₀ = a := by unfold TestJob.s₀; rw [hst]; rfl
  have hn : firstLen J.p.nums.stages = 2 + a.k := by rw [hst]; rfl
  intro ds hh
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

/-- **What `exact` asks, from the condition.** -/
theorem askedOwn_of_free (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb)
    (K : Codes) (chain firstTree : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource))
    (T : PublicTiesOwn J Js K os.length) (To : OpenTies J Js chain os)
    (ca : CsAll (restMember J Js : Member V W X Pb).part.carries) (m : Mid W X) (front : Before)
    (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (hOn : onFreeOwn φ J Js K chain os (restMember J Js : Member V W X Pb) ca m front)
    (hfit : drawsFit ((restMember J Js : Member V W X Pb).rounds.map (·.1)) ds = true)
    (hbud : budOpened J.p.nums.stages 1 ds asks)
    (hholds : front.holds chain firstTree ((restMember J Js : Member V W X Pb).rounds.map (·.1)) ds = true) :
    ∃ s next nx' rest', AskedOwn J Js (φ.pub m.st.input) (stretches _ ca) m front ds asks s next nx' rest' := by
  have O : OnFreeOwn J Js K chain os (φ.pub m.st.input) (stretches _ ca) m front := hOn rfl
  obtain ⟨a, next, nx', rest', hst', -, hlow, hsz⟩ := reach_gives_trees (renumP J.p) T.reach
  have hst : J.p.nums.stages = a :: next :: nx' :: rest' := hst'
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
  obtain ⟨Dp, cc, R, hT, Sh, Dt⟩ := O.asks
  have hfront : ∀ n, n < 1 + (1 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g)) →
      heardIn J m n = drawnAll J m ds n := fun n hn' => by
    unfold drawnAll
    rw [if_pos (by rw [hn, hk]; rw [hA] at hn'; omega)]
  have F : FormAsks J m.st.input (restFront J m) (carriedCoins J (stretches _ ca))
      (drawnAll J m ds) := by
    rw [← hby]
    exact formAsks_of_draws J _ _ _ _ a next (nx' :: rest') hst FP hall
  have hgr := groups_own firstTree To a next (nx' :: rest') hst hk O ds hholds
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
      endOk := fun c => endOk_of_plan_own J m.st.input (restFront J m)
        (carriedCoins J (stretches _ ca)) (drawnAll J m ds) K Dp cc R T.flag (by rw [hT]; exact T.plan)
        (shapeAsksO_congr J _ _ _ _ _ hfront Sh) F (dataAsks_congr J _ _ _ _ _ hfront Dt) a next nx'
        rest' hst c
      groups := hgr
      fits := hsz _ fun i => (hcnt i).trans (T.declared i).symm, low := hlow
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


/-- **The frame's sentence at the second member.** -/
theorem exact_free_own (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (K : Codes) (chain firstTree : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource))
    (T : PublicTiesOwn J Js K os.length) (To : OpenTies J Js chain os) :
    ExactMember φ σ chain firstTree (onFreeOwn φ J Js K chain os) (budOpened J.p.nums.stages)
      (restMember J Js) := by
  exact exact_rest_own φ σ J Js chain firstTree _ _
    fun ca m front ds asks hOn _ hfit hbud hholds =>
      askedOwn_of_free φ J Js K chain firstTree os T To ca m front ds asks hOn hfit hbud hholds

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.shapeAsksO_congr
#print axioms ProofFile.Honest.K12.PublicTiesOwn
#print axioms ProofFile.Honest.K12.OnFreeOwn
#print axioms ProofFile.Honest.K12.onFreeOwn
#print axioms ProofFile.Honest.K12.groups_own
#print axioms ProofFile.Honest.K12.askedOwn_of_free
#print axioms ProofFile.Honest.K12.exact_free_own
