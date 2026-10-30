-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestFits.lean: the library's own test on a block's view (`Block.Fits`,
Johnson/Top/H0/StepLaws/StepLaws.lean) gives, at a proximity test's block, the two tests on the view
that `k12_returns_one` asks (Johnson/Desc/K12/Honest/Shape/TestReturnsOne.lean): `roundsFit` at the
batching's round and `viewFromB` (TestView.lean) at the stages' rounds, at the very groups of
columns that `Block.step` shows the decision (`Block.shown`). Definitions and theorems. The main
theorem, `view_of_fits`, is stated at the block `proximityTestKind guardedProximityTestParts p` (Johnson/Desc/K12/Frame.lean;
Johnson/Desc/K12/JoinGuarded.lean). It is general in the place p, the codes K, the number ft of the
chain's first own tree, the rounds and the columns, under four tests on the plan.

In the list: a place p (`P12`, Frame.lean) holds the numbers of one proximity test, among them its
stages (`Fmt.M1.Stage`). `laidOf p` (Johnson/Desc/K12/Law/ReadsK.lean) lists the place's declared
rounds (`Fmt.DeclaredRound`), each with its oracle messages; such a list has the type `Laid`. By the
cuts of `proximityTestKind` and `stagesFrom` (Frame.lean), its first round is the batching's, and `laidS p`, the
rest, are the stages' rounds: every stage but the last has the 1 + k rounds of its fold and then the
two rounds of its switch, and the last stage has two rounds. A declared round names the trees that
it opens (`opens`) and the stored tables that it reads (`stored`). A tree's range is 2 ^ a and its
width is W: the fields `a` and `W` of its shape (`Fmt.Shape`). The range of a stage cur is that at
`cur.C.a`. A round as a view has it (`Fmt.RoundView`) has values (`vals`) and what was drawn (`drawn`),
among that the positions (`poss`). A column (`OpenedColumn`, Johnson/Desc/Step.lean) is a tree's key, a
position and a list of words. A wanted column (`Want`, Johnson/Desc/K12/Law/StepGroups.lean) is a
key, a position and a width. `groupsOf F ds Rs` (Johnson/Desc/Block.lean) lists the wanted columns
of the declared rounds ds at the draws Rs: a group for each stored table and each tree of each
round. `regroup` (same file) cuts a list of columns into groups of given lengths and leaves the keys
out: these are the dealt groups. By `step_iff` (StepLaws.lean), `Block.step` returns `.ok` just
where `Block.Fits` holds and the block's decision (`decide`) returns `.ok` at the groups
`Block.shown`.

  `view_of_fits`: under the five hypotheses below: the rounds rs are a first round rB and a list R;
    `roundsFit` passes at the batching's declared round and [rB]; and `viewFromB` passes at the
    stages cur, nxt and rest, at `laidS p`, R and the groups `Block.shown ft rs cols`
  `view_of_groups`: the induction over the stages, from any stage on, at every number F. Under
    `PlanFrom p rest j cur l K` (Johnson/Prover/Link/FormStepPlan.lean) and `OpenA rest cur l`: if
    `roundsFit` passes at the declared rounds of l and the rounds R, and the groups gs have the
    positions and widths of the groups that `groupsOf F` lists there, then
    `viewFromB rest cur l R gs` passes
  `OpenA rest cur l`: a definition, a proposition: the round of a stage that reads columns opens one
    tree, of the stage's range. At the last stage (rest is empty): if the declared rounds of l are
    two, the first opens nothing and the second opens just one tree, whose `a` is `cur.C.a`. At
    every other stage: if l has two more declared rounds after its first 1 + `cur.k`, the second of
    these two opens just one such tree
  `openA_later`: `PlanFrom p rest (j + 1) cur l K` gives `OpenA rest cur l`: from the second stage
    on the plan gives it
  `openA0B cur l`: a definition: a test with code on the plan, which `view_of_fits` asks at the
    first stage: l has two more declared rounds after its first 1 + `cur.k`, and the second of these
    two opens just one tree, whose `a` is `cur.C.a`; `openA_of_B`: where it passes,
    `OpenA (next :: rest) cur l` holds, at every next and rest
  `fit_split`: where `roundsFit ds rs` passes, it passes at the first n of both lists and at the
    rest of both, at any number n
  `pw`, `ww`: definitions: of a dealt column, its position and the number of its words; of a wanted
    column, its position and its width
  `regroup_pw`: under the step's test on the columns each dealt group has its declared positions and
    widths. If the columns got are, in key, position and width (`kpw`, StepGroups.lean), the wanted
    columns of all groups in a row, then what `regroup` cuts of them at the groups' lengths is,
    under `pw`, what the groups are under `ww`
  `groupB_of_pw`: so a group's test of TestView.lean (`groupB`) passes
  `quiet_of_foldCut`: where `foldCut` (Johnson/Prover/Link/FormFold.lean) passes, a fold's declared
    rounds open nothing and read no stored table
  `mod_below`: positions below 2 ^ a are not changed by the reduction modulo 2 ^ a
  `fst_of_pw`: a group that has, under `pw`, the positions of a list xs, each with one width W, has
    the positions xs
  `grp1_one`, `grp1_none`: the wanted groups of one declared round (`grp1`, StepGroups.lean) that
    reads no stored table: one group if it opens one tree, none if it opens none
  `stored_mem`: under `Dealt` (Johnson/Desc/K12/OpenLaws.lean) no declared round of l reads a stored
    table
  `one_answer`: one item of the sort "answer" is one answer

By what. `view_of_fits` takes the block's rounds from `k12_rounds` (StepGroups.lean) and cuts the
batching's round off by `laid_cons` (Johnson/Prover/Link/LinkJoinD.lean) and `fit_split`.
`regroup_pw` turns the second clause of `Block.Fits` into the hypothesis of `view_of_groups` on the
groups; `planFrom_of_ok` (Johnson/Prover/Link/StepPlanOk.lean) and `openA_of_B` give `PlanFrom` and
`OpenA`. `view_of_groups` computes `groupsOf` along a stage's cut by `groupsOf_cons`
(StepGroups.lean), `groupsOf_append` (Johnson/Desc/BlockSlot.lean), `groupsOf_quiet`
(Johnson/Top/H0/MergeLaw/PieceOut.lean), `quiet_of_foldCut`, `grp1_none` and `grp1_one`. It unfolds
`switchCut` and `roundsFit` by `switchCut_says` and `fit_says`
(Johnson/Prover/Link/FormSwitchLaws.lean) and counts rounds by `roundsFit_length` (StepGroups.lean).
`openA_later` calls `cs_opens`, `base_opens` and `listsOf_later`
(Johnson/Prover/Link/DeclPlan.lean). The proof of `regroup_pw` goes as that of the library's
`regroup_pos` (StepGroups.lean) does. `fit_split` has a counterpart in the library's
`roundsFit_append` (StepLaws.lean), which cuts at the first list's length.

Hypotheses of `view_of_fits`. hpl: the block's test on the plan (`planOk`) passes. hB: `batCut`
(Johnson/Prover/Link/FormBat.lean) passes at the place's first declared round, the batching's. hP:
`planFromOk` (StepPlanOk.lean), the plan's test from the first stage on, passes at the stages cur,
nxt and rest, at `laidS p` and the codes K. hA: `openA0B cur (laidS p)` passes. hF:
`Block.Fits ft rs cols` holds of the block.

Limits.
- One way: from `Block.Fits` to the two tests. The converse is not shown.
- Hypotheses next to `Block.Fits`: the block's test on the plan, the test on the batching's declared
  round, the plan's test from the first stage on, `openA0B`: all on the plan.
- A place whose first switch opens several trees does not pass: `openA0B` fails there.
- `view_of_fits` is stated at two stages or more: hP passes only where the place's stages are cur,
  nxt and rest.
- The trees' keys, which `Block.Fits` reads, are read by nothing here. `ww` leaves a wanted column's
  key out, and a dealt group has none.
- `OpenA` is a conditional: where l has not the two declared rounds that it names, it holds
  vacuously. So `OpenA` by itself does not say that a tree is opened. `view_of_groups` calls it only
  at the plan's own cut (`LastPlan.cut`, `StepPlan.cutS`, FormStepPlan.lean), and `openA0B` fails
  where the two rounds are not there.
- No values that meet the five hypotheses of `view_of_fits` together are given in this file.
  Johnson/Desc/K12/Honest/Shape/TestSeatAsksToy.lean gives some (`guard1`, `fits1`): at one small
  made-up place, at ft = 0.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestView
import Johnson.Desc.K12.Law.StepGroups
import Johnson.Top.H0.StepLaws.StepLaws
import Johnson.Top.H0.MergeLaw.PieceOut
import Johnson.Desc.BlockSlot
import Johnson.Prover.Link.DeclPlan
import Johnson.Prover.Link.StepPlanOk
import Johnson.Prover.Link.LinkJoinD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open H2K.JointK (laidS)
open H2K.Sw (kpw Want grp1 groupsOf_cons)

/-! ## 1 General -/

/-- Where `roundsFit` passes, it passes at the first n of both lists and at the rest of both. -/
theorem fit_split : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView) (n : ℕ),
    roundsFit ds rs = true →
    roundsFit (ds.take n) (rs.take n) = true ∧ roundsFit (ds.drop n) (rs.drop n) = true
  | ds, rs, 0, h => ⟨by rw [List.take_zero, List.take_zero]; rfl, h⟩
  | [], [], _ + 1, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _ + 1, h => by cases h
  | _ :: _, [], _ + 1, h => by cases h
  | d :: ds, r :: rs, n + 1, h => by
    unfold roundsFit at h
    rw [Bool.and_eq_true] at h
    obtain ⟨ih1, ih2⟩ := fit_split ds rs n h.2
    refine ⟨?_, ih2⟩
    show roundsFit (d :: ds.take n) (r :: rs.take n) = true
    unfold roundsFit
    rw [Bool.and_eq_true]
    exact ⟨h.1, ih1⟩

/-- A dealt column's position and the number of its words. -/
def pw (z : ℕ × List UInt64) : ℕ × ℕ := (z.1, z.2.length)

/-- A wanted column's position and width; its key is left out. -/
def ww (w : Want) : ℕ × ℕ := (w.2.1, w.2.2)

/-- Under the step's test on the columns, which is the hypothesis, each dealt group has its declared
positions and widths. -/
theorem regroup_pw : ∀ (groups : List (List Want)) (got : List OpenedColumn),
    got.map kpw = groups.flatMap id →
    (regroup (groups.map (·.length)) got).map (·.map pw) = groups.map (·.map ww)
  | [], _, _ => rfl
  | g :: gs, got, h => by
    rw [List.flatMap_cons] at h
    have h1 : (got.take g.length).map kpw = g := by
      rw [List.map_take, h]
      exact List.take_left' rfl
    have h2 : (got.drop g.length).map kpw = gs.flatMap id := by
      rw [List.map_drop, h]
      exact List.drop_left' rfl
    show (((got.take g.length).map fun c => (c.2.1, c.2.2)).map pw) ::
      (regroup (gs.map (·.length)) (got.drop g.length)).map (·.map pw) = _
    rw [regroup_pw gs _ h2, List.map_cons, List.map_map]
    congr 1
    conv_rhs => rw [← h1, List.map_map]
    rfl

/-- Positions below 2 ^ a are not changed by the reduction modulo 2 ^ a. -/
theorem mod_below (a : ℕ) (l : List ℕ) (h : ∀ x ∈ l, x < 2 ^ a) : l.map (· % 2 ^ a) = l := by
  refine (List.map_congr_left fun x hx => ?_).trans (List.map_id l)
  exact Nat.mod_eq_of_lt (h x hx)

theorem fst_of_pw {g : List (ℕ × List UInt64)} {xs : List ℕ} {W : ℕ}
    (h : g.map pw = xs.map fun x => (x, W)) : g.map (·.1) = xs := by
  have k := congrArg (List.map Prod.fst) h
  rw [List.map_map, List.map_map] at k
  exact k.trans (List.map_id xs)

/-- A group with the declared positions and widths passes the group's test (`groupB`,
TestView.lean). -/
theorem groupB_of_pw {a W : ℕ} {poss : List ℕ} {g : List (ℕ × List UInt64)}
    (h : g.map pw = (Fmt.listOf (poss.map (· % 2 ^ a))).map fun x => (x, W)) :
    groupB a W poss g = true := by
  unfold groupB
  rw [Bool.and_eq_true]
  refine ⟨?_, List.all_eq_true.2 fun z hz => ?_⟩
  · rw [fst_of_pw h]
    exact beq_self_eq_true _
  · have k : pw z ∈ g.map pw := List.mem_map.2 ⟨z, hz, rfl⟩
    rw [h] at k
    obtain ⟨x, -, hx⟩ := List.mem_map.1 k
    exact beq_iff_eq.2 (congrArg Prod.snd hx).symm

theorem quiet_of_foldCut {k : ℕ} {ds : List Fmt.DeclaredRound} (h : foldCut k ds = true) :
    ∀ d ∈ ds, d.stored = [] ∧ d.opens = [] := by
  cases ds with
  | nil => cases h
  | cons dE dR =>
    unfold foldCut at h
    rw [Bool.and_eq_true] at h
    intro d hd
    have k1 := List.all_eq_true.1 h.2 d hd
    rw [Bool.and_eq_true, List.isEmpty_iff, List.isEmpty_iff] at k1
    exact k1

/-- One declared round that opens one tree and reads no stored table wants one group of columns. -/
theorem grp1_one (F : ℕ) (d : Fmt.DeclaredRound) (R : Fmt.Drawn) (o : Fmt.Shape × Fmt.TreeSource)
    (hs : d.stored = []) (ho : d.opens = [o]) :
    grp1 F d R = [(Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x =>
      (o.1.tree - F, x, o.1.W)] := by
  unfold grp1
  rw [hs, ho]
  rfl

theorem grp1_none (F : ℕ) (d : Fmt.DeclaredRound) (R : Fmt.Drawn) (hs : d.stored = [])
    (ho : d.opens = []) : grp1 F d R = [] := by
  unfold grp1
  rw [hs, ho]
  rfl

/-! ## 2 The one tree that a stage's reading round opens -/

/-- The round of a stage that reads columns opens one tree, of the stage's range. A conditional:
where l has not the two declared rounds that the clause names, it holds vacuously. -/
def OpenA : List Fmt.M1.Stage → Fmt.M1.Stage → Laid → Prop
  | [], cur, l => ∀ d₁ d₂, l.map (·.1) = [d₁, d₂] →
      d₁.opens = [] ∧ ∃ o, d₂.opens = [o] ∧ o.1.a = cur.C.a
  | _ :: _, cur, l => ∀ dS dC, ((l.drop (1 + cur.k)).take 2).map (·.1) = [dS, dC] →
      ∃ o, dC.opens = [o] ∧ o.1.a = cur.C.a

/-- From the second stage on, the plan (`PlanFrom`) gives `OpenA`. -/
theorem openA_later {p : P12} {rest : List Fmt.M1.Stage} {j : ℕ} {cur : Fmt.M1.Stage} {l : Laid}
    {K : Codes} (h : PlanFrom p rest (j + 1) cur l K) : OpenA rest cur l := by
  cases rest with
  | nil =>
    obtain ⟨-, hD, hst, hm⟩ := h
    intro d₁ d₂ hc
    have hcur : p.nums.stages[j + 1]? = some cur := by
      have := congrArg (·[0]?) hst
      simpa [List.getElem?_drop] using this
    obtain ⟨hj, hxe⟩ := List.getElem?_eq_some_iff.1 (listsOf_later p.nums j cur hm hcur)
    rw [List.drop_eq_getElem_cons hj, hxe] at hD
    obtain ⟨e1, e2⟩ := base_opens cur _ _ l hD d₁ d₂ hc
    exact ⟨e1, _, e2, rfl⟩
  | cons next rest =>
    obtain ⟨-, hD, hst, hm, -⟩ := h
    intro dS dC hc
    have hcur : p.nums.stages[j + 1]? = some cur := by
      have := congrArg (·[0]?) hst
      simpa [List.getElem?_drop] using this
    obtain ⟨hj, hxe⟩ := List.getElem?_eq_some_iff.1 (listsOf_later p.nums j cur hm hcur)
    rw [List.drop_eq_getElem_cons hj, hxe] at hD
    exact ⟨_, (cs_opens cur next rest _ _ l hD dS dC hc).2, rfl⟩

/-- For the first stage: a test with code on the plan. It passes just where l has two more declared
rounds after its first 1 + `cur.k` and the second of these two opens just one tree, of the stage's
range. -/
def openA0B (cur : Fmt.M1.Stage) (l : Laid) : Bool :=
  match ((l.drop (1 + cur.k)).take 2).map (·.1) with
  | [_, dC] =>
    match dC.opens with
    | [o] => o.1.a == cur.C.a
    | _ => false
  | _ => false

theorem openA_of_B {cur next : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {l : Laid}
    (h : openA0B cur l = true) : OpenA (next :: rest) cur l := by
  intro dS dC hc
  unfold openA0B at h
  rw [hc] at h
  dsimp only at h
  split at h
  · rename_i o ho
    exact ⟨o, ho, eq_of_beq h⟩
  · cases h

/-! ## 3 The induction over the stages -/

theorem stored_mem {cur : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {L : List (List Told)}
    {l : Laid} (hD : Dealt cur rest L l) {d : Fmt.DeclaredRound} (hd : d ∈ l.map (·.1)) :
    d.stored = [] := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hd
  exact hD.stored y hy

/-- A round that shows just one item, of the sort "answer", shows one answer. -/
theorem one_answer {vals : List Fmt.ItemValue} (h : vals.map itemOf = [.answer]) :
    ∃ a, vals = [.answer a] := by
  cases vals with
  | nil => cases h
  | cons v t =>
    cases t with
    | cons _ _ => exact absurd (congrArg List.length h) (by simp)
    | nil =>
      cases v with
      | answer a => exact ⟨a, rfl⟩
      | f _ => cases h
      | e _ => cases h
      | word _ => cases h
      | root _ => cases h

/-- **Rounds of the declared form, and groups with the declared positions and widths, pass the
view's test** (`viewFromB`), from any stage on. F: the number of the chain's first own tree. -/
theorem view_of_groups (p : P12) (K : Codes) (F : ℕ) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (R : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
    PlanFrom p rest j cur l K → OpenA rest cur l → roundsFit (l.map (·.1)) R = true →
    gs.map (·.map pw) = (groupsOf F (l.map (·.1)) (R.map (·.drawn))).map (·.map ww) →
    viewFromB rest cur l R gs = true
  | [], j, cur, l, R, gs, hP, hA, hfit, hg => by
    obtain ⟨⟨c, d₁, d₂, Lp⟩, hD, -, -⟩ := hP
    obtain ⟨o1, o, o2, oa⟩ := hA d₁ d₂ Lp.cut
    have s1 : d₁.stored = [] := stored_mem hD (by rw [Lp.cut]; exact List.mem_cons_self)
    have s2 : d₂.stored = [] :=
      stored_mem hD (by rw [Lp.cut]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hfit0 := hfit
    rw [Lp.cut] at hfit hg
    obtain ⟨rL, rB, rfl⟩ := List.length_eq_two.1 (H2K.Sw.roundsFit_length _ _ hfit).symm
    have hG : groupsOf F [d₁, d₂] ([rL, rB].map (·.drawn)) =
        [(Fmt.listOf (rB.drawn.poss.map (· % 2 ^ o.1.a))).map fun x =>
          (o.1.tree - F, x, o.1.W)] := by
      show groupsOf F (d₁ :: [d₂]) (rL.drawn :: [rB.drawn]) = _
      rw [groupsOf_cons, groupsOf_cons, grp1_none F d₁ _ s1 o1, grp1_one F d₂ _ o s2 o2]
      rfl
    rw [hG] at hg
    obtain ⟨g, rfl⟩ : ∃ g, gs = [g] := by
      have k := congrArg List.length hg
      rw [List.length_map, List.length_map] at k
      exact List.length_eq_one_iff.1 k
    have hg1 : g.map pw = (Fmt.listOf (rB.drawn.poss.map (· % 2 ^ o.1.a))).map fun x =>
        (x, o.1.W) := by
      have k : g.map pw = List.map ww ((Fmt.listOf (rB.drawn.poss.map (· % 2 ^ o.1.a))).map
          fun x => (o.1.tree - F, x, o.1.W)) := List.head_eq_of_cons_eq hg
      rw [List.map_map] at k
      exact k
    obtain ⟨-, ⟨-, -, -, g5⟩, -⟩ := fit_says hfit
    have hx : ∀ x ∈ rB.drawn.poss, x < 2 ^ cur.C.a := by
      intro z hz
      have k := List.all_eq_true.1 g5 z hz
      rw [Lp.logN] at k
      exact of_decide_eq_true k
    show (roundsFit (l.map (·.1)) [rL, rB] && g.map (·.1) == Fmt.listOf rB.drawn.poss) = true
    rw [Bool.and_eq_true, fst_of_pw hg1, oa, mod_below _ _ hx]
    exact ⟨hfit0, beq_self_eq_true _⟩
  | next :: rest, j, cur, l, R, gs, hP, hA, hfit, hg => by
    obtain ⟨⟨c, n, dS, dC, Pl⟩, hD, -, -, hPt⟩ := hP
    obtain ⟨o, o2, oa⟩ := hA dS dC Pl.cutS
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, c13, c14, c15⟩ := switchCut_says Pl.cutSw
    have sS : dS.stored = [] := List.isEmpty_iff.1 c14
    have sC : dC.stored = [] := List.isEmpty_iff.1 c15
    have ed : (l.drop (1 + cur.k)).drop 2 = l.drop (cur.k + 3) := by
      rw [List.drop_drop]
      congr 1
      omega
    have el : l.map (·.1) = (l.take (1 + cur.k)).map (·.1) ++
        (dS :: dC :: (l.drop (cur.k + 3)).map (·.1)) := by
      have k1 : l.drop (1 + cur.k) = (l.drop (1 + cur.k)).take 2 ++ l.drop (cur.k + 3) := by
        rw [← ed, List.take_append_drop]
      have k2 : (l.drop (1 + cur.k)).map (·.1) = dS :: dC :: (l.drop (cur.k + 3)).map (·.1) := by
        rw [k1, List.map_append, Pl.cutS]
        rfl
      rw [← k2, ← List.map_append, List.take_append_drop]
    have hlen : l.length = R.length := by
      have k := H2K.Sw.roundsFit_length _ _ hfit
      rwa [List.length_map] at k
    have h2 : (1 + cur.k) + 2 ≤ l.length := by
      have k := congrArg List.length Pl.cutS
      rw [List.length_map, List.length_take, List.length_drop] at k
      simp only [List.length_cons, List.length_nil] at k
      omega
    obtain ⟨fF, fD⟩ := fit_split _ _ (1 + cur.k) hfit
    rw [← List.map_take] at fF
    rw [← List.map_drop] at fD
    obtain ⟨fS, fR⟩ := fit_split _ _ 2 fD
    rw [← List.map_take, Pl.cutS] at fS
    rw [← List.map_drop, ed] at fR
    obtain ⟨rS, rC, R', hRd⟩ : ∃ rS rC R', R.drop (1 + cur.k) = rS :: rC :: R' := by
      have k : 2 ≤ (R.drop (1 + cur.k)).length := by
        rw [List.length_drop]
        omega
      cases hq : R.drop (1 + cur.k) with
      | nil =>
        rw [hq] at k
        simp at k
      | cons a t =>
        cases t with
        | nil =>
          rw [hq] at k
          simp at k
        | cons b t' => exact ⟨a, b, t', rfl⟩
    rw [hRd] at fS fR
    have fS' : roundsFit [dS, dC] [rS, rC] = true := fS
    have fR' : roundsFit ((l.drop (cur.k + 3)).map (·.1)) R' = true := fR
    have eR : R.map (·.drawn) = (R.take (1 + cur.k)).map (·.drawn) ++
        (rS.drawn :: rC.drawn :: R'.map (·.drawn)) := by
      have k : R = R.take (1 + cur.k) ++ (rS :: rC :: R') := by
        rw [← hRd, List.take_append_drop]
      conv_lhs => rw [k]
      rw [List.map_append]
      rfl
    have hG : groupsOf F (l.map (·.1)) (R.map (·.drawn)) =
        ((Fmt.listOf (rC.drawn.poss.map (· % 2 ^ o.1.a))).map fun x =>
          (o.1.tree - F, x, o.1.W)) ::
          groupsOf F ((l.drop (cur.k + 3)).map (·.1)) (R'.map (·.drawn)) := by
      rw [el, eR, groupsOf_append F _ _ _ _ (by
          rw [List.length_map, List.length_map, List.length_take, List.length_take, hlen]),
        First.MergeLaw.groupsOf_quiet F _ _ (quiet_of_foldCut Pl.cutF), List.nil_append,
        groupsOf_cons, groupsOf_cons, grp1_none F dS _ sS Pl.opensS, grp1_one F dC _ o sC o2]
      rfl
    rw [hG] at hg
    cases gs with
    | nil => cases hg
    | cons g gs' =>
      have hg1 : g.map pw = (Fmt.listOf (rC.drawn.poss.map (· % 2 ^ o.1.a))).map fun x =>
          (x, o.1.W) := by
        have k : g.map pw = List.map ww ((Fmt.listOf (rC.drawn.poss.map (· % 2 ^ o.1.a))).map
            fun x => (o.1.tree - F, x, o.1.W)) := List.head_eq_of_cons_eq hg
        rw [List.map_map] at k
        exact k
      have hg2 : gs'.map (·.map pw) = (groupsOf F ((l.drop (cur.k + 3)).map (·.1))
          (R'.map (·.drawn))).map (·.map ww) := List.tail_eq_of_cons_eq hg
      have ih := view_of_groups p K F rest (j + 1) next (l.drop (cur.k + 3)) R' gs' hPt
        (openA_later hPt) fR' hg2
      have b1 : rC.vals.map itemOf = dC.items.filter (· != .root) := by
        have k := fS'
        simp only [roundsFit, Bool.and_eq_true, beq_iff_eq] at k
        exact k.2.1.1.1.1.1.1.1
      obtain ⟨a, ha⟩ := one_answer (b1.trans c13)
      have hw : widthOf [dS, dC] = o.1.W := by
        unfold widthOf
        simp [Pl.opensS, o2]
      rw [oa] at hg1
      unfold viewFromB
      rw [hRd]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨⟨by omega, fF⟩, by rw [Pl.cutS]; exact fS'⟩, by rw [ha]⟩, ?_⟩, ?_⟩, ih⟩
      · rw [Pl.cutS, hw]
        simp [Pl.opensS, o2]
      · rw [Pl.cutS, hw]
        exact groupB_of_pw hg1

/-! ## 4 At the block -/

/-- **The library's test on the block's view gives the two tests on the view, at the groups that
the decision is shown.** ft: the number of the chain's first own tree. -/
theorem view_of_fits {p : P12} {cur nxt : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {K : Codes}
    (hpl : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true)
    (hB : batCut (((H2K.JointK.laidOf p).take 1).map (·.1)) = true)
    (hP : planFromOk p (nxt :: rest) 0 cur (laidS p) K = true)
    (hA : openA0B cur (laidS p) = true) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hF : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).Fits ft rs cols) :
    ∃ rB R, rs = rB :: R ∧
      roundsFit (((H2K.JointK.laidOf p).take 1).map (·.1)) [rB] = true ∧
      viewFromB (nxt :: rest) cur (laidS p) R
        ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).shown ft rs cols) = true := by
  obtain ⟨f1, f2⟩ := hF
  have er := H2K.Sw.k12_rounds (Cl := Unit) guardedProximityTestParts p hpl
  obtain ⟨a, hl, ha1, ha2⟩ := laid_cons _ hB
  have el : (H2K.JointK.laidOf p).map (·.1) = a.1 :: (laidS p).map (·.1) := by
    conv_lhs => rw [hl]
    rfl
  have f2' : (cols.take ((groupsOf ft (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds
      (rs.map (·.drawn))).flatMap id).length).map kpw =
      (groupsOf ft (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds (rs.map (·.drawn))).flatMap id :=
    eq_of_beq f2
  have hpw := regroup_pw _ _ f2'
  rw [er, el] at f1
  cases rs with
  | nil => cases f1
  | cons rB R =>
    obtain ⟨g1, g2⟩ := fit_split _ _ 1 f1
    refine ⟨rB, R, rfl, ?_, ?_⟩
    · have k : ((H2K.JointK.laidOf p).take 1).map (·.1) = [a.1] := by
        rw [hl]
        rfl
      rw [k]
      exact g1
    · refine view_of_groups p K ft (nxt :: rest) 0 cur (laidS p) R _
        (planFrom_of_ok p _ _ _ _ _ hP) (openA_of_B hA) g2 ?_
      have k : groupsOf ft (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds
          ((rB :: R).map (·.drawn)) = groupsOf ft ((laidS p).map (·.1)) (R.map (·.drawn)) := by
        rw [er, el]
        show groupsOf ft (a.1 :: _) (rB.drawn :: _) = _
        rw [groupsOf_cons, grp1_none ft a.1 _ ha1 ha2]
        rfl
      rw [← k]
      exact hpw

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.fit_split
#print axioms ProofFile.Honest.Sh.regroup_pw
#print axioms ProofFile.Honest.Sh.mod_below
#print axioms ProofFile.Honest.Sh.fst_of_pw
#print axioms ProofFile.Honest.Sh.groupB_of_pw
#print axioms ProofFile.Honest.Sh.quiet_of_foldCut
#print axioms ProofFile.Honest.Sh.grp1_one
#print axioms ProofFile.Honest.Sh.grp1_none
#print axioms ProofFile.Honest.Sh.openA_later
#print axioms ProofFile.Honest.Sh.openA_of_B
#print axioms ProofFile.Honest.Sh.stored_mem
#print axioms ProofFile.Honest.Sh.one_answer
#print axioms ProofFile.Honest.Sh.view_of_groups
#print axioms ProofFile.Honest.Sh.view_of_fits
#print axioms ProofFile.Honest.Sh.pw
#print axioms ProofFile.Honest.Sh.ww
#print axioms ProofFile.Honest.Sh.OpenA
#print axioms ProofFile.Honest.Sh.openA0B
