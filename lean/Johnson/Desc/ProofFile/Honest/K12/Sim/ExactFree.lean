-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ExactFree.lean: the frame's own sentence `exact` at a
proximity test's second member, at a written `On` no clause of which speaks of the part's own
challenges. It is stated at a state on entry that is made of the plan's public part, not shown to be
the verifier's. The one clause of `OnPlan` (Sim/ExactPlan.lean) that did, "the listed column is the
tree's at the positions that the first reading round opens", follows from the frame's own premise
`Before.holds` (Johnson/Desc/ProofFile/Honest/Side.lean) and from clauses without these challenges.
Conditional on public ties. No property is claimed: whether a chain's run meets `OnFree` at any
place is not shown. General in the face φ (`Face`), the side σ, the two jobs J and Js, the table of
codes K, the numbers chain and firstTree and the opening o. Sim/ExactFreeKR.lean and
Sim/ExactSide.lean call `exact_free`. Definitions, statements and proofs.

Terms. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean with Honest/Side.lean. `exact` is a
field of its structure `Good`, and `ExactMember` (Honest/Small/Field.lean) is that field's text at
one member. A side (`Side`) has a sub-protocol and a list of the prover's parts (`Part`), each
paired with a term of type `Sim`. A member (`Member`) is one part with its number in the list, its
declared rounds and that term. `On` and `bud` are parameters of `Good`: a condition at a part's
start, and which positions may be read at given challenges. m (`Mid`) is the state of a chain's run
between two rounds. The front (`Before`) is what a part's simulator is given of the run before its
part; what it lists of a tree is the list of pairs (position, column) that `Before.treeCols`
returns. A place (`P12`) holds the numbers of a proximity test, among them its list of stages
(`Fmt.M1.Stage`); a place of a file is the place of a test in one of the files that the library
describes, such as the key file. A job J (`TestJob`, …/K12/Test.lean) is what a caller supplies for
its test, and the simulators' job Js (`SimJob`, Sim/Sims.lean) is what a caller says of its test to
the simulators. The tree, the real tree and the run's own tree are the one tree that `J.trees₀`
returns at m and mem, the coins that the part carries, by number; the simulators' tree is that of
`Js.trees₀ front`. The rows are the first stage's state (`rowsAt`, Sim/Row.lean). The text is the
Lean function that computes the test's rounds (`testAll`, …/K12/Test.lean). The first part has the
test's first `firstLen` rounds (…/K12/Parts.lean), the second part all the others, and the second
member is `restMember J Js` (Sim/Row.lean). ds is the list of the second part's own challenges.
Rounds and members are counted from 0. The first reading round is the round whose positions
`openedAt` takes at the first stage; under the hypotheses of `onPlan_of_free` it is the second
part's round number 1. An opening o is a tree's shape (`Fmt.Shape`, with the depth `a`) paired with
its source (`Fmt.TreeSource`). The public ties are the fields of `PubTies` (Sim/ExactPlan.lean) and of
`OpenTie`. A member of a condition is a choice of values at which it holds. To pay a clause is to
prove it.

  `exact_free`: the statement: under `PubTies J Js K` and `OpenTie J Js chain o`:
    `ExactMember φ σ chain firstTree` at `On` := `onFree φ J Js K chain o`, at `bud` :=
    `budOpened J.p.nums.stages` (Sim/ExactPlan.lean) and at the member `restMember J Js`; at a state
    on entry that is made of the plan's public part, not shown to be the verifier's
  `onPlan_of_free`: `OnFree` gives `OnPlan` at the same arguments and at every firstTree, under
    `OpenTie`, where the list of stages is a :: next :: rest and a.k = `(sgOf a).h + (sgOf a).g`
  `cols_of_holds`: the front holds what the rounds read · it lists the tree · what it lists of the
    tree is the tree's ⟹ at every position that the round opens, the column that is looked up in the
    front is the tree's. General in the front, the declared rounds, the challenges and the function
    colR that is in the tree's place; the hypotheses are named at the theorem
  `OnFree J Js K chain o pb mem m front`: a structure: what is asked at the second part's entry, in
    eight clauses. Seven are clauses of `OnPlan`, word for word, described at their fields there:
    `le`, `leS`, `heardFit`, `heard`, `door`, `fold`, `asks`. The eighth, `tree`, is in the place of
    `cols`
  `onFree`: a definition: `OnFree` in the type of the frame's `On`. At a member whose number is not
    1 it asks nothing
  `OpenTie J Js chain o`: a structure: public: the part's round number 1 is declared to open one
    tree, of the first stage's depth; the simulators' job names that tree
  `reads_mem`: what the declared round number i opens is among the frame's reads (`readsOf`): one
    read for each opening and each listed position
  `lookup_mem`, `lookup_of_any`: on `List.lookup` at a list of pairs whose first entries are
    numbers: where it returns `some w` at x, the pair (x, w) is in the list; where some pair's first
    entry is x, it returns `some` at x

By what. `exact_free` is `exact_plan` (Sim/ExactPlan.lean) after `onPlan_of_free`; the list of
stages comes from `reach_gives` (Sim/Reach.lean), and a.k = `(sgOf a).h + (sgOf a).g` from h ≤ k at
the first stage (`formPub_of_B`, …/K12/FormPubAt.lean). `onPlan_of_free` passes seven clauses on
unchanged and proves `cols` from `tree` and `OpenTie` by `cols_of_holds`, after unfolding
`SimJob.trees₀` (Sim/Sims.lean), `openedAt`, `openAt` (Johnson/LinkSim/AtText/ShiftDefs.lean) and
`drawnAll` (Sim/Exact.lean). `cols_of_holds` reads `Before.holds` at the read that `reads_mem`
gives, then calls `lookup_of_any` and `lookup_mem`. `reads_mem` and the two lemmas on `List.lookup`
go by recursion on the list.

How. The frame's `readsOf` (…/Honest/Frame.lean) and the text's own list of opened positions
(`openedAt`, Johnson/LinkSim/AtText/SpecStage.lean) reduce and list the sampled positions by one
formula. In Lean: both map `· % 2 ^ a` over the sampled positions; `Fmt.listOf` is applied inside
`readsOf`, and to `openedAt` in the clause `cols`. So where the front holds a column for every read,
it lists one at every opened position; the simulators' tree looks it up; and what is listed is the
real tree's, by a clause that ties the front to the run's own tree (it reads the input, the rows and
the front; what it does not read is the part's challenges).

Hypotheses. `exact_free` has two, next to those inside `ExactMember`:
  `T : PubTies J Js K`: eight fields on public numbers and on the two jobs' public fields, listed in
    the head of Sim/ExactPlan.lean
  `To : OpenTie J Js chain o`: three fields. `decl`: the second part has a declared round number 1,
    and its list of openings is [o]. `depth`: `o.1.a` is the first stage's depth `(sgOf J.s₀).C.a`.
    `opens`: `Js.opens` has one entry, made of `srcOf chain o.2` and `o.1.a`

Limits.
- It is stated at a state on entry that is made of the plan's public part, not shown to be the
  verifier's: `J.rec₀` is a field of the free parameter J, and no clause compares it with a
  verifier's state: `door` compares it with `Js.rec₀`, and `ShapeAsks` and `DataAsks`
  (…/K12/PlanB.lean) have clauses on it.
- Those of Sim/ExactPlan.lean but for its item on the clause `cols` of `OnPlan`, which reads ds.
- `OnFree` has no member at a place of a file. `OnFree` has no value that meets it in the library:
  the statements that conclude `OnFree` take its clauses `door`, `asks` and `tree` as premises
  (`onFree_of_play`, Sim/OnFromPlay.lean; `onFree_of_lent`, Sim/OnFromLent.lean; `onFree_of_five`,
  E2E/OfflineTestFive.lean), and `ShapeAsks` and `DataAsks` are concluded, among others, from the
  like on the state on entry (`shapeAsks_of_front`, `dataAsks_of_front`, …/K12/ShapeAll.lean), from
  the test `coreB` and two equations on the codes (`sorts_of_coreB`, …/K12/SortsMember.lean; it has
  values at two small made-up places: `sorts_one`, `sorts_came`) and, under the library's head and
  `SaysAt`, at two trees, where `OnFree` asks one (`asks_head`, …/K12/AsksWhole.lean): by reading
  the files that name them.
- Five of its eight clauses follow from the frame's own play of the first part
  (Sim/OnFromPlay.lean). That theorem, `onFree_of_play`, has hypotheses of its own, among them
  `Agree` (…/K12/CoinsAgree.lean), and the three other clauses, `door`, `asks` and `tree`, are
  hypotheses of it (`AtEntry`).
- By type the clause `tree` also reads mem, the coins that the part carries: mem is an argument of
  `J.trees₀` and of `rowsAt`.
- In a run the front itself moves with the part's own challenges (it lists the columns at all
  positions that are read in the whole run): so whoever pays the clause `tree` over runs pays it at
  every list of these challenges all the same; what is won is that the condition has the frame's
  type. `onPlan` (Sim/ExactPlan.lean) has that type too: its clause `cols` binds ds by "at every
  list ds". The frame's function from a run to such a front is `Run.beforeAt` (Honest/Side.lean).
- The hypotheses on public numbers are proved at one of the library's nine closed places (places
  written out as closed terms), the key file's test on the ranges (Sim/ExactAtKR.lean,
  Sim/ExactFreeKR.lean), where J and Js are free parameters too and the ties on their public fields
  are hypotheses; at the two others where `reachB` says "true" they are not evaluated. The counts
  nine and two: by reading Sim/ReachAt.lean.
- At the level of oracle messages: no root, salt or hash. Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (openedAt openAt)
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

/-! ## 1 From "the front holds what is read" to the columns -/

theorem lookup_mem {β : Type} : ∀ (l : List (ℕ × β)) (x : ℕ) (w : β), l.lookup x = some w →
    (x, w) ∈ l
  | [], _, _, h => by simp at h
  | (k, b) :: l, x, w, h => by
    by_cases c : x = k
    · subst c
      simp only [List.lookup_cons, beq_self_eq_true] at h
      cases h
      exact List.mem_cons_self
    · have c' : (x == k) = false := beq_eq_false_iff_ne.2 c
      simp only [List.lookup_cons, c'] at h
      exact List.mem_cons_of_mem _ (lookup_mem l x w h)

theorem lookup_of_any {β : Type} : ∀ (l : List (ℕ × β)) (x : ℕ),
    (l.any fun c => c.1 == x) = true → ∃ w, l.lookup x = some w
  | [], _, h => by simp at h
  | (k, b) :: l, x, h => by
    by_cases c : x = k
    · subst c
      exact ⟨b, by simp only [List.lookup_cons, beq_self_eq_true]⟩
    · have c' : (x == k) = false := beq_eq_false_iff_ne.2 c
      have c'' : (k == x) = false := beq_eq_false_iff_ne.2 (Ne.symm c)
      simp only [List.any_cons, c'', Bool.false_or] at h
      obtain ⟨w, hw⟩ := lookup_of_any l x h
      exact ⟨w, by simp only [List.lookup_cons, c']; exact hw⟩

/-- What the declared round number i opens is among the frame's reads. In Lean: let d be the
declared round number i, R the challenge number i and o an opening of d. Then for every x in
`Fmt.listOf` of the positions of R reduced modulo `2 ^ o.1.a`, `readsOf` has a read at position x,
of no stored item, with the source `srcOf chain o.2`. At every chain, firstTree, st and tr. -/
theorem reads_mem (chain firstTree : ℕ) (st : ℕ → ℕ → Option (List UInt64))
    (tr : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) :
    ∀ (decls : List Fmt.DeclaredRound) (ds : List Fmt.Drawn) (i : ℕ) (d : Fmt.DeclaredRound)
      (R : Fmt.Drawn), decls[i]? = some d → ds[i]? = some R → ∀ o ∈ d.opens,
      ∀ x ∈ Fmt.listOf (R.poss.map (· % 2 ^ o.1.a)),
      ∃ q ∈ readsOf chain firstTree st tr decls ds,
        q.pos = x ∧ q.item = none ∧ q.src = some (srcOf chain o.2)
  | [], _, _, _, _, h, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _, _, _, _ => by simp at h
  | d' :: decls, R' :: ds, 0, d, R, h1, h2, o, ho, x, hx => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    refine ⟨⟨o.1.tree - firstTree, x, none, some (srcOf chain o.2), (tr o.2).map (·.1),
      (tr o.2).map (·.2.col x), o.1.W⟩, ?_, rfl, rfl, rfl⟩
    unfold readsOf
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    exact List.mem_flatMap.2 ⟨o, ho, List.mem_map.2 ⟨x, hx, rfl⟩⟩
  | d' :: decls, R' :: ds, i + 1, d, R, h1, h2, o, ho, x, hx => by
    simp only [List.getElem?_cons_succ] at h1 h2
    obtain ⟨q, hq, e⟩ := reads_mem chain firstTree st tr decls ds i d R h1 h2 o ho x hx
    refine ⟨q, ?_, e⟩
    unfold readsOf
    exact List.mem_append_right _ hq

/-- **At every position that the round opens, the column that is looked up in the front is the
tree's.** Hypotheses. hh: `front.holds` passes at the declared rounds decls and the challenges ds.
hd, hR, ho: d is the declared round number i, R the challenge number i, and o an opening of d. hl:
the front lists cols at the source of o. hT: each pair in cols has the column that colR gives at its
position. colR is a free parameter: "the tree" is any function that meets hT. -/
theorem cols_of_holds (front : Before) (chain firstTree : ℕ) (decls : List Fmt.DeclaredRound)
    (ds : List Fmt.Drawn) (hh : front.holds chain firstTree decls ds = true) (i : ℕ)
    (d : Fmt.DeclaredRound) (R : Fmt.Drawn) (hd : decls[i]? = some d) (hR : ds[i]? = some R)
    (o : Fmt.Shape × Fmt.TreeSource) (ho : o ∈ d.opens) (cols : List (ℕ × List UInt64))
    (hl : front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2 = some cols)
    (colR : ℕ → List UInt64) (hT : ∀ q ∈ cols, q.2 = colR q.1) :
    ∀ x ∈ Fmt.listOf (R.poss.map (· % 2 ^ o.1.a)), colR x = (cols.lookup x).getD [] := by
  intro x hx
  obtain ⟨q, hq, e1, e2, e3⟩ := reads_mem chain firstTree (fun _ _ => none) (fun _ => none) decls
    ds i d R hd hR o ho x hx
  have h := List.all_eq_true.1 hh q hq
  rw [e2, e3] at h
  simp only [hl, e1] at h
  obtain ⟨w, hw⟩ := lookup_of_any cols x h
  rw [hw]
  exact (hT _ (lookup_mem cols x w hw)).symm

/-! ## 2 What is asked -/

/-- Public: the part's round number 1 is declared to open one tree, of the first stage's depth; the
simulators' job names that tree. The part is the second, and rounds are counted from 0. o: that
opening. The three fields read `J.p`, `Js.opens`, chain and o only. -/
structure OpenTie (J : TestJob W X) (Js : SimJob Pb) (chain : ℕ) (o : Fmt.Shape × Fmt.TreeSource) :
    Prop where
  decl : ∃ d, (J.laid.drop (firstLen J.p.nums.stages))[1]? = some d ∧ d.1.opens = [o]
  depth : o.1.a = (sgOf J.s₀).C.a
  opens : Js.opens = [((srcOf chain o.2).1, (srcOf chain o.2).2, o.1.a)]

/-- What is asked at the second part's entry: no clause speaks of the part's own challenges. pb: the
input's public part. mem: the stretches that the part carries, by number. chain: the chain's number,
as the frame's `srcOf` takes it. o: the opening of `OpenTie`. The clauses `le` to `asks` are those
of `OnPlan` (Sim/ExactPlan.lean), word for word, and are described at their fields there. `door`
compares the two jobs' fields `rec₀`. No statement that this state is the verifier's. -/
structure OnFree (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (o : Fmt.Shape × Fmt.TreeSource) (pb : Pb) (mem : ℕ → Stretch) (m : Mid W X) (front : Before) :
    Prop where
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
  asks : ∃ Dp cc R, Dp.ts.length = 1 ∧
    ShapeAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc R
  /-- one tree in front, of the first stage's depth; the front lists it; what the front lists of it
  is the tree's. cols is what `Before.treeCols` returns at the source of o -/
  tree : ∃ colR cols, J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m) =
      [((sgOf J.s₀).C.a, colR)] ∧
    front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2 = some cols ∧
    ∀ q ∈ cols, q.2 = colR q.1

/-- `OnFree` in the type of the frame's `On`: at a member whose number is not 1 it asks nothing. -/
def onFree (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (o : Fmt.Shape × Fmt.TreeSource) (u : Member V W X Pb) (ca : CsAll u.part.carries) (m : Mid W X)
    (front : Before) : Prop :=
  u.number = 1 → OnFree J Js K chain o (φ.pub m.st.input) (stretches _ ca) m front

/-- `OnFree` gives `OnPlan`, the condition of Sim/ExactPlan.lean, at every firstTree. Hypotheses:
`OpenTie`; hst: the list of stages is a :: next :: rest; hk: a.k = `(sgOf a).h + (sgOf a).g`. -/
theorem onPlan_of_free {J : TestJob W X} {Js : SimJob Pb} {K : Codes} {chain : ℕ}
    {o : Fmt.Shape × Fmt.TreeSource} {pb : Pb} {mem : ℕ → Stretch} {m : Mid W X} {front : Before}
    (firstTree : ℕ) (T : OpenTie J Js chain o) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: rest) (hk : a.k = (sgOf a).h + (sgOf a).g)
    (O : OnFree J Js K chain o pb mem m front) : OnPlan J Js K chain firstTree pb mem m front := by
  obtain ⟨colR, cols, htr, hl, hT⟩ := O.tree
  obtain ⟨d, hd, hop⟩ := T.decl
  have hs0 : J.s₀ = a := by unfold TestJob.s₀; rw [hst]; rfl
  have hn : firstLen J.p.nums.stages = 2 + a.k := by rw [hst]; rfl
  refine ⟨O.le, O.leS, O.heardFit, O.heard, O.door, O.fold, O.asks, colR,
    fun q => (cols.lookup q).getD [], htr, ?_, fun ds hh x hx => ?_⟩
  · unfold SimJob.trees₀
    rw [T.opens]
    simp only [List.map_cons, List.map_nil, hl, Option.getD_some, T.depth]
  · have e : openedAt (drawnAll J m ds) (J.p.nums.stages.drop 1) J.s₀ 1 =
        (ds.getD 1 noDraw).poss.map (· % 2 ^ o.1.a) := by
      unfold openedAt openAt drawnAll
      rw [hst, hs0, T.depth, hs0]
      simp only [List.drop_succ_cons, List.drop_zero, List.isEmpty_cons, Bool.false_eq_true,
        if_false]
      rw [if_neg (by show ¬ _ < firstLen (a :: next :: rest); show ¬ _ < 2 + a.k; omega)]
      congr 3
      show 1 + 2 + ((sgOf a).h + (sgOf a).g) - (2 + a.k) = 1
      omega
    rw [e] at hx
    cases hR : ds[1]? with
    | none =>
      have : ds.getD 1 noDraw = noDraw := by rw [List.getD_eq_getElem?_getD, hR]; rfl
      rw [this] at hx
      simp [noDraw, Fmt.listOf] at hx
    | some R =>
      have : ds.getD 1 noDraw = R := by rw [List.getD_eq_getElem?_getD, hR]; rfl
      rw [this] at hx
      exact cols_of_holds front chain firstTree _ ds hh 1 d.1 R
        (by rw [List.getElem?_map, hd]; rfl) hR o (by rw [hop]; exact List.mem_singleton.2 rfl)
        cols hl colR hT x hx

/-! ## 3 The statement -/

/-- **The frame's sentence at the second member, at a condition that reads none of the part's own
challenges.** It is stated at a state on entry that is made of the plan's public part, not shown to
be the verifier's. Under `PubTies` and `OpenTie`, at `On` := `onFree` and `bud` := `budOpened`. -/
theorem exact_free (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (K : Codes) (chain firstTree : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (T : PubTies J Js K)
    (To : OpenTie J Js chain o) :
    ExactMember φ σ chain firstTree (onFree φ J Js K chain o) (budOpened J.p.nums.stages)
      (restMember J Js) := by
  obtain ⟨a, next, nx', rest', hst, -, -, -, -⟩ := reach_gives J.p T.reach
  have FP := formPub_of_B J.p a next (nx' :: rest') hst T.form
  have hk : a.k = (sgOf a).h + (sgOf a).g := by
    have := FP.hk
    show a.k = a.h + (a.k - a.h)
    omega
  intro ca m front ds asks hOn
  exact exact_plan φ σ J Js K chain firstTree T ca m front ds asks
    fun h1 => onPlan_of_free firstTree To a next (nx' :: rest') hst hk (hOn h1)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.lookup_mem
#print axioms ProofFile.Honest.K12.lookup_of_any
#print axioms ProofFile.Honest.K12.reads_mem
#print axioms ProofFile.Honest.K12.cols_of_holds
#print axioms ProofFile.Honest.K12.onPlan_of_free
#print axioms ProofFile.Honest.K12.exact_free
#print axioms ProofFile.Honest.K12.OpenTie
#print axioms ProofFile.Honest.K12.OnFree
#print axioms ProofFile.Honest.K12.onFree
