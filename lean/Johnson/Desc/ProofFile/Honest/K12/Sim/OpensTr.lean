-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/OpensTr.lean: what a proximity test's own declared rounds read
of a tree that the test itself sends lies among the positions that the next reading round samples.
This is `own_reads_tr`. It is stated at every job J (`TestJob`, …/K12/Test.lean: what a caller
supplies for its test) and at all values of its other parameters, under the hypotheses below. It
ties two definitions. The frame (Johnson/Desc/ProofFile/Honest/Frame.lean) computes what declared
rounds read (`readsOf`). `budOpened` (Sim/ExactPlan.lean), a value for the parameter `bud` of `Good`
(Johnson/Desc/ProofFile/Honest/Side.lean), is stated with `openedTr` (Sim/CoreText.lean). The two
are tied through the list of the term's openings (`opensFrom`, …/K12/TermOpens.lean; `opensTest`,
…/K12/ColsTerm.lean) and the public clause that the declared openings are the term's (`OpensFit`,
ColsTerm.lean). `bud_own` (Sim/BudOwn.lean) calls `own_reads_tr`. Five theorems with their proofs.
On positions alone: no column, no coin.

In the list: …/K12/ is Johnson/Desc/ProofFile/Honest/K12/, and Sim/ is a folder in it. The term is
the Lean function that computes the test's rounds (`testAll`, Test.lean; from a stage on
`stagesAll`, Johnson/Desc/K12/Honest/Stages.lean); no statement of this file names it. A stage is a
`Fmt.M1.Stage`, and n is `(sgOf cur).h + (sgOf cur).g` at the stage cur. A reading round is a round
at whose sampled positions trees are read. An opening is a triple (round, depth, origin): the
reading round's number, the tree's depth, and the tree's origin (`From`, TermOpens.lean): `old k`,
the job's tree number k, or `sent r`, the tree that the test's round number r sends. A declared
opening (`planOpens`, …/K12/PlanOpens.lean) has a source (`Fmt.TreeSource`) where an opening has its
origin. `srcOf chain` (the frame) gives for a source the number of the chain that sends the tree and
the tree's number in that chain's order of sending. D has the challenges (`Fmt.Drawn`) by the
round's number. An opening's positions are `Fmt.listOf` of the list `(D round).poss`, each taken
modulo 2 ^ depth: their set, in increasing order. A read (`Read`, the frame) has the fields `pos`, a
position, and `src`: at a tree, `some` of the pair that `srcOf` gives. `depthAt J r` (Test.lean) is
the depth of the tree that the test's round number r sends, if any, computed from the stages and
from whether `J.fresh` is `none`. `sentBefore J r` (…/K12/SentTables.lean) counts the rounds below r
at which `depthAt` is `some`. `openedTr D rest cur o i` lists the positions at which the tree that
round number o + i sends is opened, where cur is a stage, rest the later stages and o the number of
the first round of cur. It is the empty list at every i that is not the first round of a switch, the
step from one stage to the next (at cur: i = 1 + n).

  `own_reads_tr`: under the hypotheses below, for a round r at which `depthAt J r` is `some`: every
    read q in `readsOf chain firstTree stored tree decls Rs` whose `src` is
    `some (chain, sent + sentBefore J r)` has `q.pos` in `openedTr D rest s 1 (r - 1)`
  `opens_tr`: each opening in the term's list from a stage on, `opensFrom rest cur o fr`, is of one
    of two kinds. Either it is of a tree in fr, the trees that hold the stage's rows, with that
    tree's depth and origin, at the stage's own reading round: number o + 1 if rest is empty, and
    o + 2 + n if not. Or its origin is `sent r` with o ≤ r, and then its positions, each once, are
    `openedTr D rest cur o (r - o)`. No hypothesis: fr, o and D are free parameters
  `reads_plan`: a read of declared rounds that read no stored table is a read of a declared opening.
    For rounds decls with `d.stored = []` at each, numbered from i, and challenges Rs whose entry n
    is `D (i + n)`: for every q in `readsOf chain firstTree stored tree decls Rs` there is an x in
    `planOpens decls i` such that `q.src` is `some` of `srcOf chain` at the source of x, and `q.pos`
    is among the positions of x
  `sentBefore_lt`, `sentBefore_inj`: if `depthAt J r` is `some` and r < r', then
    `sentBefore J r < sentBefore J r'`; so two rounds at which `depthAt` is `some` and `sentBefore`
    has the same value are one round

By what. `own_reads_tr`: `reads_plan`, whose first hypothesis is the field `stored` of `OpensFit`,
gives a declared opening. By the field `opens` it comes from an opening of `opensTest`, which at the
stages s :: rest is `opensFrom rest s 1 (frontTrees depths)` (ColsTerm.lean), and `opens_tr` gives
the two kinds. At an origin `old k` the field `olds` gives k below the length of depths, and `hold`
gives a number below sent, which the read's source excludes. At an origin `sent r'` the field
`senders` gives that `depthAt J r'` is `some`, and `sentBefore_inj` gives r = r'. `opens_tr`:
recursion on the list of the later stages, unfolding `openedTr` and `qNext`, `openAt`, `oNext`
(Johnson/LinkSim/AtText/ShiftDefs.lean). `reads_plan`: recursion on the two lists, unfolding
`readsOf` and `planOpens`. `sentBefore_lt`: unfolding `sentBefore`.

Hypotheses of `own_reads_tr`. F: `OpensFit J decls depths src₀ sent`. hst: the stages are s :: rest:
one stage or more. `hold`: for every k below the length of depths, if `srcOf chain (src₀ k)` is
(chain, n), then n < sent. hD: entry n of Rs is `D n`. hr: `depthAt J r` is `some`. The lists decls,
depths and Rs, the functions src₀, stored, tree and D, and the numbers sent, chain and firstTree are
free parameters.

Limits.
- Of the test's own rounds alone: what a round outside the test reads of such a tree is not touched:
  that is the file's whole plan. The file there is not this Lean file: it is a proof file or key
  file as a description (`FileDescription`, Johnson/Desc/Block.lean) declares it, in three chains of
  rounds. Here decls is one list of rounds, and `readsOf` is taken at that list only.
- `OpensFit` is a hypothesis. It has a test with code, `opensFitB` (…/K12/OpensFitB.lean, which this
  file does not import); `opensFit_KR` there states `OpensFit` at every job whose place is
  `piKRFull`, the written place of the key file's test on the ranges, and whose `fresh` is not
  `none`, at the rounds of `proximityTestKind guardedProximityTestParts J.p` and at written values of depths, src₀ and sent. That
  file proves `OpensFit` at three values only: this one and two small made-up jobs (`opensFit_toy`,
  `opensFit_came`). At all three `J.fresh` is not `none`: the first fold's fresh table has come
  earlier. Where `J.fresh` is `none`, the first fold sends its own table; for that case the file has
  one `#guard` on `opensFitB` only, at the stages of `ToyTrees.p`: an evaluation by Lean's
  evaluator, outside the kernel, which leaves no theorem. So in that case no theorem there gives a
  value that meets F, though `own_reads_tr` is stated in both cases.
- `hold` is a hypothesis: no tree before the test has the number of a tree that the test sends. It
  is proved at no value in this file.
- sent is a free parameter: that it is the number of trees that the chain has sent before the test
  is not stated.
- Where `J.fresh` is `none` and there are two stages or more, `depthAt J 1` is `some`, by the
  definition of `depths` (Test.lean): the first fold sends its own table. `openedTr D rest s 1 0` is
  the empty list (`openedTr_zero`, Sim/CoreText.lean). So at r = 1 the statement says there that no
  read has that source; that its hypotheses can be met there is not shown. At the values of the one
  `#guard` of OpensFitB.lean in that case (the depths [5, 4, 4], the sources `own 0`, `own 1`,
  `own 2`, and 2 for sent) `hold` is false, by reading: `srcOf chain` of `own 2` is (chain, 2), and
  2 is not below sent.
- No property is claimed. Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactPlan
import Johnson.Desc.ProofFile.Honest.K12.ColsTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (qNext oNext openAt)

variable {W X : Type}

/-! ## 1 The term's openings and `openedTr` -/

/-- **Each opening in the term's list.** An opening in `opensFrom rest cur o fr` is either of a tree
in fr, at the stage's own reading round, or has the origin `sent r` with o ≤ r; then its positions,
each once, are `openedTr D rest cur o (r - o)`. -/
theorem opens_tr (D : ℕ → Fmt.Drawn) : ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage) (o : ℕ)
    (fr : List (ℕ × From)) (x : ℕ × ℕ × From), x ∈ opensFrom rest cur o fr →
    (∃ y ∈ fr, x = (if rest.isEmpty then o + 1 else o + 2 + ((sgOf cur).h + (sgOf cur).g), y.1,
      y.2)) ∨
    ∃ r, x.2.2 = .sent r ∧ o ≤ r ∧
      Fmt.listOf ((D x.1).poss.map (· % 2 ^ x.2.1)) = openedTr D rest cur o (r - o)
  | [], cur, o, fr, x, hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact Or.inl ⟨y, hy, rfl⟩
  | next :: rest, cur, o, fr, x, hx => by
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
      exact Or.inl ⟨y, hy, rfl⟩
    · refine Or.inr ?_
      rcases opens_tr D rest next (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        [((sgOf next).C.a, .sent (o + 1 + ((sgOf cur).h + (sgOf cur).g)))] x h with
        ⟨y, hy, rfl⟩ | ⟨r, hr, hle, he⟩
      · obtain rfl := List.mem_singleton.1 hy
        refine ⟨o + 1 + ((sgOf cur).h + (sgOf cur).g), rfl, by omega, ?_⟩
        have e : o + 1 + ((sgOf cur).h + (sgOf cur).g) - o = 1 + ((sgOf cur).h + (sgOf cur).g) := by
          omega
        rw [e]
        have hT : openedTr D (next :: rest) cur o (1 + ((sgOf cur).h + (sgOf cur).g)) =
            Fmt.listOf (qNext rest.isEmpty cur next o D) := by
          conv_lhs => unfold openedTr
          rw [if_neg (Nat.lt_irrefl _), if_pos rfl]
        rw [hT]
        unfold qNext openAt oNext
        cases rest with
        | nil => rfl
        | cons _ _ => rfl
      · refine ⟨r, hr, by omega, ?_⟩
        rw [he]
        conv_rhs => unfold openedTr
        rw [if_neg (by omega), if_neg (by omega)]
        unfold oNext
        congr 1
        omega

/-! ## 2 The frame's reads and the declared openings -/

/-- A read of declared rounds that read no stored table is a read of a declared opening: it has that
opening's source, by `srcOf chain`, and its position is among the opening's. i: the first round's
number. Entry n of Rs is `D (i + n)`. -/
theorem reads_plan (chain firstTree : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) (D : ℕ → Fmt.Drawn) :
    ∀ (decls : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (i : ℕ),
      (∀ d ∈ decls, d.stored = []) → (∀ n (h : n < Rs.length), Rs[n] = D (i + n)) →
      ∀ q ∈ readsOf chain firstTree stored tree decls Rs, ∃ x ∈ planOpens decls i,
        q.src = some (srcOf chain x.2.2) ∧ q.pos ∈ Fmt.listOf ((D x.1).poss.map (· % 2 ^ x.2.1))
  | [], _, _, _, _, q, hq => by
    unfold readsOf at hq
    cases hq
  | _ :: _, [], _, _, _, q, hq => by
    unfold readsOf at hq
    cases hq
  | d :: ds, R :: Rs, i, hs, hD, q, hq => by
    unfold readsOf at hq
    rw [hs d (by simp), List.flatMap_nil, List.nil_append] at hq
    rcases List.mem_append.1 hq with h | h
    · obtain ⟨o, ho, h⟩ := List.mem_flatMap.1 h
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      refine ⟨(i, o.1.a, o.2), ?_, rfl, ?_⟩
      · unfold planOpens
        exact List.mem_append_left _ (List.mem_map.2 ⟨o, ho, rfl⟩)
      · have e : R = D i := by
          have := hD 0 (by simp)
          simpa using this
        rw [← e]
        exact hx
    · obtain ⟨x, hx, h1, h2⟩ := reads_plan chain firstTree stored tree D ds Rs (i + 1)
        (fun d' hd' => hs d' (by simp [hd'])) (fun n hn => by
          have := hD (n + 1) (by simpa using hn)
          rw [List.getElem_cons_succ] at this
          rw [this]
          congr 1
          omega) q h
      refine ⟨x, ?_, h1, h2⟩
      unfold planOpens
      exact List.mem_append_right _ hx

/-! ## 3 The numbers of the trees that the test sends -/

/-- After a round that sends a tree, at least one tree more has been sent: if `depthAt J r` is
`some` and r < r', then `sentBefore J r < sentBefore J r'`. -/
theorem sentBefore_lt (J : TestJob W X) (r r' : ℕ) (h : (depthAt J r).isSome = true)
    (hlt : r < r') : sentBefore J r < sentBefore J r' := by
  unfold sentBefore
  obtain ⟨d, rfl⟩ : ∃ d, r' = r + 1 + d := ⟨r' - (r + 1), by omega⟩
  rw [List.range_add, List.filter_append, List.length_append, List.range_succ, List.filter_append,
    List.length_append]
  simp [h]
  omega

theorem sentBefore_inj (J : TestJob W X) (r r' : ℕ) (h : (depthAt J r).isSome = true)
    (h' : (depthAt J r').isSome = true) (e : sentBefore J r = sentBefore J r') : r = r' := by
  rcases Nat.lt_trichotomy r r' with hl | he | hg
  · have := sentBefore_lt J r r' h hl
    omega
  · exact he
  · have := sentBefore_lt J r' r h' hg
    omega

/-! ## 4 The statement -/

/-- **What the test's own rounds read of the tree that its round r sends.** A read whose source is
the chain's tree number `sent + sentBefore J r` has its position in `openedTr D rest s 1 (r - 1)`.
sent: meant for the number of trees that the chain has sent before the test; a free parameter. Rs:
the test's challenges: entry n is `D n`. `hold`: a tree of the job whose source is in this chain has
a number below sent. -/
theorem own_reads_tr (J : TestJob W X) (decls : List Fmt.DeclaredRound) (depths : List ℕ)
    (src₀ : ℕ → Fmt.TreeSource) (sent chain firstTree : ℕ) (F : OpensFit J decls depths src₀ sent)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest)
    (hold : ∀ k, k < depths.length → ∀ n, srcOf chain (src₀ k) = (chain, n) → n < sent)
    (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) (D : ℕ → Fmt.Drawn)
    (Rs : List Fmt.Drawn) (hD : ∀ n (h : n < Rs.length), Rs[n] = D n) (r : ℕ)
    (hr : (depthAt J r).isSome = true) :
    ∀ q ∈ readsOf chain firstTree stored tree decls Rs,
      q.src = some (chain, sent + sentBefore J r) → q.pos ∈ openedTr D rest s 1 (r - 1) := by
  intro q hq hsrc
  obtain ⟨x', hx', h1, h2⟩ := reads_plan chain firstTree stored tree D decls Rs 0 F.stored
    (fun n hn => by rw [Nat.zero_add]; exact hD n hn) q hq
  rw [F.opens] at hx'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
  rw [hsrc] at h1
  have h1' : (chain, sent + sentBefore J r) = srcOf chain (srcBy J src₀ sent x.2.2) :=
    Option.some.inj h1
  have hx0 := hx
  unfold opensTest at hx
  rw [hst] at hx
  rcases opens_tr D rest s 1 (frontTrees depths) x hx with ⟨y, hy, rfl⟩ | ⟨r', hr', hle, he⟩
  · -- a tree of the job: its number is below sent
    exfalso
    unfold frontTrees at hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have hk := (F.olds _ hx0 z.2 rfl).1
    have := hold z.2 hk _ h1'.symm
    omega
  · rw [hr'] at h1'
    have e : sent + sentBefore J r = sent + sentBefore J r' := congrArg Prod.snd h1'
    have hs' := (F.senders x hx0 r' hr').2
    obtain rfl := sentBefore_inj J r r' hr hs' (by omega)
    rw [← he]
    exact h2

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.opens_tr
#print axioms ProofFile.Honest.K12.reads_plan
#print axioms ProofFile.Honest.K12.sentBefore_lt
#print axioms ProofFile.Honest.K12.sentBefore_inj
#print axioms ProofFile.Honest.K12.own_reads_tr
