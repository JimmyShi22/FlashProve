-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FirstAsks.lean: the hypotheses of `first_V`
(Johnson/Desc/K12/Honest/FirstValues.lean) as one structure, `FirstAsks`, and three small theorems
for callers that meet such hypotheses by a test. `first_V` is on the first stage of a proximity
test: if the claim before the first fold is true at the prover's state then, under further
hypotheses, the claim after the first switch is true at the prover's state after that switch. A test
is here a definition with values in `Bool` that has code. The theorems hold at every value of their
parameters. Johnson/Desc/ProofFile/Honest/K12/AllB.lean calls `groupTrees_colsFrom` and `fitAll_of`.
Definitions, theorems and proofs. It depends on no frame for an honest side: the frame
(Johnson/Desc/ProofFile/Honest/Frame.lean) is not among the imports, direct or indirect.

In the list: p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the place of the test. a
and next (`Fmt.M1.Stage`) are the first and the second stage, rest the stages after them. t (`T12`,
Johnson/Desc/K12/Join.lean) is the verifier's state before the first fold, P (`PS`,
Johnson/Prover/Link/BodyState.lean) the prover's state. K (`BCoins`,
Johnson/Prover/Link/BodyAll.lean), D and o are parameters of the rounds that `first_V` speaks of:
`D n` is what round number n samples, and o is the number of the stage's first round. A tree
(`Tree`, Johnson/Desc/K12/Honest/Stages.lean) is a pair: its depth, and its column function, which
gives the written column at a position. The book (`TreeBook`, OnBytes/Iop/Ground.lean) lists the
trees sent so far, and a tree's place in the book is its index in the field `trees`. `c u` is the
column function for the place u. R (`PlainRows`, Johnson/Desc/K12/Honest/FirstRows.lean) holds the
prover's rows as functions of numbers. Dp (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean) is the plain
data of the group under test, and `Dp.ts` lists the places of the group's trees.

  `firstAsks_of`: if `valuesB p K rest a next o t P D c R`
    (Johnson/Desc/K12/Honest/FirstValuesTest.lean) is true, there are row, L, Dp, cu and nx at which
    `FirstAsks` holds
  `groupTrees_colsFrom`: under the two hypotheses below, the group's trees made of `colsFrom`, that
    is `groupTrees ts log (colsFrom trees ts)` (Johnson/Desc/K12/Honest/GroupState.lean), are the
    list trees
  `fitAll_of`: if `fitAllB cur rest` is true, `FitAll cur rest` (Stages.lean) holds: along the list
    that begins with cur and goes on with rest, each stage fits the next (`CsFit`,
    OnBytes/Slice/CsData.lean)
  `FirstAsks`: a structure of propositions: all hypotheses of `first_V` at l := `laidS p`
    (Johnson/Desc/K12/Law/ReadsK.lean) but hl and hpk, field by field. hl is `l = laidS p`, which
    holds there by `rfl`. hpk is the packing's equation, `P.fM = packedN (sgOf a) (K.W (sgOf a) 0)`.
    The structure's docstring says which field is which hypothesis
  `colsFrom trees ts`: a definition: column functions by a tree's place in the book, from a list of
    trees that goes by the order of a list of places ts. For the place u it takes the tree at the
    index `ts.idxOf u` of trees: the index at which u first occurs in ts, or the length of ts where
    u is not in ts. Where trees has no entry at that index, every column is the empty list. The
    definition reads no book: ts is any list of numbers. AllB.lean calls it at `Dp.ts`
  `fitAllB cur rest`: a definition: `FitAll` as a test: `csFitB` (FirstValuesTest.lean) at each
    stage and the next

By what. `firstAsks_of` unfolds `valuesB` and `firstB` (Johnson/Desc/K12/Honest/FirstTest.lean) and
splits on the values that they match on. The tests' clauses become fields by `sized_of`, `colsAt_of`
and `firstYes_of` (FirstTest.lean), `stateAt_of` (Johnson/Desc/K12/Honest/FirstStateTest.lean), and
`csFit_of`, `holds_of` and `oldOk_of` (FirstValuesTest.lean). `groupTrees_colsFrom` compares the two
lists entry by entry, with `List.Nodup.idxOf_getElem`. `fitAll_of` goes by recursion on the list,
with `csFit_of`.

Hypotheses of `groupTrees_colsFrom`. hn: the places in ts are pairwise different (`List.Nodup`). hd:
the trees are as deep as log states at the places, one by one: `trees.map (·.1) = ts.map log`; so
the two lists are equally long.

Limits. Nothing is checked at a value here: no test is evaluated, and that `FirstAsks` holds is
shown at no arguments. No field of `FirstAsks` is shown here but from the "true" of `valuesB`; among
the fields are that the fold, the switch and the batching after it accept (in `yes`) and that the
claim before the first fold is true (`claim`). `FirstAsks` has no field for hpk: whoever calls
`first_V` from it has to show hpk separately. On a "true" of `valuesB` at a value: the limits of
FirstValuesTest.lean. `groupTrees_colsFrom` is a statement on lists: nothing on what the columns
hold. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.FirstValuesTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- The hypotheses of `first_V` (FirstValues.lean) at l := `laidS p`, without hl and hpk, in the
order of `first_V`. Each field, with the name of its hypothesis there: `early` (he), `one` (h1),
`pass` (hp), `plain` (hD), `good` (hok), `hk` (hhk), `hk'` (hhk'), `sized` (hs), `stage` (hcu),
`stage'` (hnx), `cols` (hC), `state` (hS), `yes` (Y), `range` (hr), `count` (ht), `fit` (hf), `layK`
(hLk), `layH` (hLh), `claim` (hin), `room` (hroom), `ell` (hZl), `old` (hOld), `words` (hwords). row
with the layout L is the claim that t passes. Dp is what `gpOf` returns. cu and nx are the two
stages in the program's form (`IoppStage`), as `stageAt` returns them. -/
structure FirstAsks (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (o : ℕ) (t : T12) (P : PS) (D : ℕ → Fmt.Drawn) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (row : GroupRow) (L : GroupLayout) (Dp : Plain) (cu nx : IoppStage) : Prop where
  early : p.early = true
  one : p.answers = 1
  pass : t.pass = .claim row L
  plain : gpOf p t a L = some Dp
  good : ok (gpL p a row Dp) = true
  hk : a.h ≤ a.k
  hk' : next.h ≤ next.k
  sized : (sg a).Sized
  stage : stageAt p 0 a = some cu
  stage' : stageAt p 1 next = some nx
  cols : ColsAt a Dp c R
  state : StateAt a Dp P R
  yes : FirstYes p K rest 0 a next (laidS p) o t P (groupTrees Dp.ts (logAt Dp.book) c) D
  range : ∀ x ∈ (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss, x < 2 ^ a.C.a
  count : (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss.length = a.t
  fit : CsFit (sgOf a) (sgOf next)
  layK : L.k = (sgOf a).h + (sgOf a).g
  layH : L.h = (sgOf a).h
  claim : (Slf.idf (E := GE) (J := (sgOf a).cIn.J)).Holds (stmGk (sgOf a) L.k L.h row)
    (μOf (sgOf a) P)
  room : (sgOf a).h + 2 * (sgOf a).g + 1 ≤ (sgOf a).Z.l
  ell : ((t1At p K 0 a (laidS p) o t P D).st.codes.mask.getD cu.maskCode default).ell = a.Z.l
  old : ∀ rows gp, (t1At p K 0 a (laidS p) o t P D).pass = .single rows gp →
    OldOk (sgOf a) (sgOf next) (t1At p K 0 a (laidS p) o t P D).st.codes rows nx.code nx.maskCode
  words : okE (((D (o + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple).getD
    (bitsAt p 0 next (t1At p K 0 a (laidS p) o t P D)) zeroE) = true

/-- **If `valuesB` is true, `FirstAsks` holds at some row, L, Dp, cu and nx.** -/
theorem firstAsks_of (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (o : ℕ) (t : T12) (P : PS) (D : ℕ → Fmt.Drawn) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hB : valuesB p K rest a next o t P D c R = true) :
    ∃ row L Dp cu nx, FirstAsks p K rest a next o t P D c R row L Dp cu nx := by
  unfold valuesB at hB
  rw [Bool.and_eq_true] at hB
  obtain ⟨hF, hB⟩ := hB
  unfold firstB at hF
  cases hp : t.pass with
  | claim row L =>
    cases hD : gpOf p t a L with
    | none => simp [hp, hD] at hF
    | some Dp =>
      cases hcu : stageAt p 0 a with
      | none => simp [hp, hcu] at hB
      | some cu =>
        cases hnx : stageAt p 1 next with
        | none => simp [hp, hcu, hnx] at hB
        | some nx =>
          cases h1p : (t1At p K 0 a (laidS p) o t P D).pass with
          | single rows gp =>
            simp only [hp, hD, hcu, hnx, Bool.and_eq_true, decide_eq_true_eq,
              List.all_eq_true] at hF
            simp only [hp, hD, hcu, hnx, h1p, Bool.and_eq_true, decide_eq_true_eq] at hB
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨he, h1⟩, hok⟩, hhk⟩, hs⟩, -⟩, -⟩, hC⟩, hY⟩, hr⟩, ht⟩ := hF
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hhk'⟩, hf⟩, hLk⟩, hLh⟩, hin⟩, hroom⟩, hZl⟩, hO⟩, hw⟩ := hB
            exact ⟨row, L, Dp, cu, nx, he, h1, hp, hD, hok, hhk, hhk', sized_of hs, hcu, hnx,
              colsAt_of hC, stateAt_of hS, firstYes_of _ _ _ _ _ _ _ _ _ _ _ _ hY, hr, ht,
              csFit_of hf, hLk, hLh, holds_of hin, hroom, hZl,
              fun rows' gp' h' => by
                rw [h1p] at h'
                injection h' with e1 _
                rw [← e1]
                exact oldOk_of hO, hw⟩
          | _ => simp [hp, hcu, hnx, h1p] at hB
  | _ => simp [hp] at hF

/-- Column functions by a tree's place in the book. For the place u: the column function of the tree
at the index `ts.idxOf u` of trees: where u first occurs in ts, or the length of ts where u is not
in ts. Where trees has no entry at that index, every column is the empty list. -/
def colsFrom (trees : List Tree) (ts : List ℕ) (u x : ℕ) : List UInt64 :=
  (trees.getD (ts.idxOf u) (0, fun _ => [])).2 x

/-- **The group's trees made of `colsFrom` are the list of trees.** hn: the places are pairwise
different. hd: the trees are as deep as log states at the places, one by one. -/
theorem groupTrees_colsFrom (trees : List Tree) (ts : List ℕ) (log : ℕ → ℕ) (hn : ts.Nodup)
    (hd : trees.map (·.1) = ts.map log) : groupTrees ts log (colsFrom trees ts) = trees := by
  have hlen : trees.length = ts.length := by
    have k := congrArg List.length hd
    simpa using k
  unfold groupTrees
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  have hi : i < ts.length := by simpa using h1
  rw [List.getElem_map]
  have e1 : log ts[i] = trees[i].1 := by
    have k : (trees.map (·.1))[i]'(by simpa using h2) = (ts.map log)[i]'(by simpa using hi) := by
      simp only [hd]
    simpa using k.symm
  have e2 : colsFrom trees ts ts[i] = trees[i].2 := by
    funext x
    unfold colsFrom
    rw [hn.idxOf_getElem i hi, List.getD_eq_getElem _ _ h2]
  rw [e1, e2]

/-- `FitAll` as a test: each stage fits the next, by `csFitB`. -/
def fitAllB : Fmt.M1.Stage → List Fmt.M1.Stage → Bool
  | _, [] => true
  | cur, next :: rest => csFitB (sgOf cur) (sgOf next) && fitAllB next rest

theorem fitAll_of : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage), fitAllB cur rest = true →
    FitAll cur rest
  | _, [], _ => trivial
  | cur, next :: rest, h => by
    rw [fitAllB, Bool.and_eq_true] at h
    exact ⟨csFit_of h.1, fitAll_of next rest h.2⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.firstAsks_of
#print axioms ProofFile.Honest.K12.groupTrees_colsFrom
#print axioms ProofFile.Honest.K12.fitAll_of
#print axioms ProofFile.Honest.K12.FirstAsks
#print axioms ProofFile.Honest.K12.colsFrom
#print axioms ProofFile.Honest.K12.fitAllB
