-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/SwitchInShape.lean: the structure `SwitchIn`
(Johnson/Prover/Link/FormBehindAny.lean) is proved at the first stage of a proximity test, at the
state after the first fold, where the first fold's fresh table has come earlier. `SwitchIn` is the
hypothesis of `formInv_any` (same file) on the state before a code switch; `formInv_any` says, under
further hypotheses: after an accepted switch and the batching after it, the form's half of the
invariant (`FormInv`) holds at the next stage, whatever trees the old rows were in. The state here
is `t1At` (Johnson/Desc/K12/Honest/FirstYes.lean): what the fold's decision returns at the fold's
rounds `rfAt` of the term. The term is `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean): all that a
prover shows in the stages of a proximity test, as one term. The hypotheses are those of
`first_of_shape` (FirstTerm.lean in this folder) and one more, on sampled positions. Of the
structure's nine clauses eight are derived from them, at the written state after the fold (`foldT`,
Johnson/Prover/Link/FormFold.lean): what is passed (`pass`) · the group that the fold has opened
(`group`) · "in order" (`order`) · the count of roots (`roots`) · `FoldedFit` (`ff`) ·
`DenseForm` (`dense`) · the form's shape (`cfits`) · `OldIn` (`old`). The ninth, the
positions' range (`range`), is a clause of the hypothesis `TermAsks` (FirstTerm.lean) and is passed
on. Every variable of the three theorems is a free parameter. Statements and proofs. It depends on
no frame for an honest side.

In the list: p is the place of the test (`P12`, Johnson/Desc/K12/Frame.lean: the numbers of a place
at which a proximity test is). a and next are the first two stages, n is next as the program names
it (`IoppStage`), and i is the pair of the first stage's code numbers. t₀ is the state before the
test: a value of the type of the verifier's state inside a test (`T12`, Johnson/Desc/K12/Join.lean),
with its statement `st`, its book `book` (`TreeBook`, OnBytes/Iop/Ground.lean: the trees sent so
far, and each oracle message's place in them) and its count of roots `roots`. `tBat p t₀ dB`
(FirstTerm.lean) is the state after the batching, where dB is what the round "BAT" sampled. D gives
what each later round sampled, and o is the number of the first stage's first round. P is a prover's
state (`PS`, Johnson/Prover/Link/BodyState.lean), K a parameter of the term (`BCoins`,
Johnson/Prover/Link/BodyAll.lean), c the columns. The door is the test's beginning: the front, the
batching, the question whether the group fits the first stage, and the first fold (TestDoor.lean in
this folder). The shape of a state is `testSh` (Test.lean in this folder): numbers, flags and lists;
its types hold no field element.

  `switchIn_shape`: the premises of `first_of_shape` (FirstTerm.lean in this folder) ⟹ `SwitchIn` at
    the term's state behind the first fold, at the group number "as many as the statement behind the
    batching has groups"; and that state's statement is the one behind the batching with the mask
    spent and one group more. Here "behind" means after. The theorem has one hypothesis more than
    `first_of_shape`: `hrC` below. The stage's number is 0. The single rows of `SwitchIn` are under
    "∃". In Lean the statement after the fold is `Ground.withGroup (spent S id) n.code n.maskCode`,
    where S is the statement of `tBat p t₀ dB` and `spent S id` (FormFold.lean) sets the flag
    `spentAsMask` of message number id
  `door_facts`: under `h`, `hm`, `ht`, `hpl`, `hv`, `hB` and `fB` below, at any pair nn in place of
    the next stage's code numbers, there are a group G, a row and an element x such that:
    `TestFront` (Johnson/Prover/Link/FormFirst.lean: the library's facts on the state before a test)
    holds at t₀ and G; `Bat.combine` at x returns the row, which is the batched row; `tBat p t₀ dB`
    is the written state `batT t₀ G row` (FormFirst.lean); and `p.nums.free = t₀.roots`: the count
    of roots is the place's. Nothing more is stated of x: not that it is the element that "BAT"
    sampled
  `oldIn_of_pub`: `ReadPub` (Johnson/Desc/K12/Honest/ReadPub.lean) gives `OldIn`
    (Johnson/Prover/Link/FormBehindRead.lean): the old rows' oracle messages are the statement's,
    and their places lie in trees of the book. At every statement, book, single rows, range, list of
    places and family of trees

By what. `oldIn_of_pub`: the fields `placed`, `oracle` and `tree` of `ReadPub`, and `array_mapM_inv`
(OnBytes/Slice/BlkOpenN.lean). `door_facts`: `testFront_of`, `batOwes_of` and `frontOwes_of`
(TestDoor.lean), and `bat5_yes` (Johnson/Prover/Link/FormBatLaws.lean). `switchIn_shape`:
`door_facts`; `foldFront_first` (FormFirst.lean) and `fold5_yes`
(Johnson/Prover/Link/FormFoldLaws.lean) give that `t1At` is `foldT`; then `order` by `inOrder_foldT`
(Johnson/Prover/Link/FormNextLaws.lean), `roots` by `door_facts`, `ff` by `foldedFit_pure`
(Johnson/Desc/K12/Law/FoldKeeps.lean), `dense` by `combine_dense` and `denseForm_foldOutput`
(OnBytes/Slice/BlkProxDense.lean), `cfits` by `cfits_foldOutput`
(Johnson/Prover/Link/FixEntries.lean), `old` by `readPub_sh` (ReadShape.lean in this folder) and
`oldIn_of_pub`; `pass`, `group` and the statement's equation come from the text of `foldT`.

Hypotheses of `switchIn_shape`.
- `h`: `doorB` (TestDoor.lean) is true at the shape of t₀, at the batching's declared round and at
  the two stages' code numbers
- `hm`: the field `mask` of t₀ is `some id`: this is the case "the fresh table has come earlier"
- `ht`: `stTidyB` (Johnson/Desc/Ground/Shape/Marks.lean) is true at the statement of t₀
- `hpl`: each row that the test takes in from the group under test (`runRows`) is a `PlainRow`
  (OnBytes/Slice/BlkPlain.lean): it has no written-out factor
- `hv`: `claimsB` (TestDoor.lean) is true at t₀: a test on the rows that lie open on that group
- `Pl`: `SwitchPub` (TestSwitch.lean in this folder) at the codes of t₀: the plan, the codes and the
  switch's two declared rounds dS and dC
- `hB`, `hF`: the declared rounds that are cut for the batching and for the first fold pass `batCut`
  (Johnson/Prover/Link/FormBat.lean) and `foldCut` (FormFold.lean)
- `fB`: what "BAT" sampled has the declared form (`roundsFit`, Johnson/Desc/Block.lean)
- `A`: `TermAsks` at `tBat p t₀ dB`. The proof uses its clauses `fitF`, `pub` and `range`
- `hrC`: the round rC, at which `SwitchIn` is stated, sampled the positions that D gives for round
  number o + 2 + (h + g), the switch's second round; h and g are those of `sgOf a`

Limits.
- Every hypothesis above is assumed. This file shows none of them at any place or state.
- t₀ is a free parameter: nothing here says that a verifier reaches this state in a run.
- None of the nine clauses is a hypothesis in its own form, but two come from clauses of `TermAsks`,
  which is a hypothesis: `range` is `TermAsks.range`, carried to rC by `hrC`; and `old` follows from
  `TermAsks.pub`, which is the test `readPubB` (ReadShape.lean) at the shape of the same state after
  the fold.
- "No clause on a value of the prover" is said of the hypotheses by their text; no theorem of this
  file states it. By type `TermAsks` takes P, K and c. Its clauses `fitF` and `fitS` read the term's
  rounds (`rfAt`, `rsAt`), and so the prover's state, though `roundsFit` tests of a sent item its
  sort only. Its clause `pub` is at the state after the fold, which by type depends on the term's
  rounds, and nothing here says that the shape after the fold is a function of the shape before it.
  Its clause `width` reads the lengths of the columns c.
- Not all hypotheses are tests on the shape: `ht`, `hpl` and `hv` take the state or its statement,
  not the shape, and `claimsB` reads field elements of the open rows.
- The case in which the first fold sends its own table is not served: the clause `roots` of
  `SwitchIn` is false there. By reading, and stated by no theorem of this file: at stage number 0
  the clause says that the state's count of roots is `p.nums.free`; `doorB` tests that the count
  before the test is `p.nums.free`; and the written state after such a fold (`foldTOwn`,
  Johnson/Desc/K12/Honest/OwnFold.lean) counts one root more.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.FirstTerm
import Johnson.Prover.Link.FormBehindAny

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.K12

/-- `ReadPub` gives `OldIn`: the old rows' oracle messages are messages of the statement S, and
their places lie in trees of the book B0. -/
theorem oldIn_of_pub {S : Statement} {B0 : TreeBook} {old : SingleRows} {logN : ℕ}
    {places : Array (ℕ × ℕ)} {TT : ℕ → OnBytes.Tree} (Pb : ReadPub S B0 old logN places TT) :
    OldIn S B0 old := by
  obtain ⟨z1, z2⟩ := array_mapM_inv _ _ _ Pb.placed
  refine ⟨fun o ho => ?_, fun o ho pl hpl => ?_⟩
  · obtain ⟨x, hx⟩ := Pb.oracle o (Array.mem_toList_iff.2 ho)
    exact lt_of_some hx
  · obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem ho
    have e := z2 k hk
    have hk' : k < places.size := by rw [z1]; exact hk
    have e2 : places[k]? = some places[k] := Array.getElem?_eq_getElem hk'
    rw [hpl, e2] at e
    obtain rfl := Option.some.inj e
    have hm : (places[k]).1 ∈ treesAt places := by
      unfold treesAt
      rw [listOfT_eq, Fmt.listOf_mem, Array.toList_map]
      exact List.mem_map.2 ⟨_, Array.mem_toList_iff.2 (Array.getElem_mem hk'), rfl⟩
    exact lt_of_some (Pb.tree _ hm).there

/-- What the door's tests give, where the fresh table has come earlier. G: the group under test.
row: the batched row. x: the element at which `Bat.combine` returns that row. -/
theorem door_facts {p : P12} {a next : Fmt.M1.Stage} {t₀ : T12} {i nn : ℕ × ℕ} {id : ℕ}
    {dB : Fmt.Drawn}
    (h : doorB p a next (((laidOf p).take 1).map (·.1)) i nn (testSh t₀) = true)
    (hm : t₀.mask = some id) (ht : stTidyB t₀.st = true)
    (hpl : ∀ G, t₀.st.groups[t₀.g]? = some G → ∀ r ∈ (runRows t₀.st G).toList, PlainRow r)
    (hv : claimsB t₀ = true) (hB : batCut (((laidOf p).take 1).map (·.1)) = true)
    (fB : roundsFit (((laidOf p).take 1).map (·.1)) [⟨[], dB⟩] = true) :
    ∃ G row x, TestFront p a next t₀ G i nn id ∧
      Bat.combine (begun t₀.st t₀.g G) t₀.g ⟨Means.layoutOf t₀.st G, runRows t₀.st G⟩ x =
        some row ∧
      tBat p t₀ dB = batT t₀ G row ∧ p.nums.free = t₀.roots := by
  unfold doorB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h4' : (match t₀.mask with
    | some id => cameB a (testSh t₀).core t₀.g i id
    | none => (testSh t₀).core.st.oracles.length == (testSh t₀).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := ProofFile.Honest.Sh.testFront_of h1 hm h4' ht hpl
  obtain ⟨row, hr, hb⟩ := bat5_yes H _ (batOwes_of h2 H.group) hB [⟨[], dB⟩] fB
  exact ⟨G, row, _, H, hr, getD_of_ok hb, (frontOwes_of h3 hv H.group).roots⟩

/-- **`SwitchIn` at the first stage, under the hypotheses of `first_of_shape` and `hrC`.** The state
is the term's state after the first fold (`t1At`). rC: the round whose sampled positions the clause
`range` of `SwitchIn` speaks of. -/
theorem switchIn_shape (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (o : ℕ) (t₀ : T12) (P : PS) (D : ℕ → Fmt.Drawn) (dB : Fmt.Drawn) (Dp : Plain)
    (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage) (id : ℕ) (dS dC : Fmt.DeclaredRound)
    (h : doorB p a next (((laidOf p).take 1).map (·.1)) i (n.code, n.maskCode) (testSh t₀) = true)
    (hm : t₀.mask = some id) (ht : stTidyB t₀.st = true)
    (hpl : ∀ G, t₀.st.groups[t₀.g]? = some G → ∀ r ∈ (runRows t₀.st G).toList, PlainRow r)
    (hv : claimsB t₀ = true)
    (Pl : SwitchPub p t₀.st.codes 0 a next rest.isEmpty ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf p).take 1).map (·.1)) = true)
    (hF : foldCut a.k (((laidS p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf p).take 1).map (·.1)) [⟨[], dB⟩] = true)
    (A : TermAsks p K rest a next o (tBat p t₀ dB) P D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC)
    (rC : Fmt.RoundView) (hrC : rC.drawn.poss = (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss) :
    ∃ rows, SwitchIn p 0 a next n (tBat p t₀ dB).st.groups.size
        (t1At p K 0 a (laidS p) o (tBat p t₀ dB) P D) rows rC ∧
      (t1At p K 0 a (laidS p) o (tBat p t₀ dB) P D).st =
        Ground.withGroup (spent (tBat p t₀ dB).st id) n.code n.maskCode := by
  obtain ⟨G, row, x, H, hr, eB, hroots⟩ := door_facts h hm ht hpl hv hB fB
  rw [eB] at A ⊢
  have F := foldFront_first H x row hr
  have hfold := fold5_yes F hF (rfAt K 0 a o (batT t₀ G row) P D) A.fitF
  have e1 : t1At p K 0 a (laidS p) o (batT t₀ G row) P D = _ := getD_of_ok hfold
  obtain ⟨rE, rR, hrs, hR⟩ := rounds_split (length_of_foldCut hF) A.fitF
  obtain ⟨places, Pb⟩ := readPub_sh (A.pub _ _ (by rw [e1]; rfl))
  rw [e1] at Pb ⊢
  rw [hrs] at Pb ⊢
  have hcodes : (batT t₀ G row).st.codes = t₀.st.codes := batT_codes t₀ G row
  have hrow : foldRowOk (spent (batT t₀ G row).st id)
      (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)) row = true :=
    (Own.foldRowFits_agrees _ _ _).trans ((foldRowFits_spent _ _ _ _).trans F.rowFits)
  have hlen : (rR.map drawnOf).length = a.k := by rw [List.length_map]; exact hR
  have hplain : DenseForm row.c := combine_dense _ _ _ _ _ H.dense hr
  obtain ⟨cd, hcd, ecd⟩ := Pl.codes.base
  refine ⟨_, ⟨rfl, ?_,
    inOrder_foldT _ row _ _ _ id _ (H.order.begun t₀.g G H.group), hroots.symm, ?_,
    denseForm_foldOutput _ _ row id _ _ _ hplain, ?_, by rw [hrC]; exact A.range,
    oldIn_of_pub Pb⟩, rfl⟩
  · show ((batT t₀ G row).st.groups.push _)[(batT t₀ G row).st.groups.size]? = _
    rw [Array.getElem?_push_size]
  · have Pl' : SwitchPub p (batT t₀ G row).st.codes 0 a next rest.isEmpty ⟨i.1, i.2, a.k, a.h⟩ n dS
        dC := by
      rw [hcodes]
      exact Pl
    exact foldedFit_pure (batT t₀ G row).st.codes (sgOf a) (sgOf next) ⟨i.1, i.2, a.k, a.h⟩
      Pl'.codes n.code n.maskCode Pl'.zk Pl'.codeN Pl'.zkN Pl'.small (batT t₀ G row).st
      (spent (batT t₀ G row).st id) row (Means.layoutOf t₀.st G) id (drawnOf rE)
      (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)) (rR.map drawnOf) rfl
      rfl
      (H2K.Pin.combine_noKept0 _ _ _ _ _ hr fun k => H.noKept k) (fun k _ => H.noKept k)
      (hlen.trans Pl.codes.k) ((Own.foldShapeFits_agrees _ _).trans F.shape) hrow
  · have h1 := cfits_foldOutput (spent (batT t₀ G row).st id)
      (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)) row id (drawnOf rE)
      (rR.map drawnOf) (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)) hlen
      hrow
    have e : ((spent (batT t₀ G row).st id).codes.base.getD
        (ioppFoldShape ⟨i.1, i.2, a.k, a.h⟩ (Means.layoutOf t₀.st G)).code default).ell =
        (sgOf a).C.l := by
      show ((batT t₀ G row).st.codes.base.getD i.1 default).ell = _
      rw [hcodes, Array.getD_eq_getD_getElem?, hcd]
      exact congrArg (·.l) ecd
    rw [e] at h1
    exact h1

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.oldIn_of_pub
#print axioms ProofFile.Honest.Sh.door_facts
#print axioms ProofFile.Honest.Sh.switchIn_shape
