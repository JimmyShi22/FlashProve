-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestSwitch.lean: the first stage of a proximity test accepts, in
whatever trees the members of the group under test are placed. The front, the batching, the frame's
question, the first fold, the first switch, the batching after it and the frame's question after
that, all of the description's own block (`guardedProximityTestParts`, Johnson/Desc/K12/JoinGuarded.lean), accept in a
row, and the structures between them are written out. This is proved from one Bool on the shape of
the structure before the test (`doorB`, Johnson/Desc/K12/Honest/Shape/TestDoor.lean) and the
hypotheses that are listed below; one of them, `ReadsAny`, is that the switch's reading of the old
rows accepts. Both cases of the first fold's mask. No prover, no coin, no frame for an honest side.
Definitions and theorems, general in the plan, the stages, the declared rounds, the rounds of the
view and the structure before the test.

Why. `switchFacts_of` (Johnson/Prover/Link/FormSwitchFacts.lean) and `behind_paid`
(Johnson/Prover/Link/FormBehind.lean) prove `SwitchFacts` and `BehindFront`
(Johnson/Prover/Link/FormSwitch.lean): the clauses that a switch and the batching after it ask. One
hypothesis of `switchFacts_of` is tied to old rows in one tree: that this tree can be read
(`ReadFront`, Johnson/Prover/Link/ReadFront.lean). A test's first stage may read a group whose
members are in several trees.

Terms. The structure inside a test is `T12` (Johnson/Desc/K12/Join.lean): the statement `st`; the
book of trees `book` (`TreeBook`: the trees, and each oracle message's place in a tree); the count
of roots; the number `g` of the group under test; what passes from a part to the next (`pass`); and
`mask`, the number of the oracle message that holds the present stage's mask, if it has come. Its
shape is `testSh t` (`TestSh`, Johnson/Desc/K12/Honest/Shape/Test.lean). A group (`Group`) has
members: oracle messages, by their numbers; a member "stands in" the tree in which the book places
it. The parts are fields of `guardedProximityTestParts`: `front`, `bat` (the batching), `fold`, `switch`, `batBehind`
(the batching after a switch). A part (`Part`, Johnson/Desc/K12/Frame.lean) accepts where its
`decide` returns `.ok` with the next structure. The frame is the proximity test's own (`proximityTestKind`,
`stagesFrom`, same file): it puts the parts in order, cuts the declared rounds among them, and asks
two questions of the structure: after the first batching, whether the group is the first stage's
(`firstFits`); after each stage but the last, where `p.early` is true, whether the next mask has
come (`maskCame`). The frame for an honest side is another:
Johnson/Desc/ProofFile/Honest/Frame.lean. The door is the word of TestDoor.lean for the front, the
batching, the first question and the first fold. The plan is p (`P12`: the numbers of the place of
the test), with the codes K. A stage is given twice: as cur, nxt or next (`Fmt.M1.Stage`: its
numbers) and as c or n (`IoppStage`: its two codes by their numbers in K, with k and h). dS and dC
are the switch's two declared rounds; rS and rC are these rounds in a view: the round of the seed
and the round of the positions. The old rows are the single rows (`SingleRows`) that the fold
returns and that the switch reads at the listed positions (`Tw.L9.readOld`,
Johnson/Top/H0/Tw/L9/Switch.lean). A letter is a parameter of a statement; the switch's letters are
the fields of D (`Taken`, Johnson/Desc/K12/Law/SwDid.lean): what a switch has taken of its two
rounds and has made on its way. "In front of" and "behind" mean before and after in the order of the
parts; "asked" introduces hypotheses.

  `first_stage_of_shape`: in the case `t.mask = some id`, under the hypotheses below, there are the
    group G under test and the row that the batching makes of the rows that the test takes in
    (`Bat.combine`, at the element that the batching's round drew) such that: the front returns t;
    the batching returns `batT t G row`; the first question is true there; the fold of stage number
    0 returns `foldT` at `batT t G row`; and `SwitchDone` holds at that structure and at the single
    rows `foldOut`
  `first_stage_of_shape_own`: the same in the case `t.mask = none`, with `foldCutOwn` for `foldCut`,
    `foldTOwn` for `foldT`, and `foldOut` at `enteredT` (Johnson/Desc/K12/Honest/OwnFold.lean)
  `SwitchDone`: what a switch and its batching have delivered: the two accepts; the next mask has
    come; the library's own structure of a switch (`Did`); "in order" behind; the letters' answer,
    rounds and group; what is public of the old rows (`FoldedFit`, `CFits`, `DenseForm`). A
    definition. In Lean: there are D, an element x, a row row', a book B and a layout lay such that:
    B is bk of the book after the sending (the field `book` of `swIn`); lay is `Own.layoutOf` at the
    group with its new member; `guardedProximityTestParts.switch` returns `switchT` at the rounds [rS, rC] and the
    columns gs; `guardedProximityTestParts.batBehind` returns `behindT` there; the field `mask` of `behindT` is
    `some (t.st.oracles.size + 1)`; the second question is true; `Did` holds at D; the statement of
    `behindT` is in order (`Means.InOrder`); `D.alpha` is `E.ofTriple a`, `D.rS` is rS, `D.rC` is
    rC, and `D.G` is the group with the two codes of n and no member; and the three propositions
    hold of the old rows
  `switch_any`: `SwitchDone` at a structure t whose `pass` is `.single` of what a fold returns of a
    batched row (`foldOutput`), under `SwitchPub` at the codes of t, `ReadsAny`, and hypotheses on
    t, on the batched row and on the two rounds
  `switch_behind_fold`: the same at `foldT`, the structure after a fold whose `FoldFront`
    (Johnson/Prover/Link/FormFold.lean) holds, with any m in the field `mask`
  `first_switch_came`, `first_switch_own`: the same at stage number 0, after the first fold, under
    the hypotheses of the theorems on the door: `TestFront` (Johnson/Prover/Link/FormFirst.lean), or
    `TestFrontOwn` (Johnson/Desc/K12/Honest/OwnFoldFirst.lean)
  `switchFacts_any`: `SwitchFacts` holds at some D and x. It is `switchFacts_of` with one hypothesis
    changed: in place of `ReadFront` at one old tree, that the reading itself returns `.ok` at every
    D. Its proof calls the same lemmas in the same order
  `SwitchPub`: a structure of propositions: what is public at a switch: the plan, the codes, the two
    declared rounds; no clause on a tree of the old rows. Two of its clauses are `p.early = true`
    and `p.answers = 1`
  `switchPub_of_step`: `StepPlan` (Johnson/Prover/Link/FormStepPlan.lean), the plan at a step whose
    round of the positions opens one tree (`opensC`), gives `SwitchPub`
  `ReadsAny`: a definition: at every D there are symbols y such that `Tw.L9.readOld` at `swIn` and
    at the positions of rC returns `.ok` with y, with no column left, and with the book bk of the
    book after the sending: one function bk for all D
  `read_size`: where `Tw.L9.readOld` returns `.ok` and `i.old.masks ≤ 2`, it returns as many symbols
    as listed positions times rows
  `batT_codes`, `batT_step`: `batT t G row` has the codes of t; if t has as many oracle messages as
    its book has places, so has `batT t G row`
  `withOwn_sent`: `withOwn S F` (OwnFold.lean) is `stSent S #[foldMaskNotice F]`
  `rounds_split`: rounds of a declared form of 1 + k rounds, without their digests (`noDigest`), are
    a first round and k more
  `length_of_foldCutOwn`: a list of declared rounds that passes `foldCutOwn k` has 1 + k rounds

By what. The two theorems on the first stage call the two on the first switch; these call
`switch_behind_fold`, which calls `switch_any`, which calls `switchFacts_any`. Beyond that:
`read_size`: `readOld_inv` (Johnson/Desc/K12/Law/SwRead.lean) and `singleRowsSymbols_inv`
(OnBytes/Iop/SymbolLaws.lean). `switchFacts_any`: the lemmas of
Johnson/Prover/Link/FormSwitchPay.lean, `switchCut_says`, `fit_says` and `swNotices_eq`
(FormSwitchLaws.lean), `nz_says` (FormSwitchFacts.lean) and `addOk_of` (SwitchSeat.lean), all in
that folder; where `switchFacts_of` calls `read_yes` (ReadYes.lean), it takes the hypothesis and
`read_size`. `switch_any`: `foldedFit_pure` (Johnson/Desc/K12/Law/FoldKeeps.lean),
`cfits_foldOutput` (Johnson/Prover/Link/FixEntries.lean), `denseForm_foldOutput`
(OnBytes/Slice/BlkProxDense.lean), `switchFacts_any`, `behind_paid`, `did_mask`
(Johnson/Desc/K12/Law/SwTies.lean), and `switch5_yes`, `behind5_yes`, `front_of_facts`
(FormSwitchLaws.lean). `switch_behind_fold`: `step_foldT`, `inOrder_foldT`
(Johnson/Prover/Link/FormNextLaws.lean), `foldRowFits_spent` (FormFoldLaws.lean, same folder),
`foldShapeFits_agrees`, `foldRowFits_agrees` (Johnson/Desc/Own/FoldAgree.lean). The two on the first
switch: `foldFront_first` (FormFirst.lean), `foldFrontOwn_first` (OwnFoldFirst.lean),
`front_entered` (Johnson/Desc/K12/Honest/OwnFoldLaws.lean), `combine_noKept0`
(Johnson/Desc/K12/Law/BatNoKept.lean), `combine_dense`, `denseRow_of_plain` (BlkProxDense.lean),
`InOrder.begun`, `InOrder.stSent` (Johnson/Desc/Means/Order.lean). The two on the first stage:
`testFront_of`, `testFrontOwn_of`, `batOwes_of`, `frontOwes_of` (TestDoor.lean); `bat5_yes`,
`group_batT` (Johnson/Prover/Link/FormBatLaws.lean), `front5_yes` (FormDoorLaws.lean), `fold5_yes`
(FormFoldLaws.lean), `length_of_foldCut` (FoldCutLen.lean), all in that folder; `door_yes_own`
(Johnson/Desc/K12/Honest/OwnFoldDoor.lean); `front_in_step` (Johnson/Desc/K12/SeatLaws.lean).
`batT_codes`: `closeLedgers_codes` (OnBytes/Slice/BlkStLaws.lean). `batT_step`: `begun_sizes`
(OnBytes/Slice/BlkProxKeeps.lean). `rounds_split`: `roundsFit_len` (Johnson/Desc/Sound/Gather.lean).
`length_of_foldCutOwn`: `foldCutOwn_of` (OwnFoldLaws.lean).

Hypotheses of `first_stage_of_shape` and `first_stage_of_shape_own`, next to h, the Bool `doorB` at
the shape of t, and hm, the case.
- The door's four (the head of TestDoor.lean says what each reads). ht: the first mark, `stTidyB`
  (Johnson/Desc/Ground/Shape/Marks.lean). hp: the rows that the test takes in are plain
  (`PlainRow`). hv: the front's named test on the open rows, `claimsB`. hB, hF, fB, fF: the
  batching's and the fold's declared rounds pass the tests on the plan's cuts (`batCut`; `foldCut`
  or `foldCutOwn`), and their rounds are of the declared form (`roundsFit`).
- Pl: `SwitchPub`: a proposition on plan and codes. A test with code that gives it: `switchPubB`,
  Johnson/Desc/K12/Honest/Shape/TestSwitchPub.lean.
- The view's form: the two rounds are of the declared form; the round of the positions shows one
  answer (the letter a names it). In Lean: hfit, hans. That the drawn factor is not 0 follows from
  the format's own test on draws that are never 0 (`nz_says`). The switch's part is applied to its
  two rounds as they are, the batching's and the fold's parts to theirs without the digests
  (`noDigest`).
- hread: `ReadsAny` at the structure and the single rows after the first fold, for the group under
  test and the row that the batching makes.

Limits.
- The first stage only: nothing on a later stage or on the base case.
- The rows that the test takes in are plain: of a test that takes in a row with a written-out factor
  these theorems say nothing.
- Of the old rows' form `SwitchDone` gives `DenseForm` (OnBytes/Slice/BlkProxDense.lean), which
  allows written-out factors. It is less than `PlainForm` (`denseForm_of_plain`, same file): that
  the form has no written-out factor is not given.
- `ReadsAny` is a hypothesis here. A theorem of that form, at one written term's own rounds and
  columns: `read_first_any`, Johnson/Desc/K12/Honest/Shape/ReadFirst.lean.
- The parameters last, n, dS, dC (and cur, nxt, cutB, cutF, i) are free in the theorems: the caller
  supplies the plan's own.
- `SwitchPub` and the structure `SwitchPlan` of Johnson/Prover/Link/FormBehindAny.lean say much the
  same; neither gives the other.
- Nothing is evaluated here: that the hypotheses hold at a place of a file is not shown here.
  Evaluations at small made-up examples, by #guard, of `firstB` (TestSwitchPub.lean), which joins
  `doorB`, `switchPubB` and the tests on the cuts: Johnson/Desc/K12/Honest/Shape/TestSwitchToy.lean
  (not in the library yet). `ReadsAny` is not evaluated there.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestDoor
import Johnson.Prover.Link.FormSwitchFacts
import Johnson.Prover.Link.FormBehind
import OnBytes.Iop.SymbolLaws
import Johnson.Prover.Link.FormStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open H2K.JointK (foldedFit_pure)

/-! ## 1 `SwitchFacts`, in whatever trees the old rows are -/

/-- Where the reading of the old rows returns `.ok`, it returns as many symbols as listed positions
times rows. -/
theorem read_size (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col)
    (ys : Array E) (hm : i.old.masks ≤ 2) (h : Tw.L9.readOld i pos = .ok (B, left, ys)) :
    ys.size = pos.all.size * i.old.rows := by
  obtain ⟨places, cols, opened, _, _, _, h4⟩ := readOld_inv i pos B left ys h
  exact (singleRowsSymbols_inv i.old opened pos.all.size ys hm h4).2.2.1

/-- **`SwitchFacts` holds, in whatever trees the old rows are.** It is `switchFacts_of`
(Johnson/Prover/Link/FormSwitchFacts.lean) with one hypothesis changed: in place of "the one old
tree can be read" (`ReadFront`), hread: the reading itself returns `.ok` at every D. bk: what the
reading makes of the book after the sending. -/
theorem switchFacts_any {s s' : Sg} (hf : CsFit s s') {p : P12} {n : IoppStage} {last : Bool}
    {dS dC : Fmt.DeclaredRound} {t : T12} {rS rC : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    {rows : SingleRows} {gp j : ℕ} {next : Fmt.M1.Stage}
    (hpass : t.pass = .single rows gp) (hstage : stageAt p (j + 1) next = some n)
    (hearly : p.early = true) (hone : p.answers = 1) (hnk : n.k = s'.h + s'.g) (hnh : n.h = s'.h)
    (ff : FoldedFit s s' t.st.codes n.code n.maskCode rows)
    (hc : Means.CFits (ceilLog2 s.C.l) rows.c) (hp : DenseForm rows.c)
    (hcut : switchCut s.C.a dS dC = true) (hfit : roundsFit [dS, dC] [rS, rC] = true)
    (hdrawE : dS.entry.drawE = (Send.cube t.st.codes (swTarget p n).shape).bits + 1)
    (htrees : Own.treesCan t.st.codes (swNotices p n last) = true)
    (hstep : t.st.oracles.size = t.book.place.size)
    (hG : t.st.groups[gp]? = some { code := n.code, maskCode := n.maskCode })
    (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (hsmall : 2 ^ (s'.h + s'.g) * s'.C.l ≤ 2 ^ 63 ∧ 2 ^ s'.h * s'.Z.l ≤ 2 ^ 63)
    (bk : TreeBook → TreeBook)
    (hread : ∀ D : Taken, ∃ y, Tw.L9.readOld (swIn p n last dS dC t rC gs rows gp D)
      (Positions.ofDraws s.C.a rC.drawn.poss) =
        .ok (bk (swIn p n last dS dC t rC gs rows gp D).book, [], y)) :
    ∃ (D : Taken) (x : Fmt.Ext),
      SwitchFacts p n last dS dC t rS rC gs rows gp D j next
        (bk (swIn p n last dS dC t rC gs rows gp D).book) x ∧
      D.alpha = E.ofTriple a ∧ D.G = { code := n.code, maskCode := n.maskCode } ∧
      D.rS = rS ∧ D.rC = rC := by
  have eT : swTarget p n = switchTargetStage n.code n.maskCode (s'.h + s'.g) s'.h 1 := by
    unfold swTarget
    rw [hnk, hnh, hone]
  obtain ⟨c1, c2, -, -, -, -, -, c8, -, -, -⟩ := switchCut_says hcut
  obtain ⟨⟨-, f2, -, -⟩, ⟨g2, -, -, g5⟩, -⟩ := fit_says hfit
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -⟩ := switchCut_says hcut
  obtain ⟨lay, hlay⟩ : ∃ lay, Own.treesMade t.st.codes (swNotices p n last) = some lay :=
    Option.isSome_iff_exists.1 htrees
  have hlen : (rS.drawn.elems.map E.ofTriple).length =
      (Send.cube t.st.codes (swTarget p n).shape).bits + 1 := by
    rw [List.length_map, f2, hdrawE]
  obtain ⟨beta, hbeta⟩ := seed_of _ _ hlen
  have lZ' : (t.st.codes.mask.getD n.maskCode default).ell = s'.Z.l :=
    congrArg (·.l) (getD_of_map_some ff.prog.zk')
  have hZpos : 1 ≤ s'.Z.l := by
    have hmask := hf.mask
    rcases Nat.eq_zero_or_pos s'.Z.l with h0 | h0
    · rw [h0] at hmask
      omega
    · exact h0
  obtain ⟨places, hpl⟩ : ∃ places, Send.pad t.st.codes (swTarget p n).shape = some places := by
    rw [eT]
    exact pad_some _ _ _ _ _ (by rw [lZ']; exact hZpos)
  obtain ⟨smp, hsmp⟩ := form_some t.st.codes (swTarget p n).shape t.st.oracles.size
    ⟨(rS.drawn.elems.map E.ofTriple).take (Send.cube t.st.codes (swTarget p n).shape).bits, beta⟩
    0 places hpl
  obtain ⟨cd, hcd, hcdC⟩ : ∃ cd, t.st.codes.base[rows.code]? = some cd ∧ codeOf cd = s.C := by
    have h := ff.prog.code
    cases hz : t.st.codes.base[rows.code]? with
    | none => rw [hz] at h; cases h
    | some z => rw [hz] at h; exact ⟨z, rfl, Option.some.inj h⟩
  have hcda : cd.logN = s.C.a := congrArg (·.a) hcdC
  obtain ⟨x, hx⟩ : ∃ x, rC.drawn.elems = [x] :=
    List.length_eq_one_iff.1 (g2.trans c8)
  obtain ⟨y, hy⟩ := hread ⟨lay, rS, rC, beta, E.ofTriple a, smp, places,
    cd, #[], { code := n.code, maskCode := n.maskCode }, []⟩
  have hysz : y.size = (Positions.ofDraws s.C.a rC.drawn.poss).all.size * rows.rows :=
    read_size _ _ _ _ _ (by
      show rows.masks ≤ 2
      rw [ff.prog.masks]) hy
  have hxs : ∀ z ∈ rC.drawn.poss, z < 2 ^ s.C.a := by
    intro z hz
    have := List.all_eq_true.1 g5 z hz
    rw [c10] at this
    exact of_decide_eq_true this
  let D1 : Taken := ⟨lay, rS, rC, beta, E.ofTriple a, smp, places, cd, y,
    { code := n.code, maskCode := n.maskCode }, []⟩
  let D : Taken := { D1 with rows := (Own.swRows (D1.stJ (swTarget p n) gp (othersOf last n) t.st)
    rows (swTarget p n) t.st.oracles.size #[] (swPos rC D1) y).getD [] }
  have hpos : swPos rC D = Positions.ofDraws s.C.a rC.drawn.poss := by
    show Positions.ofDraws cd.logN rC.drawn.poss = _
    rw [hcda]
  have hgroup : (ledgerShut (D.stA (swTarget p n) (othersOf last n) t.st) (swTarget p n)
      t.st.oracles.size).groups[gp]? = some D.G := by
    rw [shut_groups]
    exact hG
  have hcan : Tw.K2.rowsCan (D.stJ (swTarget p n) gp (othersOf last n) t.st) rows (swTarget p n)
      #[] (swPos rC D) D.y = true := by
    rw [hpos, eT]
    exact can_of _ rows n.code n.maskCode _ _ _
      ((D.stJ_shape _ gp (othersOf last n) t.st).1.symm ▸ ff.prog) ff.kept _ y hysz
  have e := swNotices_eq p n last
  refine ⟨D, x,
    { pass := hpass, stage := hstage, early := hearly, one := hone
      guard := by
        rw [eT]
        exact guard_of hf t.st rows n.code n.maskCode ff.prog
      cut := by
        show switchCut cd.logN dS dC = true
        rw [hcda]
        exact hcut
      fit := hfit
      recv := recv_of t.st t.book (lt_of_map_some ff.prog.code') (lt_of_map_some ff.prog.zk')
        htrees hstep
      trees := hlay, seed := hbeta
      factor := factor_of dS rS _ beta c1 c2 hdrawE (f2.trans hdrawE) (nz_says hfit) hbeta
      form := hsmp, pad := hpl, ans := hans
      admit := by
        rw [e]
        exact admit_of t.st _ _ _ places hpl hone
      elem := hx, code := hcd
      read := by
        rw [hpos]
        exact hy
      group := hgroup
      joinOk := join_of D (swTarget p n) gp (othersOf last n) t.st hG rfl rfl rfl rfl
      can := hcan, made := rfl
      addOk := addOk_of hf ff hnk hnh hone hgroup hpl hcan rfl rfl rfl hsmall hc hp hxs },
    rfl, rfl, rfl, rfl⟩

/-! ## 2 The switch and the batching after it accept -/

/-- **What is public at a switch**: the plan, the codes, the two declared rounds. No clause on a
tree of the old rows. c, n: the two stages as the program names them. -/
structure SwitchPub (p : P12) (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool)
    (c n : IoppStage) (dS dC : Fmt.DeclaredRound) : Prop where
  early : p.early = true
  one : p.answers = 1
  stageN : stageAt p (j + 1) next = some n
  fits : CsFit (sgOf cur) (sgOf next)
  small : (sgOf cur).C.a ≤ 32
  codes : StageCodes (sgOf cur) c K
  zk : (K.mask[c.maskCode]?).map codeOf = some (sgOf cur).Z
  codeN : (K.base[n.code]?).map codeOf = some (sgOf next).C
  zkN : (K.mask[n.maskCode]?).map codeOf = some (sgOf next).Z
  nk : n.k = (sgOf next).h + (sgOf next).g
  nh : n.h = (sgOf next).h
  lengths : K.lengthsOk = true
  bounds : 2 ^ ((sgOf next).h + (sgOf next).g) * (sgOf next).C.l ≤ 2 ^ 63 ∧
    2 ^ (sgOf next).h * (sgOf next).Z.l ≤ 2 ^ 63
  cutSw : switchCut (sgOf cur).C.a dS dC = true
  drawE : dS.entry.drawE = (Send.cube K (swTarget p n).shape).bits + 1
  count : dC.entry.rows = 2 + 3 * dC.entry.poss
  trees : Own.treesCan K (swNotices p n last) = true

/-- `StepPlan`, the plan at a step whose round of the positions opens one tree, gives it. -/
theorem switchPub_of_step {p : P12} {K : Codes} {j : ℕ} {cur next : Fmt.M1.Stage} {last : Bool}
    {l : Laid} {c n : IoppStage} {dS dC : Fmt.DeclaredRound}
    (Pl : StepPlan p K j cur next last l c n dS dC) : SwitchPub p K j cur next last c n dS dC :=
  ⟨Pl.early, Pl.one, Pl.stageN, Pl.fits, Pl.sized.small, Pl.codes, Pl.zk, Pl.codeN, Pl.zkN, Pl.nk,
    Pl.nh, Pl.lengths, Pl.bounds, Pl.cutSw, Pl.drawE, by rw [Pl.count, Pl.poss], Pl.trees⟩

/-- **What a switch and the batching behind it have delivered**, at the structure t in front of the
switch: the two parts' accepts, with the structures behind written out; the frame's question behind
them (the next mask has come); the library's own structure of a switch (`Did`) at the same letters;
"in order" behind; the letters' answer, rounds and group; what is public of the old rows. The
letters: the fields of D. bk: what the reading makes of the book after the sending. -/
def SwitchDone (p : P12) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool) (n : IoppStage)
    (dS dC : Fmt.DeclaredRound) (t : T12) (rows : SingleRows) (gp : ℕ) (rS rC : Fmt.RoundView) (a : Fmt.Ext)
    (gs : List (List (ℕ × List UInt64))) (bk : TreeBook → TreeBook) : Prop :=
  ∃ (D : Taken) (x : Fmt.Ext) (row' : GroupRow) (B : TreeBook) (lay : GroupLayout),
    B = bk (swIn p n last dS dC t rC gs rows gp D).book ∧
    lay = Own.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st) ∧
    (guardedProximityTestParts.switch p j cur next last [dS, dC]).decide t [rS, rC] gs =
      .ok (switchT p n last t rC gp D B (E.ofTriple x)) ∧
    (guardedProximityTestParts.batBehind p (j + 1) next [dS, dC]).decide
      (switchT p n last t rC gp D B (E.ofTriple x)) [] [] =
        .ok (behindT p n last t rC gp D B row' lay) ∧
    (behindT p n last t rC gp D B row' lay).mask = some (t.st.oracles.size + 1) ∧
    (!p.early || guardedProximityTestParts.maskCame (behindT p n last t rC gp D B row' lay)) = true ∧
    Did p.nums.firstTree (keyed p [dS, dC] gs) rows (swTarget p n) gp (othersOf last n) t.st
      t.book t.roots (behindT p n last t rC gp D B row' lay).st B (swOut p n last t rC D) row' lay
      (E.ofTriple x) D ∧
    Means.InOrder (behindT p n last t rC gp D B row' lay).st ∧
    D.alpha = E.ofTriple a ∧ D.rS = rS ∧ D.rC = rC ∧
    D.G = { code := n.code, maskCode := n.maskCode } ∧
    FoldedFit (sgOf cur) (sgOf next) t.st.codes n.code n.maskCode rows ∧
    Means.CFits (ceilLog2 (sgOf cur).C.l) rows.c ∧ DenseForm rows.c

/-- The reading of the old rows returns `.ok` at every D, leaves no column, and returns the book bk
of the book after the sending. -/
def ReadsAny (p : P12) (cur : Fmt.M1.Stage) (last : Bool) (n : IoppStage) (dS dC : Fmt.DeclaredRound)
    (t : T12) (rows : SingleRows) (gp : ℕ) (rC : Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (bk : TreeBook → TreeBook) : Prop :=
  ∀ D : Taken, ∃ y, Tw.L9.readOld (swIn p n last dS dC t rC gs rows gp D)
    (Positions.ofDraws (sgOf cur).C.a rC.drawn.poss) =
      .ok (bk (swIn p n last dS dC t rC gs rows gp D).book, [], y)

/-- **A switch and the batching after it accept, in whatever trees the old rows are.** t: the
structure before the switch; what passes is what a fold returns of a batched row. bk: what the
reading makes of the book after the sending. -/
theorem switch_any {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {last : Bool} {c n : IoppStage}
    {dS dC : Fmt.DeclaredRound} {t : T12} (Pl : SwitchPub p t.st.codes j cur next last c n dS dC)
    {S0 S1 : Statement} {row : GroupRow} {L : GroupLayout} {id gp : ℕ} {eps claim : E}
    {gamma : List E}
    (hpass : t.pass = .single (foldOutput S1 (ioppFoldShape c L) row id eps gamma claim) gp)
    (hc0 : S0.codes = t.st.codes) (hc1 : S1.codes = t.st.codes) (hlen : gamma.length = c.k)
    (hshape : foldShapeOk S0 (ioppFoldShape c L) = true)
    (hrow : foldRowOk S1 (ioppFoldShape c L) row = true) (h0 : row.kept = #[])
    (hkept : ∀ i, i < L.members.size → L.kept.getD i false = false) (hplain : DenseForm row.c)
    (hstep : t.st.oracles.size = t.book.place.size)
    (hG : t.st.groups[gp]? = some { code := n.code, maskCode := n.maskCode })
    (hO : Means.InOrder t.st) (rS rC : Fmt.RoundView) (hfit : roundsFit [dS, dC] [rS, rC] = true)
    (a : Fmt.Ext) (hans : rC.vals = [.answer a]) (gs : List (List (ℕ × List UInt64)))
    (bk : TreeBook → TreeBook)
    (hread : ReadsAny p cur last n dS dC t
      (foldOutput S1 (ioppFoldShape c L) row id eps gamma claim) gp rC gs bk) :
    SwitchDone p j cur next last n dS dC t
      (foldOutput S1 (ioppFoldShape c L) row id eps gamma claim) gp rS rC a gs bk := by
  have ff : FoldedFit (sgOf cur) (sgOf next) t.st.codes n.code n.maskCode
      (foldOutput S1 (ioppFoldShape c L) row id eps gamma claim) :=
    foldedFit_pure t.st.codes (sgOf cur) (sgOf next) c Pl.codes n.code n.maskCode Pl.zk Pl.codeN
      Pl.zkN Pl.small S0 S1 row L id eps claim gamma hc0 hc1 h0 hkept (hlen.trans Pl.codes.k)
      hshape hrow
  obtain ⟨cd, hcd, ecd⟩ := Pl.codes.base
  have hc : Means.CFits (ceilLog2 (sgOf cur).C.l)
      (foldOutput S1 (ioppFoldShape c L) row id eps gamma claim).c := by
    have h1 := cfits_foldOutput S1 (ioppFoldShape c L) row id eps gamma claim hlen hrow
    have e : (S1.codes.base.getD (ioppFoldShape c L).code default).ell = (sgOf cur).C.l := by
      show (S1.codes.base.getD c.code default).ell = _
      rw [hc1, Array.getD_eq_getD_getElem?, hcd]
      exact congrArg (·.l) ecd
    rw [e] at h1
    exact h1
  have hp : DenseForm (foldOutput S1 (ioppFoldShape c L) row id eps gamma claim).c :=
    denseForm_foldOutput S1 (ioppFoldShape c L) row id eps gamma claim hplain
  obtain ⟨D, x, F, hα, hDG, hrS, hrC⟩ := switchFacts_any Pl.fits hpass Pl.stageN Pl.early Pl.one
    Pl.nk Pl.nh ff hc hp Pl.cutSw hfit Pl.drawE Pl.trees hstep hG a hans Pl.bounds bk hread
  obtain ⟨row', F', hd, _, hB⟩ := behind_paid F ff hO Pl.lengths hDG hrS hrC Pl.count
  have hmask := did_mask hd (by cases last <;> rfl)
  refine ⟨D, x, row', _, _, rfl, rfl, switch5_yes cur (front_of_facts F),
    behind5_yes dS rC j next _ F', hmask, ?_, hd, hB, hα, hrS, hrC, hDG, ff, hc, hp⟩
  show (!p.early || ((swOut p n last t rC D).others[0]?).isSome) = true
  rw [hmask]
  simp

/-! ## 3 After a fold -/

/-- **After a fold's written-out structure.** tB: the structure before the fold. m: the mask's field
behind it (the fold's part leaves it as it was). -/
theorem switch_behind_fold {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {last : Bool}
    {c n : IoppStage} {dS dC : Fmt.DeclaredRound} {tB : T12} {row : GroupRow} {L : GroupLayout}
    {id : ℕ} (F : FoldFront p j cur tB row L c (n.code, n.maskCode) id)
    (Pl : SwitchPub p tB.st.codes j cur next last c n dS dC) (h0 : row.kept = #[])
    (hkept : ∀ i, i < L.members.size → L.kept.getD i false = false) (hplain : DenseForm row.c)
    (hstep : tB.st.oracles.size = tB.book.place.size) (hO : Means.InOrder tB.st) (m : Option ℕ)
    (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (hR : rR.length = c.k) (rS rC : Fmt.RoundView)
    (hfit : roundsFit [dS, dC] [rS, rC] = true) (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (gs : List (List (ℕ × List UInt64))) (bk : TreeBook → TreeBook)
    (hread : ReadsAny p cur last n dS dC
      { foldT tB row L c (n.code, n.maskCode) id (rE :: rR) with mask := m }
      (foldOut tB row L c id (rE :: rR)) tB.st.groups.size rC gs bk) :
    SwitchDone p j cur next last n dS dC
      { foldT tB row L c (n.code, n.maskCode) id (rE :: rR) with mask := m }
      (foldOut tB row L c id (rE :: rR)) tB.st.groups.size rS rC a gs bk :=
  switch_any (t := { foldT tB row L c (n.code, n.maskCode) id (rE :: rR) with mask := m })
    (S0 := tB.st) (S1 := spent tB.st id) (gp := tB.st.groups.size) Pl rfl rfl rfl
    (by rw [List.length_map]; exact hR) ((Own.foldShapeFits_agrees _ _).trans F.shape)
    ((Own.foldRowFits_agrees _ _ _).trans ((foldRowFits_spent _ _ _ _).trans F.rowFits)) h0 hkept
    hplain (step_foldT tB row L c _ id (rE :: rR) hstep)
    (by
      show (tB.st.groups.push _)[tB.st.groups.size]? = _
      simp)
    (inOrder_foldT tB row L c _ id (rE :: rR) hO) rS rC hfit a hans gs bk hread

/-! ## 4 The first switch, after the door -/

open ProofFile.Honest.K12 (TestFrontOwn foldTOwn enteredT withOwn ownBook foldFrontOwn_first
  front_entered)

theorem batT_codes (t : T12) (G : Group) (row : GroupRow) :
    (batT t G row).st.codes = t.st.codes := closeLedgers_codes _ _

theorem batT_step (t : T12) (G : Group) (row : GroupRow)
    (h : t.st.oracles.size = t.book.place.size) :
    (batT t G row).st.oracles.size = (batT t G row).book.place.size := by
  show (begun t.st t.g G).oracles.size = t.book.place.size
  rw [(ProxRun.begun_sizes _ _ _).1]
  exact h

/-- **The first switch, where the mask has come.** -/
theorem first_switch_came {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {G : Group} {i : ℕ × ℕ}
    {n : IoppStage} {id : ℕ} (H : TestFront p cur nxt t G i (n.code, n.maskCode) id)
    (hstep : t.st.oracles.size = t.book.place.size) {x : E} {row : GroupRow}
    (hr : Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩ x = some row)
    {last : Bool} {dS dC : Fmt.DeclaredRound}
    (Pl : SwitchPub p t.st.codes 0 cur nxt last ⟨i.1, i.2, cur.k, cur.h⟩ n dS dC)
    (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (hR : rR.length = cur.k) (rS rC : Fmt.RoundView)
    (hfit : roundsFit [dS, dC] [rS, rC] = true) (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (gs : List (List (ℕ × List UInt64))) (bk : TreeBook → TreeBook)
    (hread : ReadsAny p cur last n dS dC
      (foldT (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
        (n.code, n.maskCode) id (rE :: rR))
      (foldOut (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ id (rE :: rR))
      (batT t G row).st.groups.size rC gs bk) :
    SwitchDone p 0 cur nxt last n dS dC
      (foldT (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
        (n.code, n.maskCode) id (rE :: rR))
      (foldOut (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ id (rE :: rR))
      (batT t G row).st.groups.size rS rC a gs bk :=
  switch_behind_fold (foldFront_first H x row hr) (by rw [batT_codes]; exact Pl)
    (H2K.Pin.combine_noKept0 _ _ _ _ _ hr fun k => H.noKept k) (fun k _ => H.noKept k)
    (combine_dense _ _ _ _ _ H.dense hr) (batT_step t G row hstep) (H.order.begun t.g G H.group)
    (batT t G row).mask rE rR hR rS rC hfit a hans gs bk hread

theorem withOwn_sent (S : Statement) (F : FoldShape) :
    withOwn S F = stSent S #[foldMaskNotice F] := by
  unfold withOwn stSent
  simp

/-- **The first switch, where the first fold receives its own mask.** -/
theorem first_switch_own {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {G : Group} {i : ℕ × ℕ}
    {n : IoppStage} (H : TestFrontOwn p cur nxt t G i (n.code, n.maskCode)) {x : E}
    {row : GroupRow}
    (hr : Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩ x = some row)
    {last : Bool} {dS dC : Fmt.DeclaredRound}
    (Pl : SwitchPub p t.st.codes 0 cur nxt last ⟨i.1, i.2, cur.k, cur.h⟩ n dS dC)
    (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (hR : rR.length = cur.k) (rS rC : Fmt.RoundView)
    (hfit : roundsFit [dS, dC] [rS, rC] = true) (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (gs : List (List (ℕ × List UInt64))) (bk : TreeBook → TreeBook)
    (hread : ReadsAny p cur last n dS dC
      (foldTOwn p (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
        (n.code, n.maskCode) (rE :: rR))
      (foldOut (enteredT p (batT t G row)
          (ioppFoldShape ⟨i.1, i.2, cur.k, cur.h⟩ (Means.layoutOf t.st G))) row
        (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ (batT t G row).st.oracles.size
        (rE :: rR))
      (batT t G row).st.groups.size rC gs bk) :
    SwitchDone p 0 cur nxt last n dS dC
      (foldTOwn p (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
        (n.code, n.maskCode) (rE :: rR))
      (foldOut (enteredT p (batT t G row)
          (ioppFoldShape ⟨i.1, i.2, cur.k, cur.h⟩ (Means.layoutOf t.st G))) row
        (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ (batT t G row).st.oracles.size
        (rE :: rR))
      (batT t G row).st.groups.size rS rC a gs bk := by
  have H' := foldFrontOwn_first H x row hr
  refine switch_behind_fold (front_entered H') (by
      show SwitchPub p (batT t G row).st.codes _ _ _ _ _ _ _ _
      rw [batT_codes]
      exact Pl)
    (H2K.Pin.combine_noKept0 _ _ _ _ _ hr fun k => H.noKept k) (fun k _ => H.noKept k)
    (combine_dense _ _ _ _ _ (fun r h => denseRow_of_plain (H.plain r h)) hr) ?_ ?_ none rE rR hR
    rS rC hfit a hans gs bk hread
  · show ((batT t G row).st.oracles.push _).size = ((batT t G row).book.place.push _).size
    rw [Array.size_push, Array.size_push, H'.inStep]
  · show Means.InOrder (withOwn (batT t G row).st _)
    rw [withOwn_sent]
    exact (H.order.begun t.g G H.group).stSent _

/-! ## 5 The whole first stage, from the shape -/

open ProofFile.Honest.K12 (foldCutOwn foldCutOwn_of door_yes_own)

/-- Rounds of a declared form of 1 + k rounds, without their digests: a first round and k more. -/
theorem rounds_split {k : ℕ} {cut : List Fmt.DeclaredRound} (hc : cut.length = 1 + k)
    {rs : List Fmt.RoundView} (hf : roundsFit cut rs = true) :
    ∃ rE rR, rs.map noDigest = rE :: rR ∧ rR.length = k := by
  have hlen : (rs.map noDigest).length = 1 + k := by
    rw [List.length_map, Sound.roundsFit_len _ _ hf, hc]
  cases h : rs.map noDigest with
  | nil =>
    rw [h] at hlen
    simp at hlen
    omega
  | cons rE rR =>
    rw [h, List.length_cons] at hlen
    exact ⟨rE, rR, rfl, by omega⟩

theorem length_of_foldCutOwn {k : ℕ} : ∀ {cut : List Fmt.DeclaredRound}, foldCutOwn k cut = true →
    cut.length = 1 + k
  | [], h => by cases h
  | dE :: dR, h => by
    show dR.length + 1 = 1 + k
    rw [(foldCutOwn_of h).2.1, Nat.add_comm]

/-- **The first stage from the shape, where the mask has come**: the front, the batching, the
frame's question, the first fold, the first switch and the batching behind it accept in a row,
whatever trees the group's members stand in. Asked: the door's Bool on the shape; the first mark;
the rows taken in are plain; the front's named test on the open rows; what is public at the switch;
the tests on the plan's cuts; rounds of the declared form; the round of the positions shows one
answer; the reading's accept, at the row that the batching makes. -/
theorem first_stage_of_shape {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i : ℕ × ℕ}
    {n : IoppStage} {id : ℕ} {cutB cutF : List Fmt.DeclaredRound} {last : Bool}
    {dS dC : Fmt.DeclaredRound} (h : doorB p cur nxt cutB i (n.code, n.maskCode) (testSh t) = true)
    (hm : t.mask = some id) (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true)
    (Pl : SwitchPub p t.st.codes 0 cur nxt last ⟨i.1, i.2, cur.k, cur.h⟩ n dS dC)
    (hB : batCut cutB = true) (hF : foldCut cur.k cutF = true) (rsB rsF : List Fmt.RoundView)
    (fB : roundsFit cutB rsB = true) (fF : roundsFit cutF rsF = true) (rS rC : Fmt.RoundView)
    (hfit : roundsFit [dS, dC] [rS, rC] = true) (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (gs : List (List (ℕ × List UInt64))) (bk : TreeBook → TreeBook)
    (hread : ∀ G row, t.st.groups[t.g]? = some G →
      Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row →
      ReadsAny p cur last n dS dC
      (foldT (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
        (n.code, n.maskCode) id (rsF.map noDigest))
      (foldOut (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ id
        (rsF.map noDigest))
      (batT t G row).st.groups.size rC gs bk) :
    ∃ G row,
      t.st.groups[t.g]? = some G ∧
      Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row ∧
      (guardedProximityTestParts.front p).decide t [] [] = .ok t ∧
      (guardedProximityTestParts.bat p cutB).decide t (rsB.map noDigest) [] = .ok (batT t G row) ∧
      (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true ∧
      (guardedProximityTestParts.fold p 0 cur cutF).decide (batT t G row) (rsF.map noDigest) [] =
        .ok (foldT (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
          (n.code, n.maskCode) id (rsF.map noDigest)) ∧
      SwitchDone p 0 cur nxt last n dS dC
        (foldT (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
          (n.code, n.maskCode) id (rsF.map noDigest))
        (foldOut (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ id
          (rsF.map noDigest))
        (batT t G row).st.groups.size rS rC a gs bk := by
  have h' := h
  unfold doorB at h'
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
  have h4' : (match t.mask with
    | some id => cameB cur (testSh t).core t.g i id
    | none => (testSh t).core.st.oracles.length == (testSh t).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFront_of h1 hm h4' ht hp
  have B := batOwes_of h2 H.group
  have Fo := frontOwes_of h3 hv H.group
  obtain ⟨row, hr, hb⟩ := bat5_yes H cutB B hB rsB fB
  obtain ⟨rE, rR, hrs, hR⟩ := rounds_split (length_of_foldCut hF) fF
  have hrd := hread G row H.group hr
  refine ⟨G, row, H.group, hr, front5_yes B.pass H.group Fo, hb, group_batT H row,
    fold5_yes (foldFront_first H _ row hr) hF rsF fF, ?_⟩
  rw [hrs] at hrd ⊢
  exact first_switch_came H (VerifiableInference.Desc.K12.Seat.front_in_step Fo.front) hr Pl rE rR
    hR rS rC hfit a hans gs bk hrd

/-- **The first stage from the shape, where the first fold receives its own mask.** -/
theorem first_stage_of_shape_own {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i : ℕ × ℕ}
    {n : IoppStage} {cutB cutF : List Fmt.DeclaredRound} {last : Bool} {dS dC : Fmt.DeclaredRound}
    (h : doorB p cur nxt cutB i (n.code, n.maskCode) (testSh t) = true) (hm : t.mask = none)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true)
    (Pl : SwitchPub p t.st.codes 0 cur nxt last ⟨i.1, i.2, cur.k, cur.h⟩ n dS dC)
    (hB : batCut cutB = true) (hF : foldCutOwn cur.k cutF = true) (rsB rsF : List Fmt.RoundView)
    (fB : roundsFit cutB rsB = true) (fF : roundsFit cutF rsF = true) (rS rC : Fmt.RoundView)
    (hfit : roundsFit [dS, dC] [rS, rC] = true) (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (gs : List (List (ℕ × List UInt64))) (bk : TreeBook → TreeBook)
    (hread : ∀ G row, t.st.groups[t.g]? = some G →
      Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row →
      ReadsAny p cur last n dS dC
      (foldTOwn p (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
        (n.code, n.maskCode) (rsF.map noDigest))
      (foldOut (enteredT p (batT t G row)
          (ioppFoldShape ⟨i.1, i.2, cur.k, cur.h⟩ (Means.layoutOf t.st G))) row
        (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ (batT t G row).st.oracles.size
        (rsF.map noDigest))
      (batT t G row).st.groups.size rC gs bk) :
    ∃ G row,
      t.st.groups[t.g]? = some G ∧
      Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row ∧
      (guardedProximityTestParts.front p).decide t [] [] = .ok t ∧
      (guardedProximityTestParts.bat p cutB).decide t (rsB.map noDigest) [] = .ok (batT t G row) ∧
      (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true ∧
      (guardedProximityTestParts.fold p 0 cur cutF).decide (batT t G row) (rsF.map noDigest) [] =
        .ok (foldTOwn p (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
          (n.code, n.maskCode) (rsF.map noDigest)) ∧
      SwitchDone p 0 cur nxt last n dS dC
        (foldTOwn p (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
          (n.code, n.maskCode) (rsF.map noDigest))
        (foldOut (enteredT p (batT t G row)
            (ioppFoldShape ⟨i.1, i.2, cur.k, cur.h⟩ (Means.layoutOf t.st G))) row
          (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ (batT t G row).st.oracles.size
          (rsF.map noDigest))
        (batT t G row).st.groups.size rS rC a gs bk := by
  have h' := h
  unfold doorB at h'
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
  have h4' : (match t.mask with
    | some id => cameB cur (testSh t).core t.g i id
    | none => (testSh t).core.st.oracles.length == (testSh t).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFrontOwn_of h1 hm (by simpa using h4') ht hp
  obtain ⟨row, hr, a1, a2, a3, a4⟩ := door_yes_own H cutB cutF (batOwes_of h2 H.group)
    (frontOwes_of h3 hv H.group) hB hF rsB rsF fB fF
  obtain ⟨rE, rR, hrs, hR⟩ := rounds_split (length_of_foldCutOwn hF) fF
  have hrd := hread G row H.group hr
  refine ⟨G, row, H.group, hr, a1, a2, a3, a4, ?_⟩
  rw [hrs] at hrd ⊢
  exact first_switch_own H hr Pl rE rR hR rS rC hfit a hans gs bk hrd

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.read_size
#print axioms ProofFile.Honest.Sh.switchFacts_any
#print axioms ProofFile.Honest.Sh.switchPub_of_step
#print axioms ProofFile.Honest.Sh.switch_any
#print axioms ProofFile.Honest.Sh.switch_behind_fold
#print axioms ProofFile.Honest.Sh.batT_codes
#print axioms ProofFile.Honest.Sh.batT_step
#print axioms ProofFile.Honest.Sh.first_switch_came
#print axioms ProofFile.Honest.Sh.withOwn_sent
#print axioms ProofFile.Honest.Sh.first_switch_own
#print axioms ProofFile.Honest.Sh.rounds_split
#print axioms ProofFile.Honest.Sh.length_of_foldCutOwn
#print axioms ProofFile.Honest.Sh.first_stage_of_shape
#print axioms ProofFile.Honest.Sh.first_stage_of_shape_own
#print axioms ProofFile.Honest.Sh.SwitchPub
#print axioms ProofFile.Honest.Sh.SwitchDone
#print axioms ProofFile.Honest.Sh.ReadsAny
