-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ShapeAll.lean: the decision of a proximity test's block accepts
all that `testAll` (Test.lean in this folder) shows at a job whose functions are the caller's, at
every list of challenges that the test's declared rounds can sample, from premises that name no
challenge of the test. That is `accepts_every_list`: of its hypotheses only the last, which says
that the list can be sampled, names a challenge of the test. That a list can be sampled means that
`drawsFit`, a test of the frame (Johnson/Desc/ProofFile/Honest/Frame.lean), is true of the declared
rounds and the list. `accepts_of_plan` (PlanB.lean in this folder) concludes the same acceptance at
one family of challenges, from a test on the plan (`planB`) and three structures. Two of the three,
`ShapeAsks` and `DataAsks`, are stated at the challenges: they speak of the state after the batching
and of the state after the first fold. Here these two states are written out, as `batT`
(Johnson/Prover/Link/FormFirst.lean) and `foldT` (Johnson/Prover/Link/FormFold.lean). By the text of
these two definitions the challenges enter the two states through the claim's row and the single
rows only. What the two structures ask of these rows is proved whatever was sampled, provided that
the rounds of the batching and of the first fold have the declared form (two clauses of the third
structure, `FormAsks`). So the two structures follow from two that name no challenge of the test,
`FrontAsks` and `DataFront`. `FormAsks` holds at every list that can be sampled, under four clauses
on the plan (`formAsks_of_draws`, FormDraws.lean in this folder). Where the first fold's fresh table
has come earlier; three stages or more. General in the job, the prover's input, the front, the
coins, the table of codes, the plain data, the columns and the plain rows. Definitions, statements
and proofs.

In the list: J is a job (`TestJob`, Test.lean): what a caller supplies for its test. `J.p` is its
place (`P12`, Johnson/Desc/K12/Frame.lean): the numbers of a place at which a proximity test is,
among them the list of stages (`Fmt.M1.Stage`); `stA J.p` and `stN J.p` (PlanB.lean) are the first
two stages. The plan is the place with the rounds that it declares, `(laidOf J.p).map (·.1)`
(Johnson/Desc/K12/Law/ReadsK.lean). w is the prover's input. fr is the front (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean): what precedes the test, among it the challenges received
(`heard`). C: the coins that `testAll` reads (`TestCoins`, Test.lean). D: the test's challenges by
the round's number; `byNo ds` (PlayedTerm.lean in this folder) reads a list ds in this way. The term
is `testAll J w fr C D`: all that is shown in the test. The block is `proximityTestKind guardedProximityTestParts J.p`
(Johnson/Desc/K12/Frame.lean; `guardedProximityTestParts`: Johnson/Desc/K12/JoinGuarded.lean). The state on entry is
`J.rec₀ w fr`, of the type `T12` of the verifier's state inside a test (Johnson/Desc/K12/Join.lean).
Its fields are a statement `st`, a book of trees `book` (`TreeBook`, OnBytes/Iop/Ground.lean), a
count `roots`, the number `g` of the group under test, what a part of the block passes on (`pass`: a
batching a claim's row with its layout, a fold single rows), and `mask`: the number of the message
that holds the fresh table, where that has come earlier. G is group number g of the statement on
entry, and its layout is `layoutOf` (Johnson/Desc/Means/Layout.lean). `begun`
(OnBytes/Slice/BlkBegin.lean) gives the statement with the group's test begun: the members' ledgers
are closed, and the group is marked and holds no open row. `spent S id` (FormFold.lean) sets the
flag `spentAsMask` of message number id. `Ground.withGroup` (Johnson/Desc/First/Base/Ground.lean)
appends a group without member or row. K is a table of codes (`Codes`, OnBytes/Iop/Ground.lean). Dp
is the library's plain data on the group under test (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean),
among them the list `Dp.ts` of trees. c is a tree's column at a position, as words. R is the
prover's rows as plain functions of numbers (`PlainRows`, Johnson/Desc/K12/Honest/FirstRows.lean). A
shape holds numbers, flags and lists: `coreSh` (Johnson/Desc/Ground/Shape/Core.lean) of a statement,
a book of trees and a count of roots; `singleSh`, of type `SingleSh`
(Johnson/Desc/K12/Honest/Shape/Test.lean), of single rows. `lettersOf` (AllB.lean in this folder)
computes from the place and its first two stages the pair i of the first stage's code numbers and
the next stage n as the program names it.

  `accepts_every_list`: under the six hypotheses below, at every list that the declared rounds can
    sample the block's decision accepts all that the term shows: the block's `decide`, at the state
    on entry, the rounds of `testAll J w fr C (byNo ds)` without their digests (`noDigest`,
    Johnson/Desc/Block.lean) and its groups of opened columns, returns `.ok t'` for some state t'
  `shapeAsks_of_front`: if `planB J.p K Dp.ts.length` is true, and `FrontAsks J w fr K Dp` and
    `FormAsks J w fr C D` hold, then `ShapeAsks J w fr C D K Dp` holds. D is a free parameter. The
    whole `FormAsks` is a hypothesis, though the proof uses only its clauses on the batching's and
    the first fold's rounds (`bat`, `fold`); ShapeOfTwo.lean in this folder states the same from
    these two clauses
  `dataAsks_of_front`: under the same three hypotheses, `DataFront J w fr C Dp c R` gives
    `DataAsks J w fr C D Dp c R`. Of `FormAsks` the proof uses `bat` only
  `FrontAsks J w fr K Dp`: a definition: a structure of eight hypotheses on the state on entry. The
    first six are the six clauses of `ShapeAsks` that name no challenge, word for word: `codes`,
    `door`, `came`, `tidy`, `plainRows` and `claims`; the head of PlanB.lean says what each is. The
    other two are stated at the group under test, G. `plain`: the plain data are made of the state
    with the group's test begun, and pass their test: `gpOf` (FirstOk.lean) returns Dp at `batT` of
    the state on entry, G and the empty row, and Dp passes `gpL` (FirstOk.lean) at the empty row;
    and two sizes of the layout: 2 ^ `logEll` and 2 ^ `logEllZk` are the first stage's `C.l` and
    `Z.l`. `pub`, at the number id in the field `mask`: `readPubB`
    (Johnson/Desc/K12/Honest/Shape/ReadShape.lean) is true at the state with the fresh table spent
    and the next group made, at `frontSingle`. In Lean that state is `coreSh` of the statement
    `Ground.withGroup (spent (begun st g G) id) n.code n.maskCode`, with st, g, the book of trees
    and the count of roots of the state on entry; `frontSingle` is at the layout of G, i, the first
    stage's k and h, and id; the range of positions is the first stage's `C.a`
  `DataFront J w fr C Dp c R`: a definition: a structure of four hypotheses on the prover's data:
    `DataAsks` with its last clause at the state with the group's test begun. `cols`, `state` and
    `trees` are those of `DataAsks`, word for word. `allSay` has the statement `begun st g G` and
    the layout of G where `DataAsks` has the statement after the batching and the layout that is
    passed there
  `frontSingle L i k h id`: a definition: the shape of the single rows after the first fold, as far
    as `readPubB` reads it. It is made of the layout L, the two codes' numbers i, the stage's k and
    h and the fresh table's number id: `lay` is L with k and h set, `gamma` is k, `masks` is 2,
    `fresh` is id, `keptRows` is 0. The six other fields (`code` and `maskCode` from i; 0, the empty
    list and true for the rest) are compared with nothing here
  `readPubB_congr`: `readPubB` reads five fields of that shape only: it returns the same at two
    values of `SingleSh` that agree in `masks`, `keptRows`, `gamma`, `lay` and `fresh`

By what. `shapeAsks_of_front` unfolds `planB` and keeps four of its clauses: `switchPubB`, `batCut`,
`foldCut`, and that h is at most k at the first stage. `door_facts`
(Johnson/Desc/K12/Honest/Shape/SwitchInShape.lean), which calls `bat5_yes`
(Johnson/Prover/Link/FormBatLaws.lean), gives the group G and the batched row, and with `recB_eq`
(WholeShape.lean in this folder) that the state after the batching is `batT`; its hypothesis on the
rows taken in comes from `plainRows` by `runRows_plain`
(Johnson/Desc/K12/Honest/Shape/TestDoor.lean). `foldFront_first` (FormFirst.lean), `fold5_yes`
(Johnson/Prover/Link/FormFoldLaws.lean), `getD_of_ok` (Johnson/Prover/Link/BodyYes.lean),
`length_of_foldCut` (Johnson/Prover/Link/FoldCutLen.lean) and `rounds_split`
(Johnson/Desc/K12/Honest/Shape/TestSwitch.lean) give that the state after the first fold (`tFold`,
PlanB.lean) is `foldT` at a first round and k more. The clause `plain` of `ShapeAsks`: `gpOf` does
not read the row; `gpL` reads of it only whether it has a kept form (`gpLS_eq`, TestDoor.lean), and
it has none (`H2K.Pin.combine_noKept0`, Johnson/Desc/K12/Law/BatNoKept.lean); the layout's k and h
are fields of `TestFront` (FormFirst.lean), with `kk_eq` (Johnson/Prover/Link/BodySorts.lean). The
clause on the codes after the first fold: `foldT_keeps` (FormFoldLaws.lean) and `batT_codes`
(TestSwitch.lean). The clause `pub`: `foldOut_says` (Johnson/Prover/Link/FormRooms.lean) gives four
of the five fields and `rounds_split` the fifth, `gamma`, so `readPubB_congr` carries
`FrontAsks.pub` over; `OldOk` (Johnson/Desc/K12/Honest/FirstValues.lean) is the first five clauses
of `FoldedFit` (OnBytes/Slice/BlkProxSeg.lean), which `foldedFit_pure`
(Johnson/Desc/K12/Law/FoldKeeps.lean) gives, from `switchPub_of`
(Johnson/Desc/K12/Honest/Shape/TestSwitchPub.lean), `Own.foldShapeFits_agrees` and
`Own.foldRowFits_agrees` (Johnson/Desc/Own/FoldAgree.lean) and `foldRowFits_spent`
(FormFoldLaws.lean). `dataAsks_of_front` calls `door_facts` and `recB_eq`, and reads `allSay` at
`batT`. `accepts_every_list` calls `formAsks_of_draws`, the two theorems above and
`accepts_of_plan`.

Hypotheses of `accepts_every_list`. hP: `planB` is true at the place, K and the number of trees in
`Dp.ts`. hst: the place's list of stages is a :: next :: rest. Pb: `FormPub J.p a next rest`
(FormDraws.lean): four clauses on the plan. S: `FrontAsks` at K and Dp. Dt: `DataFront` at the coins
C, at Dp, c and R. hd: `drawsFit` is true of the declared rounds and ds; it is false where the two
lists differ in length.

Limits.
- `FrontAsks` and `DataFront` are hypotheses; no value that meets them is given here.
- The state on entry is whatever the job's function `rec₀` returns at w and fr. It is compared with
  nothing here: it is not shown to be the verifier's. The states after the batching and after the
  first fold are computed from it. No honest prover is defined here: the term is `testAll` at any
  job.
- The case in which the first fold sends its own table is not served: `came` asks that the field
  `mask` of the state on entry is `some`.
- `planB` is false at a place with fewer than three stages.
- The coins are a letter: the law holds at each family of coins at which `DataFront` holds; that it
  holds at all coins that a book lends is not shown. Here a letter is a free parameter, C; the law
  is `accepts_every_list`; a book is the frame's book of coins (`ProverCoinCounts`).
- The premises hang on the front: on the input and on the challenges heard in front of the test.
  That is: by type `FrontAsks` reads the prover's input w and the front fr, through `J.rec₀`, and
  `DataFront` reads them and the coins C, through `J.rec₀`, `J.first` and `J.trees₀`.
- `plain`, `pub` and `allSay` are implications: where the statement on entry has no group number g
  they ask nothing. In the proofs the group comes from `door_facts`.
- `plainRows` asks the mark `stPlainB` (Johnson/Desc/Ground/Shape/Marks.lean): no open row and no
  sample row of the statement on entry has a written-out factor. By that file's head, and by no
  theorem, a row with such a factor is placed on the last chain of both files, the proof file and
  the key file. Where the mark fails no value meets `FrontAsks`, and `accepts_every_list` is
  vacuous.
- The conclusion is the decision (`Block.decide`) of the proximity test's own block only; for the
  rest the reach is that of `accepts_of_plan`: see the limits of PlanB.lean. The declared rounds are
  `(laidOf J.p).map (·.1)`: that this is the block's own list of rounds is not shown here.
  EveryAt.lean (not in the library yet) in this folder states the acceptance at the block's own
  list, where the block's `planOk` is true (`accepts_every_rounds`), and carries it into the frame's
  statements.
- Nothing is said at a list of which `drawsFit` is false.
- Nothing on what is left untested after the test.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.FormDraws
import Johnson.Desc.K12.Law.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain
  switchPubB SingleSh door_facts batT_codes rounds_split gpLS_eq)

variable {W X : Type}

/-- The shape of the single rows after the first fold, as far as `readPubB` reads it. L: the layout.
i: the two codes' numbers. k, h: the stage's. id: the fresh table's number. -/
def frontSingle (L : GroupLayout) (i : ℕ × ℕ) (k h id : ℕ) : SingleSh :=
  ⟨i.1, i.2, { L with k := k, h := h }, k, 2, id, 0, [], 0, true, true⟩

theorem readPubB_congr (c : CoreSh) (r r' : SingleSh) (logN : ℕ) (h1 : r.masks = r'.masks)
    (h2 : r.keptRows = r'.keptRows) (h3 : r.gamma = r'.gamma) (h4 : r.lay = r'.lay)
    (h5 : r.fresh = r'.fresh) : readPubB c r logN = readPubB c r' logN := by
  cases r
  cases r'
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

section
variable (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)

/-- The hypotheses on the state on entry, `J.rec₀ w fr`; they name no challenge of the test. The
state is the job's, not shown to be the verifier's. -/
structure FrontAsks (K : Codes) (Dp : Plain) : Prop where
  codes : (J.rec₀ w fr).st.codes = K
  door : Sh.doorB J.p (stA J.p) (stN J.p) (((laidOf J.p).take 1).map (·.1))
    (lettersOf J.p (stA J.p) (stN J.p)).i
    ((lettersOf J.p (stA J.p) (stN J.p)).n.code, (lettersOf J.p (stA J.p) (stN J.p)).n.maskCode)
    (testSh (J.rec₀ w fr)) = true
  came : (J.rec₀ w fr).mask.isSome = true
  tidy : stTidyB (J.rec₀ w fr).st = true
  plainRows : stPlainB (J.rec₀ w fr).st = true
  claims : claimsB (J.rec₀ w fr) = true
  plain : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
    gpOf J.p (batT (J.rec₀ w fr) G {}) (stA J.p) (layoutOf (J.rec₀ w fr).st G) = some Dp ∧
      ok (gpL J.p (stA J.p) {} Dp) = true ∧
      2 ^ (layoutOf (J.rec₀ w fr).st G).logEll = (stA J.p).C.l ∧
      2 ^ (layoutOf (J.rec₀ w fr).st G).logEllZk = (stA J.p).Z.l
  pub : ∀ G id, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
    (J.rec₀ w fr).mask = some id →
    readPubB (coreSh ⟨Ground.withGroup (spent (begun (J.rec₀ w fr).st (J.rec₀ w fr).g G) id)
        (lettersOf J.p (stA J.p) (stN J.p)).n.code (lettersOf J.p (stA J.p) (stN J.p)).n.maskCode,
        (J.rec₀ w fr).book, (J.rec₀ w fr).roots⟩)
      (frontSingle (layoutOf (J.rec₀ w fr).st G) (lettersOf J.p (stA J.p) (stN J.p)).i (stA J.p).k
        (stA J.p).h id) (stA J.p).C.a = true

/-- The hypotheses on the prover's data: `DataAsks` (PlanB.lean) with its last clause at the state
with the group's test begun. They name no challenge of the test. -/
structure DataFront (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows) : Prop where
  cols : ColsAt (stA J.p) Dp c R
  state : StateAt (stA J.p) Dp (J.first w fr C) R
  trees : J.trees₀ w fr C.mem (J.first w fr C) = groupTrees Dp.ts (logAt Dp.book) c
  allSay : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
    AllSay rdE (begun (J.rec₀ w fr).st (J.rec₀ w fr).g G) (runRows (J.rec₀ w fr).st G).toList
      (wordsAt (begun (J.rec₀ w fr).st (J.rec₀ w fr).g G) (layoutOf (J.rec₀ w fr).st G) R)

end

/-- **`ShapeAsks` at the challenges D, from `FrontAsks`, which is on the state on entry.** Of F the
proof uses the clauses `bat` and `fold` only. -/
theorem shapeAsks_of_front (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (hP : planB J.p K Dp.ts.length = true)
    (S : FrontAsks J w fr K Dp) (F : FormAsks J w fr C D) : ShapeAsks J w fr C D K Dp := by
  unfold planB planL at hP
  split at hP
  · rename_i a next nx' rest' hst
    have hA : stA J.p = a := by
      unfold stA
      rw [hst]
      rfl
    have hN : stN J.p = next := by
      unfold stN
      rw [hst]
      rfl
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hP
    obtain ⟨-, -, p3, p4, p5, p6, -⟩ := hP
    obtain ⟨id, hm⟩ := Option.isSome_iff_exists.1 S.came
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s9⟩ := S
    have f1 := F.bat
    have f2 := F.fold
    have s2' := s2
    simp only [hA, hN] at s2' s7 s9 f2
    have Pl := switchPub_of p3
    rw [← s1] at Pl
    obtain ⟨G, row, x, H, hr, eB, -⟩ :=
      door_facts s2' hm s4 (fun G hG => runRows_plain s5 hG) s6 p4 f1
    have eR : J.recB w fr (D 0) = batT (J.rec₀ w fr) G row := (recB_eq J w fr (D 0)).trans eB
    rw [eR] at f2
    have FF := foldFront_first H x row hr
    have hfold := fold5_yes FF p5 _ f2
    have e1 := getD_of_ok (d := batT (J.rec₀ w fr) G row) hfold
    obtain ⟨rE, rR, hrs, hR'⟩ := rounds_split (length_of_foldCut p5) f2
    have hk0 : row.kept = #[] := H2K.Pin.combine_noKept0 _ _ _ _ _ hr fun k => H.noKept k
    have kk : (sgOf a).h + (sgOf a).g = a.k := kk_eq p6
    obtain ⟨q1, q2, q3, q4⟩ := s7 G H.group
    have eT : tFold J w fr C D = foldT (batT (J.rec₀ w fr) G row) row
        (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
          a.h⟩ ((lettersOf J.p a next).n.code, (lettersOf J.p a next).n.maskCode) id
        (rE :: rR) := by
      show t1At J.p _ 0 (stA J.p) (laidS J.p) 1 (J.recB w fr (D 0)) _ D = _
      rw [hA, eR, ← hrs]
      exact e1
    refine ⟨s1, s2, s3, s4, s5, s6, ?_, ?_, ?_⟩
    · -- the plain data
      intro row' L' h
      rw [eR] at h ⊢
      have h' : Passing.claim row (layoutOf (J.rec₀ w fr).st G) = .claim row' L' := h
      injection h' with h1 h2
      subst h1 h2
      rw [hA]
      refine ⟨q1, ?_, H.layK.trans kk.symm, H.layH, q3, q4⟩
      rw [← gpLS_eq, hk0]
      rw [← gpLS_eq] at q2
      exact q2
    · rw [eT]
      exact (foldT_keeps _ _ _ _ _ _ _).1.trans ((batT_codes _ G row).trans s1)
    · -- the single rows
      intro rows gp h
      rw [eT] at h ⊢
      have h' : Passing.single (foldOut (batT (J.rec₀ w fr) G row) row
          (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2,
            a.k, a.h⟩ id (rE :: rR)) (batT (J.rec₀ w fr) G row).st.groups.size =
          .single rows gp := h
      injection h' with h1 h2
      subst h1 h2
      rw [hA, hN]
      obtain ⟨y1, y2, y3, y4⟩ := foldOut_says (batT (J.rec₀ w fr) G row) row
        (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
          a.h⟩ id rE rR
      constructor
      · refine (readPubB_congr _ _ _ _ y1 (y4 fun k => H.noKept k) ?_ y3 y2).trans
          (s9 G id H.group hm)
        show (rR.map drawnOf).length = a.k
        rw [List.length_map]
        exact hR'
      · have hcodes : (batT (J.rec₀ w fr) G row).st.codes = (J.rec₀ w fr).st.codes :=
          batT_codes _ G row
        have Pl' : SwitchPub J.p (batT (J.rec₀ w fr) G row).st.codes 0 a next
            (nx' :: rest').isEmpty ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
              a.h⟩ (lettersOf J.p a next).n (lettersOf J.p a next).dS
            (lettersOf J.p a next).dC := by
          rw [hcodes]
          exact Pl
        have hrow : foldRowOk (spent (batT (J.rec₀ w fr) G row).st id)
            (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
              (layoutOf (J.rec₀ w fr).st G)) row = true :=
          (Own.foldRowFits_agrees _ _ _).trans ((foldRowFits_spent _ _ _ _).trans FF.rowFits)
        have hlen : (rR.map drawnOf).length = a.k := by
          rw [List.length_map]
          exact hR'
        rw [(foldT_keeps _ _ _ _ _ _ _).1]
        obtain ⟨g1, g2, g3, g4, g5, -⟩ := foldedFit_pure (batT (J.rec₀ w fr) G row).st.codes
          (sgOf a) (sgOf next) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
          Pl'.codes (lettersOf J.p a next).n.code (lettersOf J.p a next).n.maskCode Pl'.zk
          Pl'.codeN Pl'.zkN Pl'.small (batT (J.rec₀ w fr) G row).st
          (spent (batT (J.rec₀ w fr) G row).st id) row (layoutOf (J.rec₀ w fr).st G) id
          (drawnOf rE) (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))
          (rR.map drawnOf) rfl rfl hk0 (fun k _ => H.noKept k) (hlen.trans Pl.codes.k)
          ((Own.foldShapeFits_agrees _ _).trans FF.shape) hrow
        exact ⟨g1, g2, g3, g4, g5⟩
  · simp at hP

/-- **`DataAsks` at the challenges D, from `DataFront`.** S and F serve to write out the state after
the batching; of F the proof uses the clause `bat` only. -/
theorem dataAsks_of_front (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : FrontAsks J w fr K Dp)
    (F : FormAsks J w fr C D) (Dt : DataFront J w fr C Dp c R) : DataAsks J w fr C D Dp c R := by
  refine ⟨Dt.cols, Dt.state, Dt.trees, fun row' L' h G' hG' => ?_⟩
  unfold planB planL at hP
  split at hP
  · rename_i a next nx' rest' hst
    have hA : stA J.p = a := by
      unfold stA
      rw [hst]
      rfl
    have hN : stN J.p = next := by
      unfold stN
      rw [hst]
      rfl
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hP
    obtain ⟨-, -, -, p4, -⟩ := hP
    obtain ⟨id, hm⟩ := Option.isSome_iff_exists.1 S.came
    have s2 := S.door
    simp only [hA, hN] at s2
    obtain ⟨G, row, x, H, hr, eB, -⟩ :=
      door_facts s2 hm S.tidy (fun G hG => runRows_plain S.plainRows hG) S.claims p4 F.bat
    have eR : J.recB w fr (D 0) = batT (J.rec₀ w fr) G row := (recB_eq J w fr (D 0)).trans eB
    obtain rfl : G = G' := Option.some.inj (H.group.symm.trans hG')
    rw [eR] at h ⊢
    have h' : Passing.claim row (layoutOf (J.rec₀ w fr).st G) = .claim row' L' := h
    injection h' with h1 h2
    subst h1 h2
    exact Dt.allSay G hG'
  · simp at hP

/-- **At every list that can be sampled the decision accepts all that the term shows.** The term is
`testAll` at the job J, whose functions are the caller's. hd: the list ds can be sampled. -/
theorem accepts_every_list (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (K : Codes)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: rest) (Pb : FormPub J.p a next rest)
    (S : FrontAsks J w fr K Dp) (Dt : DataFront J w fr C Dp c R) (ds : List Fmt.Drawn)
    (hd : drawsFit ((laidOf J.p).map (·.1)) ds = true) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C (byNo ds)).rs.map noDigest) (testAll J w fr C (byNo ds)).gs = .ok t' := by
  have F := formAsks_of_draws J w fr C ds a next rest hst Pb hd
  exact accepts_of_plan J w fr C (byNo ds) K Dp c R hP (shapeAsks_of_front J w fr C _ K Dp hP S F) F
    (dataAsks_of_front J w fr C _ K Dp c R hP S F Dt)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.readPubB_congr
#print axioms ProofFile.Honest.K12.shapeAsks_of_front
#print axioms ProofFile.Honest.K12.dataAsks_of_front
#print axioms ProofFile.Honest.K12.accepts_every_list
#print axioms ProofFile.Honest.K12.frontSingle
#print axioms ProofFile.Honest.K12.FrontAsks
#print axioms ProofFile.Honest.K12.DataFront
