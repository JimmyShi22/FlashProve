-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FirstTest.lean: one test with code, `firstB`, whose "true" gives all the
hypotheses of `hy_atFirst_rows` (Johnson/Desc/K12/Honest/FirstRows.lean), the theorem on what the
first code switch of a proximity test reads, at plain rows. It is written so that these hypotheses
can be checked together at a value by an evaluation. The main theorem, `hy_atFirst_test`, has the
test's "true" as its only hypothesis and holds at every value of the test's parameters. Definitions
with code, and theorems with their proofs. It does not depend on the frame for an honest side
(Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list: p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the place of the test. a
and next (`Fmt.M1.Stage`) are the first and the second stage, rest the stages after them. `sg a`
(Johnson/Desc/K12/Law/FirstOkLaw.lean) and `sgOf a` (Johnson/Desc/K12/Law/ChainOf.lean) are the
sizes of a in the library's form (`Sg`): the codes C and Z, the numbers h and g = k - h, and the
number of positions. t (`T12`, Johnson/Desc/K12/Join.lean) is the state inside the test before the
first fold; its field `pass` is what one part of the test passes to the next. K (`BCoins`,
Johnson/Prover/Link/BodyAll.lean), P (`PS`, Johnson/Prover/Link/BodyState.lean) and D are parameters
of the pieces named next; D n is what round number n samples, and o is the number of the stage's
first round. The pieces (Johnson/Desc/K12/Honest/FirstYes.lean and Stages.lean in the same folder),
written here without their arguments: `rfAt` and `rsAt` are the fold's and the switch's rounds,
`aGroups` the groups of opened columns, and `t1At`, `aRec2` and `t3At` the states after the fold,
after the switch, and after the batching that follows the switch (where a part rejects, the state
before it is kept). Dp (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean) are the plain data of the group
under test: among them a book (`TreeBook`, OnBytes/Iop/Ground.lean: the trees, and for each oracle
message its tree and its part of that tree), the group's members `mems` and the fresh table `fresh`,
each an oracle message as a part of a tree (`Seat1`), and the places `ts` of their trees. A tree's
place is its index in `book.trees`. c u x is the column, a list of words, of the tree at the place u
at the position x. R (`PlainRows`, FirstRows.lean) are the prover's rows as plain functions of
numbers.

  `hy_atFirst_test`: where `firstB p K rest a next o t P D c R` is true, there are `row`, `L`, `Dp`,
    a proof `hok` that Dp passes `gpL`, and `nx` such that t passes the claim of `row` with the
    layout `L`, `gpOf p t a L` returns Dp, `stageAt p 1 next` returns `nx`, and the conclusion of
    `hy_atFirst_rows` holds at these, at the declared rounds `laidS p`
  `firstB`: a definition: the test. It is false unless t passes a claim and `gpOf` (FirstOk.lean)
    returns plain data Dp. Then it asks, in this order: `p.early`; `p.answers = 1`; every clause of
    `gpL` (FirstOk.lean) at Dp; `a.h ≤ a.k`; `sizedB a`; `stageAt` (Join.lean) returns a stage cu
    for a as stage number 0, and in the statement of `t1At` the base code number `cu.code` has
    `logN = a.C.a`; `stageAt` returns a stage for next as stage number 1; `colsB`; `firstYesB` at
    stage number 0 and at the trees `groupTrees Dp.ts (logAt Dp.book) c`
    (Johnson/Desc/K12/Honest/GroupState.lean); the positions that round number o + 2 + (h + g)
    samples are all below `2 ^ a.C.a`; they are `a.t` many. The declared rounds are `laidS p`
    (Johnson/Desc/K12/Law/ReadsK.lean) throughout: the place's declared rounds, each with its oracle
    messages, after the first round, "BAT"
  `firstYesB`, `firstYes_of`: a definition: `FirstYes` (FirstYes.lean) as a test, field by field.
    The decisions of the fold, of the switch and of the batching after it (parts of `guardedProximityTestParts`,
    Johnson/Desc/K12/JoinGuarded.lean) return a state (`Except.isOk`): the fold's from t on `rfAt`, the
    switch's from `t1At` on `rsAt` with `aGroups`, the batching's from `aRec2` on no round and no
    group; the rounds are taken without their digests (`noDigest`, Johnson/Desc/Block.lean).
    `p.early` is false or `guardedProximityTestParts.maskCame` is true at `t3At`. The fold's block (`foldAt`,
    Johnson/Desc/K12/FrameLaws.lean) has 1 + (h + g) rounds and no opening; the switch's
    (`switchAt`, same file) has two rounds and as many openings as there are trees. The theorem: its
    "true" gives `FirstYes`. Both at every stage number j, all declared rounds l and every list of
    trees
  `colsB`, `memB`, `colsAt_of`: definitions: `ColsAt` and `MemAt` (FirstRows.lean) as tests. `colsB`
    runs over every position of every tree: at every place in `Dp.ts` the column has the width that
    the book states (`widthAt`, FirstOk.lean); `memB` at every member; the symbols of the fresh
    table's rows, `2 ^ a.h` many, are in its tree's column. `memB` is on one member's rows at one
    position: the symbols (`symG`, Johnson/Prover/Link/Base.lean) of its main rows and of its mask
    rows are in the column, from the offsets `skM` and `skZ` (FirstOk.lean) on. The theorem: the
    "true" of `colsB` gives `ColsAt`
  `sizedB`, `sized_of`: a definition: the four clauses of `Sg.Sized` (OnBytes/Slice/Numbers.lean) on
    the two codes of a stage, as a test. The theorem: its "true" gives `(sg a).Sized`
  `sameE`, `same_of`: a definition: whether two elements of the extension field (`GE`) are written
    as the same three words (`ofE`, OnBytes/Slice/Field.lean). The theorem: its "true" gives that
    the two are equal
  `ok_of`, `all_range`: lemmas: `Except.isOk x = true` gives a y with `x = .ok y`;
    `(List.range n).all f = true` gives `f i = true` at every i below n

By what. `hy_atFirst_test` unfolds `firstB`, takes its cases and its clauses apart and calls
`hy_atFirst_rows` (FirstRows.lean) at l := `laidS p`; `sized_of`, `colsAt_of` and `firstYes_of` turn
three of the clauses into the propositions that this theorem takes. `colsAt_of` goes by `all_range`,
`same_of` and `mem_zipIdx_get` (Johnson/Desc/K12/Law/FirstOkLaw.lean). `same_of` applies `toE` to
both sides and rewrites by `toE_ofE` (OnBytes/Slice/Field.lean).

Limits.
- A "true" of the test at a value is an evaluation by Lean's evaluator, outside the kernel; the
  statements here are theorems. Such an evaluation leaves no theorem: it does not prove the
  hypothesis of `hy_atFirst_test`. Nothing is evaluated in this file, and it gives no value at which
  the test is true. Evaluations by `#guard`, at small made-up places:
  Johnson/Desc/ProofFile/Honest/K12/ToyGroup.lean.
- The test runs over all positions of all the group's trees: it is for small sizes.
- Only the direction from "true" to the hypotheses is proved. That the test is true wherever the
  hypotheses hold is not stated.
- The conclusion is that of `hy_atFirst_rows`, with its limits (FirstRows.lean). Among them: at a
  stage that samples no position its last clause is vacuous.
- t is a free parameter: that it is a state that a verifier reaches is not stated.
- The test reads the columns c, the rows R and the parameters K, P and D. Of the clauses that
  Johnson/Desc/K12/Honest/FirstReads.lean calls public, the one at `t1At` reads K, P and D too.
- `firstB` is the short name of two tests. This one, `ProofFile.Honest.K12.firstB`, runs the parts'
  decisions. `ProofFile.Honest.Sh.firstB` (Johnson/Desc/K12/Honest/Shape/TestSwitchPub.lean) is another
  test, on a shape, the place's numbers and declared rounds.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.FirstRows
import Johnson.Desc.K12.Law.ReadsK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-! ## Tools -/

theorem ok_of {α : Type} {x : Except String α} (h : Except.isOk x = true) : ∃ y, x = .ok y := by
  cases x with
  | ok y => exact ⟨y, rfl⟩
  | error _ => cases h

/-- Whether two elements of the extension field are written as the same three words (`ofE`). -/
def sameE (x y : GE) : Bool := decide (ofE x = ofE y)

theorem same_of {x y : GE} (h : sameE x y = true) : x = y := by
  have e := congrArg toE (of_decide_eq_true h)
  rwa [toE_ofE, toE_ofE] at e

theorem all_range {n : ℕ} {f : ℕ → Bool} (h : (List.range n).all f = true) (i : ℕ) (hi : i < n) :
    f i = true := List.all_eq_true.1 h i (List.mem_range.2 hi)

/-! ## The acceptances -/

section Yes
variable (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (j : ℕ) (cur next : Fmt.M1.Stage)
  (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree) (D : ℕ → Fmt.Drawn)

/-- `FirstYes` as a test, in the order of the structure's fields: `Except.isOk` of the three
decisions, the clause on `maskCame`, and `decide` of the four equations on numbers of rounds and of
openings. -/
def firstYesB : Bool :=
  Except.isOk ((guardedProximityTestParts.fold p j cur ((l.take (1 + cur.k)).map (·.1))).decide t
    ((rfAt K j cur o t P D).map noDigest) []) &&
  Except.isOk ((guardedProximityTestParts.switch p j cur next rest.isEmpty
    (((l.drop (1 + cur.k)).take 2).map (·.1))).decide (t1At p K j cur l o t P D)
    ((rsAt p K rest j cur next l o t P D).map noDigest) (aGroups cur o trees D)) &&
  Except.isOk ((guardedProximityTestParts.batBehind p (j + 1) next (((l.drop (1 + cur.k)).take 2).map (·.1))).decide
    (aRec2 p K rest j cur next l o t P trees D) [] []) &&
  (!p.early || guardedProximityTestParts.maskCame (t3At p K rest j cur next l o t P trees D)) &&
  decide ((foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length =
    1 + ((sgOf cur).h + (sgOf cur).g)) &&
  decide ((foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings = 0) &&
  decide ((switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).rounds.length = 2) &&
  decide ((switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).openings = trees.length)

theorem firstYes_of (h : firstYesB p K rest j cur next l o t P trees D = true) :
    FirstYes p K rest j cur next l o t P trees D := by
  simp only [firstYesB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨ok_of h1, ok_of h2, ok_of h3, h4, h5, h6, h7, h8⟩

end Yes

/-! ## The prover's data -/

/-- `MemAt` as a test: one member's rows at one position. s: the member, as a part of a tree. j: the
member's number. x: the position; the column is `c s.t x`. -/
def memB (a : Fmt.M1.Stage) (c : ℕ → ℕ → List UInt64) (R : PlainRows) (s : Seat1) (j x : ℕ) :
    Bool :=
  ((List.range s.sh.mainRows).all fun i =>
    sameE (if s.sh.mainDeg == 1 then read1 (c s.t x) (skM s.tsh s.part + i)
      else read3 (c s.t x) (skM s.tsh s.part + 3 * i)) (symG a.C x (R.M j i) (R.T j i))) &&
  (List.range s.sh.maskRows).all fun i =>
    sameE (read3 (c s.t x) (skZ s.tsh s.part + 3 * i))
      (symG a.Z (x % 2 ^ a.Z.a) (R.Z j i) (R.ZT j i))

/-- `ColsAt` as a test, over every position of every tree. The widths; the members' rows; the fresh
table's. -/
def colsB (a : Fmt.M1.Stage) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows) : Bool :=
  (Dp.ts.all fun u => (List.range (2 ^ logAt Dp.book u)).all fun x =>
    decide ((c u x).length = widthAt Dp.book u)) &&
  (Dp.mems.zipIdx.all fun s => (List.range (2 ^ s.1.tsh.logN)).all fun x =>
    memB a c R s.1 s.2 x) &&
  (List.range (2 ^ Dp.fresh.tsh.logN)).all fun x => (List.range (2 ^ a.h)).all fun b =>
    sameE (read3 (c Dp.fresh.t x) (skZ Dp.fresh.tsh Dp.fresh.part + 3 * b))
      (symG a.Z (x % 2 ^ a.Z.a) (R.F b) (R.FT b))

/-- The test's "true" gives `ColsAt`. -/
theorem colsAt_of {a : Fmt.M1.Stage} {Dp : Plain} {c : ℕ → ℕ → List UInt64} {R : PlainRows}
    (hB : colsB a Dp c R = true) : ColsAt a Dp c R := by
  simp only [colsB, Bool.and_eq_true] at hB
  refine ⟨fun u hu x hx => of_decide_eq_true (all_range (List.all_eq_true.1 hB.1.1 u hu) x hx),
    fun j x hx => ?_, fun x hx b hb => same_of (all_range (all_range hB.2 x hx) b hb)⟩
  have h := all_range (List.all_eq_true.1 hB.1.2 _ (mem_zipIdx_get Dp.mems j)) x hx
  simp only [memB, Bool.and_eq_true] at h
  exact ⟨fun i hi => same_of (all_range h.1 i hi), fun i hi => same_of (all_range h.2 i hi)⟩

/-! ## The test -/

/-- The stage's sizes are in order: the four clauses of `Sg.Sized` at the stage's two codes, as a
test. -/
def sizedB (a : Fmt.M1.Stage) : Bool :=
  decide (a.C.a ≤ 32) && decide (a.Z.a ≤ a.C.a) && decide (a.C.r + a.C.l ≤ 2 ^ a.C.a) &&
    decide (a.Z.r + a.Z.l ≤ 2 ^ a.Z.a)

theorem sized_of {a : Fmt.M1.Stage} (h : sizedB a = true) : (sg a).Sized := by
  simp only [sizedB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The test. False unless t passes a claim and `gpOf` returns plain data Dp. Then the conjunction
of tests for the hypotheses of `hy_atFirst_rows`, at the declared rounds `laidS p`. -/
def firstB (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage) (o : ℕ)
    (t : T12) (P : PS) (D : ℕ → Fmt.Drawn) (c : ℕ → ℕ → List UInt64) (R : PlainRows) : Bool :=
  match t.pass with
  | .claim row L =>
    match gpOf p t a L with
    | some Dp =>
      p.early && decide (p.answers = 1) && ok (gpL p a row Dp) && decide (a.h ≤ a.k) && sizedB a &&
      (match stageAt p 0 a with
        | some cu => decide (((t1At p K 0 a (laidS p) o t P D).st.codes.base[cu.code]?).map
            (·.logN) = some a.C.a)
        | none => false) && (stageAt p 1 next).isSome &&
      colsB a Dp c R &&
      firstYesB p K rest 0 a next (laidS p) o t P (groupTrees Dp.ts (logAt Dp.book) c) D &&
      ((D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss.all fun x => decide (x < 2 ^ a.C.a)) &&
      decide ((D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss.length = a.t)
    | none => false
  | _ => false

/-- **The test's "true" gives what the first switch reads.** The conclusion of `hy_atFirst_rows` at
l := `laidS p`. The claim's row and layout, the plain data, the proof that they pass `gpL`, and the
second stage in the program's form are among the things that are stated to exist. -/
theorem hy_atFirst_test (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (o : ℕ) (t : T12) (P : PS) (D : ℕ → Fmt.Drawn) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hB : firstB p K rest a next o t P D c R = true) :
    ∃ (row : GroupRow) (L : GroupLayout) (Dp : Plain) (hok : ok (gpL p a row Dp) = true)
      (nx : IoppStage) (rows : SingleRows) (gp : ℕ) (out : Switched) (row' : GroupRow)
      (lay' : GroupLayout) (theta : E) (Dk : Taken),
      t.pass = .claim row L ∧ gpOf p t a L = some Dp ∧ stageAt p 1 next = some nx ∧
      (t1At p K 0 a (laidS p) o t P D).pass = .single rows gp ∧
      Did p.nums.firstTree
        (keyed p ((((laidS p).drop (1 + a.k)).take 2).map (·.1))
          (aGroups a o (groupTrees Dp.ts (logAt Dp.book) c) D)) rows
        (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) gp (othersOf rest.isEmpty nx)
        (t1At p K 0 a (laidS p) o t P D).st (t1At p K 0 a (laidS p) o t P D).book
        (t1At p K 0 a (laidS p) o t P D).roots
        (t3At p K rest 0 a next (laidS p) o t P (groupTrees Dp.ts (logAt Dp.book) c) D).st
        (t3At p K rest 0 a next (laidS p) o t P (groupTrees Dp.ts (logAt Dp.book) c) D).book out
        row' lay' theta Dk ∧
      (t3At p K rest 0 a next (laidS p) o t P (groupTrees Dp.ts (logAt Dp.book) c) D).pass =
        .claim row' lay' ∧
      (∀ (Qs : Fin (sg a).t → (sg a).Ps),
        (∀ i, (Qs i).val = Dk.rC.drawn.poss.getD i.val 0) →
        ∀ i α, (sg a).cMid.T ((sg a).cMid.enc
            (foldMsg (sg a) (layJ (GroupAt hok) (msgsOf R hok)) (freshOf R (sg a)) (aPoint a o D))
            (foldTl (sg a) (layQ (GroupAt hok) (tailsOf R hok)) (freshTlOf R (sg a))
              (aPoint a o D)))
            (Qs i) α = symS (sg a) rows out.positions Dk.y (Qs i).val α) := by
  unfold firstB at hB
  cases hp : t.pass with
  | claim row L =>
    simp only [hp] at hB
    cases hD : gpOf p t a L with
    | none => simp [hD] at hB
    | some Dp =>
      simp only [hD, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hB
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨he, h1⟩, hok⟩, hhk⟩, hs⟩, hcd⟩, hnx⟩, hC⟩, hY⟩, hr⟩, ht⟩ := hB
      obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.1 hnx
      cases hcu : stageAt p 0 a with
      | none => simp [hcu] at hcd
      | some cu =>
      simp only [hcu, decide_eq_true_eq] at hcd
      obtain ⟨rows, gp, out, row', lay', theta, Dk, e⟩ := hy_atFirst_rows p K rest a next (laidS p)
        o t P D he h1 rfl row L hp Dp hD hok hhk (sized_of hs) cu nx hcu hnx hcd c R (colsAt_of hC)
        (firstYes_of _ _ _ _ _ _ _ _ _ _ _ _ hY) hr ht
      exact ⟨row, L, Dp, hok, nx, rows, gp, out, row', lay', theta, Dk, rfl, hD, hnx, e⟩
  | _ => simp [hp] at hB

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.ok_of
#print axioms ProofFile.Honest.K12.same_of
#print axioms ProofFile.Honest.K12.all_range
#print axioms ProofFile.Honest.K12.firstYes_of
#print axioms ProofFile.Honest.K12.colsAt_of
#print axioms ProofFile.Honest.K12.sized_of
#print axioms ProofFile.Honest.K12.hy_atFirst_test
#print axioms ProofFile.Honest.K12.sameE
#print axioms ProofFile.Honest.K12.firstYesB
#print axioms ProofFile.Honest.K12.memB
#print axioms ProofFile.Honest.K12.colsB
#print axioms ProofFile.Honest.K12.sizedB
#print axioms ProofFile.Honest.K12.firstB
