-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestReturnsOne.lean: a proximity test's block returns, whole, from the
shape in front, where the group's members and the first fold's mask stand in one tree and the mask
has come: at any rounds and columns of the declared form. In Lean: under the fourteen hypotheses of
`k12_returns_one` the decision of the test's block (`proximityTestKind`, Johnson/Desc/K12/Frame.lean, at the parts
`guardedProximityTestParts`, Johnson/Desc/K12/JoinGuarded.lean) returns `.ok`; below: "the block accepts". The whole block
is its front, its batching, the question whether the group is the first stage's, and its stages;
TestReturns.lean in this folder treats the stages only. One hypothesis, on `ValsFrom`, is on the
values of the test's own rounds and columns. Two theorems, no definition; general in the place, the
structure before the test, the rounds and the columns. The verifier's structure alone: no prover, no
coin, no frame for an honest side. (That frame is Johnson/Desc/ProofFile/Honest/Frame.lean.)

In the list and below: a file that is named without a folder is in this folder, and Link/ is short
for Johnson/Prover/Link/. p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the place of a
test: the plan. Among them are its stages (`Fmt.M1.Stage`); cur and nxt are the first two. A part
(`Part`, same file) is a piece of the test with a decision of its own: the front, which has no
round; the batching; at each stage but the last a fold, a switch and a batching after it; at the
last stage the base case. t (`T12`, Johnson/Desc/K12/Join.lean) is the verifier's structure inside a
test, here before the front: a statement `t.st`, a book of trees `t.book`, a count of roots
`t.roots`, the number `t.g` of the group under test, and `t.mask`, the number of the message that
holds the first fold's mask, if it has come. "Mask" is the library's name for a message: nothing is
said of what a mask does. The members of the group G (`Group`) are numbers of messages of the
statement. The shape of t is `testSh t` (Test.lean). `laidOf p` (Johnson/Desc/K12/Law/ReadsK.lean)
lists the place's declared rounds, each with its oracle messages: the first is the batching's, and
`laidS p`, the rest, are the stages'. The view is here the rounds (`Fmt.RoundView`) and the groups of
columns that a decision takes as arguments; a column is a position with a list of words. `noDigest`
(Johnson/Desc/Block.lean) sets the field `drawn.digest` of a round to `none`. `batT t G row`
(Link/FormFirst.lean) is t after the batching: its statement is `begun t.st t.g G`
(OnBytes/Slice/BlkBegin.lean), and it passes on the claim row with the group's layout.

  `k12_returns_one`: under the fourteen hypotheses below there is a structure t' such that the
    block's decision at t, the rounds `(rB :: R).map noDigest` and the groups of columns gs returns
    `.ok t'`. rB is the batching's round; R and gs are the stages' rounds and groups of columns
  `formInv_of_shape`: the form's half of the stages' invariant (`FormInv`, Link/FormInv.lean) at the
    first stage, after the batching, all thirteen fields. Under `TestFront` (Link/FormFirst.lean: a
    structure of twenty hypotheses), the count of roots (`p.nums.free = t.roots`), the test `seat1B`
    (TestSeat.lean) and `cur.h ≤ cur.k`: there is a tree tr such that `FormInv` holds at stage
    number 0 and `batT t G row`, for every element θ, every row that `Bat.combine` returns at θ, and
    every column function col of the width of tr. Some fields repeat a hypothesis (`layH`, `roots`,
    `width`). `TestFront`, the count of roots and h ≤ k are hypotheses here: only `k12_returns_one`
    derives them from tests

By what. `k12_returns_one` splits `doorB` into its four conjuncts. From the first and the fourth,
with hm, ht and hp, `testFront_of` (TestDoor.lean) gives the group G and `TestFront`. From the
second, `batOwes_of` (same file) gives `BatOwes` (Link/FormBat.lean). From the third, with hv,
`frontOwes_of` (same file) gives `FrontOwes` (Link/FormDoor.lean), whose field `roots` is the count
of roots. By `front5_yes` (Link/FormDoorLaws.lean) the front accepts and returns t; by `bat5_yes`
(Link/FormBatLaws.lean) the batching accepts and returns `batT t G row`; by `group_batT` (same file)
the group is the first stage's. `planFrom_of_ok` (Link/StepPlanOk.lean) gives `PlanFrom`
(Link/FormStepPlan.lean), and with it h ≤ k at cur (`StepPlan.hk`). By `begun_codes`
(OnBytes/Slice/BlkLinkHead.lean) the codes after the batching are those of t, so `PlanFrom` holds at
them too. `formInv_of_shape` gives `FormInv`; it is taken at a column function of zero words, of
which `FormInv` reads the length only. `viewFrom_of_B` (TestView.lean) gives `ViewFrom`, and
`stages_returns` (TestReturns.lean) the stages' accept. `k12_yes` (Link/TestYes.lean) joins the
front's accept, the batching's, the answer on the group and the stages' accept; `laid_cons`
(Link/LinkJoinD.lean) shows that the batching has one round and no opening. `formInv_of_shape` calls
`seat1_of_B` (TestSeat.lean), `foldFront_first` (Link/FormFirst.lean), `ReadSeat.begun`
(Link/ReadRide.lean), `combine_noKept0` (Johnson/Desc/K12/Law/BatNoKept.lean), `combine_dense`
(OnBytes/Slice/BlkProxDense.lean), `InOrder.begun` (Johnson/Desc/Means/Order.lean) and `begun_sizes`
(OnBytes/Slice/BlkProxKeeps.lean).

Hypotheses of `k12_returns_one`: what kind each of the fourteen is.
- Equations on the plan: the stages are cur, nxt and rest (hst; redundant: `planFromOk` has it as a
  clause); the place has declared rounds (hrd: `H2U.roundsOfNums`,
  Johnson/Desc/K12/TestEntries.lean, returns a list); it has oracle messages (hor:
  `H2U.testOracles`, same file, returns a list).
- An equation on the structure: it names the first fold's mask. (hm: `t.mask = some id`.)
- Tests with code on the shape, the plan or the view: `doorB`, `seat1B`, `batCut`, `planFromOk`,
  `roundsFit`, `viewFromB`. A test with code is a definition of type `Bool`. h: `doorB`
  (TestDoor.lean) at the shape of t. The door of a test is its front, its batching, the question on
  the group and its first fold; with the marks, `doorB` gives `TestFront` and the count of roots.
  hs: `seat1B` (TestSeat.lean): the group's members and then the message id are all the parts of the
  tree at place tN of the book; its other clauses are listed in that file. hB: `batCut`
  (Link/FormBat.lean) at the batching's declared round. hP: `planFromOk` (Link/StepPlanOk.lean), the
  plan's test from the first stage on, at the codes of t. fB: `roundsFit` (Johnson/Desc/Block.lean)
  at the batching's declared round and rB. hV: `viewFromB` (TestView.lean) at the stages' declared
  rounds, R and gs.
- Three marks on the structure in front, which read the open rows' summands, left out of the shape:
  the first mark (`stTidyB`), which reads values at one spot; "the rows taken in have no written-out
  factor"; the front's named test on the open rows (`claimsB`), which is a test on values: three of
  its clauses read the rows' coefficients (TestDoor.lean). (ht, hp, hv. `stTidyB` is in
  Johnson/Desc/Ground/Shape/Marks.lean, whose head names the spot.)
- On the values of the test's own rounds and columns: `ValsFrom` alone. (hvals: for the group G
  under test and the row that `Bat.combine` returns at the element that rB drew (`drawnOf`,
  Link/FormFold.lean): `ValsFrom`, the base case's test on values (TestReturns.lean), at
  `batT t G row`, `R.map noDigest` and gs.)
The parameters i, n, id and tN are free, and each is tied by a clause: i and n to `p.idx[0]?` and
`p.idx[1]?` in `doorB`, id by hm, tN in `seat1B`.

Limits.
- One tree, and the mask has come: a group whose members stand in several trees, and a first fold
  that sends its own mask, are not served; the tree must be opened at no list yet. In Lean: the
  clauses `T.parts == G.members ++ [id]` and `T.lists == 0` of `seat1B`; hm, and `cameB` in `doorB`;
  `!p.nums.ownMask` in `planFromOk`.
- The reach, in numbers: of the eight places of a proximity test at the full size (four of a proof
  file, four of a key file) the first switch opens one tree at two: the proof file's last test after
  the links (`piLFull`, Johnson/Desc/K12/Law/PlacesFull.lean: the first chain's finish; its
  `place.link` is `none`) and the key file's test on the ranges: at most these two can be served.
  The numbers of trees are evaluated in Johnson/Desc/ProofFile/Honest/K12/Sim/ReachAt.lean
  (`opensOf`: one at these two, two or three at the other six), at the library's closed terms for
  the eight places; that these terms are the places of a file is no theorem. That `opensOf` reads
  the declared round that `seat1B` reads is by reading: no theorem.
- No instance of `k12_returns_one` at `piLFull` is stated in Lean. None at the ranges' test is in
  this library.
- The link's own protocol has a proximity test of its own (`p12Of frP`; `p12Of`:
  Johnson/Desc/K15/HsemSays.lean; `frP`: Johnson/Desc/K15/TypedP.lean): a ninth place. No instance
  of `k12_returns_one` is stated there.
- "The declared form" is `roundsFit` and `viewFromB`, not the library's test on a block's view
  (`Block.Fits`, Johnson/Top/H0/StepLaws/StepLaws.lean): from that test to these leads
  `view_of_fits` (TestFits.lean), under tests on the plan.
- No written-out factor in the rows taken in: hp asks `PlainRow` (OnBytes/Slice/BlkPlain.lean) of
  every row of `runRows` (OnBytes/Slice/BlkBegin.lean). A test that takes in a row with such a
  factor is not served.
- No values that meet the fourteen hypotheses together are given in this file.
- What structure the block returns is not said: `k12_returns_one` states only that there is one.
- The place has two stages or more (hst). `doorB`, through `batOwesB`, and `planFromOk` ask
  `p.early`, the place's flag "the masks come early".
- The theorem is on the block's `decide`: the block's own test on the plan (`planOk`) is not
  treated. That the hypotheses are necessary is not shown here.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestSeat
import Johnson.Desc.K12.Honest.Shape.TestView
import Johnson.Prover.Link.StepPlanOk
import Johnson.Prover.Link.ReadRide
import Johnson.Prover.Link.TestYes
import Johnson.Prover.Link.LinkJoinD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open H2K.JointK (laidOf laidS)

/-- The form's half of the invariant at the first stage, after the batching: `FormInv` at stage
number 0 and `batT t G row`, under `TestFront`, the count of roots, the test `seat1B` and h ≤ k. θ:
any element. row: what `Bat.combine` returns at θ. col: any column function of the width of the tree
tr. -/
theorem formInv_of_shape {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {G : Group} {i n : ℕ × ℕ}
    {id tN : ℕ} {l : Laid} (H : TestFront p cur nxt t G i n id) (hr0 : p.nums.free = t.roots)
    (hs : seat1B cur l (coreSh ⟨t.st, t.book, t.roots⟩) t.g id tN = true) (hk : cur.h ≤ cur.k) :
    ∃ tr : Tree, ∀ (θ : E) (row : GroupRow),
      Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩ θ = some row →
      ∀ col : ℕ → List UInt64, (∀ x, (col x).length = tr.shape.mainWidth + tr.shape.maskWidth) →
      FormInv p 0 cur l (batT t G row) col row (layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ n id tN
        tr := by
  obtain ⟨e0, tr, hS, hlog, hdecl⟩ := seat1_of_B hs H.group
  refine ⟨tr, fun θ row hc col hcol => ?_⟩
  exact
    { front := foldFront_first H θ row hc
      kept0 := H2K.Pin.combine_noKept0 _ _ _ _ _ hc fun j => H.noKept j
      keptL := fun j _ => H.noKept j
      layK := by
        show (layoutOf t.st G).k = cur.h + (cur.k - cur.h)
        rw [H.layK]
        omega
      layH := H.layH
      dense := combine_dense _ _ _ _ _ H.dense hc
      order := H.order.begun t.g G H.group
      step := by
        show (begun t.st t.g G).oracles.size = t.book.place.size
        rw [(ProxRun.begun_sizes _ _ _).1]
        exact e0
      roots := by
        show t.roots = p.nums.free + 0
        exact hr0.symm
      seat := hS.begun t.g G
      log := hlog
      decl := hdecl
      width := hcol }

/-- **The block returns, whole, from the shape in front**: one tree at the first stage; the mask has
come. rB: the batching's round. R, gs: the stages' rounds and groups of columns. The file's head
says what kind each of the fourteen hypotheses is. -/
theorem k12_returns_one {p : P12} {cur nxt : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {t : T12}
    {i n : ℕ × ℕ} {id tN : ℕ} {ds : List Fmt.DeclaredRound} {os : List (List (ℕ × ℕ))}
    (hst : p.nums.stages = cur :: nxt :: rest) (hrd : H2U.roundsOfNums p.nums = some ds)
    (hor : H2U.testOracles p.nums = some os)
    (h : doorB p cur nxt (((laidOf p).take 1).map (·.1)) i n (testSh t) = true)
    (hm : t.mask = some id) (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true)
    (hs : seat1B cur (laidS p) (coreSh ⟨t.st, t.book, t.roots⟩) t.g id tN = true)
    (hB : batCut (((laidOf p).take 1).map (·.1)) = true)
    (hP : planFromOk p (nxt :: rest) 0 cur (laidS p) t.st.codes = true)
    (rB : Fmt.RoundView) (fB : roundsFit (((laidOf p).take 1).map (·.1)) [rB] = true)
    (R : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hV : viewFromB (nxt :: rest) cur (laidS p) R gs = true)
    (hvals : ∀ G row, t.st.groups[t.g]? = some G →
      Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩
        (drawnOf (noDigest rB)) = some row →
      ValsFrom p (nxt :: rest) 0 cur (laidS p) (batT t G row) (R.map noDigest) gs) :
    ∃ t', (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t ((rB :: R).map noDigest) gs = .ok t' := by
  unfold doorB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h4' : (match t.mask with
    | some id => cameB cur (testSh t).core t.g i id
    | none => (testSh t).core.st.oracles.length == (testSh t).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFront_of h1 hm h4' ht hp
  have B := batOwes_of h2 H.group
  have F := frontOwes_of h3 hv H.group
  obtain ⟨row, hr, hb⟩ := bat5_yes H _ B hB [rB] fB
  have hf := front5_yes B.pass H.group F
  have PF := planFrom_of_ok p _ _ _ _ _ hP
  have hk : cur.h ≤ cur.k := by
    obtain ⟨⟨_, _, _, _, Pl⟩, -⟩ := PF
    exact Pl.hk
  obtain ⟨tr, hI⟩ := formInv_of_shape H F.roots hs hk
  have I := hI _ row hr (fun _ => List.replicate (tr.shape.mainWidth + tr.shape.maskWidth) 0)
    (fun _ => List.length_replicate)
  have PF' : PlanFrom p (nxt :: rest) 0 cur (laidS p) (batT t G row).st.codes := by
    show PlanFrom p (nxt :: rest) 0 cur (laidS p) (begun t.st t.g G).codes
    rw [begun_codes]
    exact PF
  obtain ⟨tE, hE⟩ := stages_returns p rest 0 cur nxt (laidS p) (batT t G row) _ row _ _ _ id tN tr
    R gs PF' I (viewFrom_of_B _ _ _ _ _ hV) (hvals G row H.group hr)
  have ez : ds.zip p.oracles = laidOf p := by
    unfold H2K.JointK.laidOf
    rw [hrd]
    rfl
  obtain ⟨a, hl, ha1, ha2⟩ := laid_cons _ hB
  have q1 : (batAt guardedProximityTestParts p (laidOf p) : Block T12 Unit).rounds.length = 1 := by
    show (((laidOf p).take 1).map (·.1)).length = 1
    rw [hl]
    rfl
  have q2 : (batAt guardedProximityTestParts p (laidOf p) : Block T12 Unit).openings = 0 := by
    show (((laidOf p).take 1).map (·.1)).foldl
      (fun n r => n + r.stored.length + r.opens.length) 0 = 0
    rw [hl]
    show 0 + a.1.stored.length + a.1.opens.length = 0
    rw [ha1, ha2]
    rfl
  refine ⟨tE, k12_yes guardedProximityTestParts p cur (nxt :: rest) ds os t t (batT t G row) tE _ _ hst hrd hor hf
    ?_ (group_batT H row) ?_⟩
  · rw [ez, q1, q2]
    exact hb
  · rw [ez, q1, q2]
    exact hE

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.formInv_of_shape
#print axioms ProofFile.Honest.Sh.k12_returns_one
