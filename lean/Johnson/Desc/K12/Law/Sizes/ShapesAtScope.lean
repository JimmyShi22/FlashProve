-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/ShapesAtScope.lean: the three oracle messages of a proof's shared chain
(the folded row's, Omega's, the split's) and the sizes of the two lists of codes, as the planner
lays them: first general, off the planner's own text; then at the full size, as far as two tests on
a member of a proximity test's group read them. Definitions, statements and proofs.

Why. The test on a member's site (`siteL`, Johnson/Desc/K12/Law/SiteOk.lean) and the test on its
sample read of the member's shape: whether it has main rows, mask rows or both; the degree of its
main rows; its number of answers; and, for the kind of rows that it lacks, the code at the number
that the shape names. That no message of the three has rows of both kinds, and that the idle number
lies beyond the list, had stood on a run's print.
Main names.
  `linRowsOf_pos`: a message that holds an entry has a row.
  `linFinish_shapes`: THE THREE SHAPES, WHOLE, as `linFinish`
    (OnBytes/Params/Fit/KeySizedParts.lean) lays them: `canonical`
    (OnBytes/Params/DeriveLin.lean) of `linU`, `linOmega`, `linSplitMsg` (Fit/LinParts.lean) with a
    code's number filled in. The two stages whose numbers are filled in stand under «there are»:
    which numbers is not said.
  `LongMsg o n`: main rows alone, over the extension field, n answers, the word for "no code" as
    its mask code's number. `MaskMsg o n`: one mask row alone, n answers, that word as its main
    code's number.
  `shapes_of_proofSized`: the three in what `proofSized` returns, where a sample has an answer.
  `codesFew_of_proofSized`: each list holds at most one code for each stage of the four tests.
  `placeCode_at`, `placeCode_stays`, `ioppStages_stays`, `ioppStages_head`: WHERE A STAGE's CODE
    LIES: the main code of a list's first stage stands, in the lists that are returned, at the
    number that the stage names; and later placings keep it.
  `linFinish_heads`: the two stages above are the heads of two tests; the two classes of leaves.
  `split_of_proofSized`: THE SPLIT IS NEEDED wherever the main codes of the first stages of the
    folded row's test and of the own test part: which two numbers the shapes name hangs on the last
    test's stages; that they part does not: the codes at them part.
  `ShapesFull M`: sixteen fields at the full size. `shapesFull_of_configure`: from `AtFull M`
    (StageSizesAtScope.lean), configure's yes and a bound on the link's line's stages.
    `shapesFull_of_public`: at a public part as at the full size.
The three fields on answers hang on one number of the full size's setting: one answer to a sample
(`samples_at`; through `AtFull.setP`).
Nearest kin. The planner's own tests `LinShape.ok` and `linOk` (OnBytes/Iop/Lin.lean), which
`sized_tests` (OnBytes/Params/Fit/TreesSized.lean) hands off sized's yes, say of the three: main
rows at the first two, no mask row at Omega, and the split's rows where a split is needed. They say
nothing of an idle number. `linSized_parts` (Fit/LinParts.lean) has the two numbers of rows. That
the split is needed is had in scope by a second road, of other premises: off the places' numbers
where the plan has a place for Omega's test (`places_split`), which asks the description's test on
the plan and the pinned written lists.
What it is not. IT SPEAKS OF THE PLAN's SHAPES AND THE PLAN's CODES. That a record's message has the
plan's shape, and that a record's codes are the plan's, are two equations more, neither here: so it
pays no premise on a member by itself. Not said: the numbers of the codes in use; the closed numbers
of rows; the depth of the split's tree; any code's content. No soundness is claimed. Nothing on
hiding.

-/
import Johnson.Desc.K12.Law.Sizes.IdxAtScope
import OnBytes.Params.Fit.KeySizedParts
import OnBytes.Params.Fit.SizedParts
import OnBytes.Params.Fit.StagesFew
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open OnBytes OnBytes.Params
open H2K.Member

/-! ## 1. General: off the planner's text -/

/-- The rows of an oracle message that holds at least one entry. -/
theorem linRowsOf_pos {n k : ℕ} (h : 0 < n) : 0 < linRowsOf n (2 ^ k) true := by
  show 0 < (n + 2 ^ k - 1) / 2 ^ k
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  exact Nat.div_pos (by omega) hp

/-- **What linSized's closing text lays as the three oracle messages of the shared chain, whole.**
gu, gw: the first stages of the folded row's and of the own test as the shape names them: only the
numbers of their codes are read. -/
theorem linFinish_shapes {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {X Y Z : Sizing} {stU stO stW : List StageSize} {x : LinSized}
    (h : linFinish s L T codes X Y Z stU stO stW = some (x, c)) :
    ∃ gu gw : IoppStage, x.shape.fold.u = canonical { linU s L T with code := gu.code } ∧
      x.shape.omega = canonical { linOmega s L with code := gw.code } ∧
      x.shape.sharedSplit = canonical { linSplitMsg s with maskCode := gu.maskCode } := by
  unfold linFinish at h
  dsimp only at h
  split at h
  · rename_i gu _ gw _ _ _
    cases h
    exact ⟨gu, gw, rfl, rfl, rfl⟩
  · cases h

/-- What is said of a message with main rows alone. -/
def LongMsg (o : OracleShape) (answers : ℕ) : Prop :=
  0 < o.mainRows ∧ o.maskRows = 0 ∧ o.mainDeg = 3 ∧ o.answers = answers ∧ o.maskCode = noId

/-- What is said of the split's message: one mask row and no main row. -/
def MaskMsg (o : OracleShape) (answers : ℕ) : Prop :=
  o.mainRows = 0 ∧ o.maskRows = 1 ∧ o.answers = answers ∧ o.code = noId

theorem longMsg_canonical (s : Setting) (rows code : ℕ) (h : 0 < rows) :
    LongMsg (canonical { linMsg s rows 0 with code := code }) s.samples := by
  have hr : (rows == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  refine ⟨h, rfl, ?_, rfl, rfl⟩
  show (if (rows == 0) = true then 1 else 3) = 3
  rw [hr]
  rfl

theorem maskMsg_canonical (s : Setting) (maskCode : ℕ) :
    MaskMsg (canonical { linSplitMsg s with maskCode := maskCode }) s.samples :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The three oracle messages of the shared chain in what proofSized returns.** -/
theorem shapes_of_proofSized {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) (hs : 0 < (settingOf l).samples) :
    LongMsg z.batch.shape.fold.u (settingOf l).samples ∧
      LongMsg z.batch.shape.omega (settingOf l).samples ∧
      MaskMsg z.batch.shape.sharedSplit (settingOf l).samples := by
  obtain ⟨_, _, _, T, codes1, _, _, _, _, _, _, _, hB⟩ := proofSized_parts h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hF⟩ := linSized_named hB
  obtain ⟨gu, gw, e1, e2, e3⟩ := linFinish_shapes hF
  rw [e1, e2, e3]
  exact ⟨longMsg_canonical _ _ _ (linRowsOf_pos (by omega)),
    longMsg_canonical _ _ _ (linRowsOf_pos (by omega)), maskMsg_canonical _ _⟩

/-- **How many codes a proof's lists hold**: at most one in each list for each stage of the four
tests. -/
theorem codesFew_of_proofSized {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    CodesFew (l.link.stages.length + 1 + z.batch.folded.stages.length +
      z.batch.omega.stages.length + z.batch.own.stages.length) z.codes := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hst, _, _, _⟩ := proofSized_parts h
  have hl := solveStages_length hst
  have e := (tests_of_proofSized h).2.2.2.2
  have F := ioppStages_few z.batch.own.stages _ _ (ioppStages_few z.batch.omega.stages _ _
    (ioppStages_few z.batch.folded.stages _ _ (ioppStages_few z.last.stages _ _ codesFew_empty)))
  rw [← e, hl] at F
  exact F.mono (by omega)


/-! ## 2. Where a stage's code lies; so the split is needed -/

/-- The code that is placed lies at the number that is returned. -/
theorem placeCode_at (list : Array Code) (c : CodeSize) :
    (placeCode list c).1[(placeCode list c).2]? = some ⟨c.logN, c.ell, c.r⟩ := by
  unfold placeCode
  dsimp only
  split
  · rename_i i hi
    obtain ⟨hlt, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
    have e : list.toList[i] = ⟨c.logN, c.ell, c.r⟩ := eq_of_beq hp
    show list[i]? = _
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hlt, e]
  · show (list.push _)[list.size]? = _
    rw [Array.getElem?_push_size]

/-- A code that is placed leaves the list's members where they are. -/
theorem placeCode_stays (list : Array Code) (c : CodeSize) {i : ℕ} {x : Code}
    (h : list[i]? = some x) : (placeCode list c).1[i]? = some x := by
  unfold placeCode
  dsimp only
  split
  · exact h
  · have hi : i < list.size := by
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at h
      cases h
    show (list.push _)[i]? = _
    rw [Array.getElem?_push_lt hi, ← h, Array.getElem?_eq_getElem hi]

/-- So do the codes of a list of stages: the main rows' list. -/
theorem ioppStages_stays : ∀ (st : List StageSize) (codes : Codes) {i : ℕ} {x : Code},
    codes.base[i]? = some x → (ioppStages st codes).2.base[i]? = some x
  | [], _, _, _, h => h
  | y :: rest, codes, i, x, h => by
    unfold ioppStages
    dsimp only
    exact ioppStages_stays rest _ (placeCode_stays codes.base y.g.main h)

/-- **The first stage's main code lies at the number that the stage names.** -/
theorem ioppStages_head (y : StageSize) (rest : List StageSize) (codes : Codes) :
    ∃ g tl, (ioppStages (y :: rest) codes).1 = g :: tl ∧
      (ioppStages (y :: rest) codes).2.base[g.code]? =
        some ⟨y.g.main.logN, y.g.main.ell, y.g.main.r⟩ := by
  unfold ioppStages
  dsimp only
  exact ⟨_, _, rfl, ioppStages_stays rest _ (placeCode_at codes.base y.g.main)⟩

/-- linFinish's shapes with the two stages named as the heads of two tests, and the two classes of
leaves. -/
theorem linFinish_heads {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {X Y Z : Sizing} {stU stO stW : List StageSize} {x : LinSized}
    (h : linFinish s L T codes X Y Z stU stO stW = some (x, c)) :
    ∃ (gu gw : IoppStage) (tu tw : List IoppStage), x.shape.testU = gu :: tu ∧
      x.shape.testOwn = gw :: tw ∧
      x.shape.fold.u = canonical { linU s L T with code := gu.code } ∧
      x.shape.omega = canonical { linOmega s L with code := gw.code } ∧
      x.shape.omegaLeafClass = 1 ∧ x.shape.sharedSplitLeafClass = 2 := by
  unfold linFinish at h
  dsimp only at h
  split at h
  · rename_i gu tu gw tw hu hw
    cases h
    exact ⟨gu, gw, tu, tw, hu, hw, rfl, rfl, rfl, rfl⟩
  · cases h

/-- A message with main rows keeps the number of its main code. -/
theorem code_canonical (s : Setting) (rows code : ℕ) (h : 0 < rows) :
    (canonical { linMsg s rows 0 with code := code }).code = code := by
  have hr : (rows == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  show (if (rows == 0) = true then noId else code) = code
  rw [hr]
  rfl

/-- **The split is needed wherever the first stages of the folded row's test and of the own test
have main codes that part**; and the two classes of leaves part. -/
theorem split_of_proofSized {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) (hs : 0 < (settingOf l).samples) {yU yW : StageSize}
    {rU rW : List StageSize} (hU : z.batch.folded.stages = yU :: rU)
    (hW : z.batch.own.stages = yW :: rW)
    (hne : (⟨yU.g.main.logN, yU.g.main.ell, yU.g.main.r⟩ : Code) ≠
      ⟨yW.g.main.logN, yW.g.main.ell, yW.g.main.r⟩) :
    z.batch.shape.sharedSplitNeeded = true ∧
      z.batch.shape.omegaLeafClass ≠ z.batch.shape.sharedSplitLeafClass := by
  obtain ⟨_, _, _, T, codes1, _, _, _, _, _, _, _, hB⟩ := proofSized_parts h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hF⟩ := linSized_named hB
  obtain ⟨gu, gw, tu, tw, eU, eW, e1, e2, c1, c2⟩ := linFinish_heads hF
  obtain ⟨_, tU, _, tW, tC⟩ := tests_of_proofSized h
  refine ⟨?_, by rw [c1, c2]; decide⟩
  -- the two numbers
  have u1 : z.batch.shape.fold.u.code = gu.code := by
    rw [e1]
    exact code_canonical _ _ _ (linRowsOf_pos (by omega))
  have o1 : z.batch.shape.omega.code = gw.code := by
    rw [e2]
    exact code_canonical _ _ _ (linRowsOf_pos (by omega))
  -- the codes at the two numbers
  rw [hU] at tU tW tC
  rw [hW] at tW tC
  obtain ⟨g1, t1, a1, b1⟩ := ioppStages_head yU rU (ioppStages z.last.stages {}).2
  obtain ⟨g2, t2, a2, b2⟩ := ioppStages_head yW rW (ioppStages z.batch.omega.stages
    (ioppStages (yU :: rU) (ioppStages z.last.stages {}).2).2).2
  have hg1 : gu = g1 := (List.cons.inj (eU.symm.trans (tU.trans a1))).1
  have hg2 : gw = g2 := (List.cons.inj (eW.symm.trans (tW.trans a2))).1
  have B1 : z.codes.base[gu.code]? = some ⟨yU.g.main.logN, yU.g.main.ell, yU.g.main.r⟩ := by
    rw [tC, hg1]
    exact ioppStages_stays _ _ (ioppStages_stays _ _ b1)
  have B2 : z.codes.base[gw.code]? = some ⟨yW.g.main.logN, yW.g.main.ell, yW.g.main.r⟩ := by
    rw [tC, hg2]
    exact b2
  show (z.batch.shape.fold.u.code != z.batch.shape.omega.code) = true
  rw [u1, o1, bne_iff_ne]
  intro e
  rw [e] at B1
  exact hne (Option.some.inj (B1.symm.trans B2))

/-! ## 3. At the full size -/

/-- **The three oracle messages of the shared chain and the two lists' sizes, as far as two tests on
a member of a group read them.** z := M.sized.proof, S := z.batch.shape. -/
structure ShapesFull (M : Configured) : Prop where
  /-- the folded row's message: main rows alone -/
  uMain : 0 < M.sized.proof.batch.shape.fold.u.mainRows
  uMask : M.sized.proof.batch.shape.fold.u.maskRows = 0
  uDeg : M.sized.proof.batch.shape.fold.u.mainDeg = 3
  /-- one answer to a sample: the setting's number of samples at the full size -/
  uAns : M.sized.proof.batch.shape.fold.u.answers = 1
  /-- the number of its idle mask code lies beyond the list -/
  uIdle : M.sized.proof.codes.mask.size ≤ M.sized.proof.batch.shape.fold.u.maskCode
  /-- Omega's message: the like -/
  oMain : 0 < M.sized.proof.batch.shape.omega.mainRows
  oMask : M.sized.proof.batch.shape.omega.maskRows = 0
  oDeg : M.sized.proof.batch.shape.omega.mainDeg = 3
  oAns : M.sized.proof.batch.shape.omega.answers = 1
  oIdle : M.sized.proof.codes.mask.size ≤ M.sized.proof.batch.shape.omega.maskCode
  /-- the split's message: one mask row alone -/
  sMain : M.sized.proof.batch.shape.sharedSplit.mainRows = 0
  sMask : M.sized.proof.batch.shape.sharedSplit.maskRows = 1
  sAns : M.sized.proof.batch.shape.sharedSplit.answers = 1
  /-- the number of its idle main code lies beyond the list -/
  sIdle : M.sized.proof.codes.base.size ≤ M.sized.proof.batch.shape.sharedSplit.code
  /-- the folded row and Omega differ in code: the split's message is sent -/
  split : M.sized.proof.batch.shape.sharedSplitNeeded = true
  /-- Omega's message and the split's have two classes of leaves -/
  classes : M.sized.proof.batch.shape.omegaLeafClass ≠
    M.sized.proof.batch.shape.sharedSplitLeafClass

/-- The three typed lists of stages are short. -/
theorem three_short : szUFull.length + szOFull.length + szWFull.length ≤ 64 := by decide +kernel

/-- The typed list of the folded row's test has a first stage. -/
theorem consU : szUFull = szUFull.headD default :: szUFull.tail := by decide +kernel

/-- So has the own test's. -/
theorem consW : szWFull = szWFull.headD default :: szWFull.tail := by decide +kernel

/-- The main codes of these two first stages part. The folded row's test is held against the OWN
test, not against Omega's: the planner's text gives Omega's message the number of the own test's
first stage's main code. -/
theorem heads_part :
    (⟨(szUFull.headD default).g.main.logN, (szUFull.headD default).g.main.ell,
        (szUFull.headD default).g.main.r⟩ : Code) ≠
      ⟨(szWFull.headD default).g.main.logN, (szWFull.headD default).g.main.ell,
        (szWFull.headD default).g.main.r⟩ := by decide +kernel

/-- At the full size's setting a sample has one answer. -/
theorem samples_at : setAt.samples = 1 := by decide +kernel

/-- **From configure's yes, where the sizes are the full size's.** Of the lines only the number of
stages of the link's line is read; 64 stands for any number far below the word for "no code". -/
theorem shapesFull_of_configure {l : Lines} {shapes : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (A : AtFull made) (hc : configure l shapes cfg bits = .ok made)
    (hl : l.link.stages.length ≤ 64) : ShapesFull made := by
  obtain ⟨hp, hset, _⟩ := configure_proof_sizes hc
  have h1 : (settingOf l).samples = 1 := by
    rw [← hset, A.setP]
    exact samples_at
  obtain ⟨⟨u1, u2, u3, u4, u5⟩, ⟨o1, o2, o3, o4, o5⟩, s1, s2, s3, s4⟩ :=
    shapes_of_proofSized hp (by omega)
  obtain ⟨sp, cs⟩ := split_of_proofSized hp (by omega) (A.U.trans consU) (A.W.trans consW)
    heads_part
  have F := codesFew_of_proofSized hp
  rw [A.U, A.O, A.W] at F
  have hs := three_short
  have hn : noId = 4294967295 := rfl
  exact ⟨u1, u2, u3, u4.trans h1, by rw [u5]; have := F.2; omega, o1, o2, o3, o4.trans h1,
    by rw [o5]; have := F.2; omega, s1, s2, s3.trans h1, by rw [s4]; have := F.1; omega, sp, cs⟩

/-- The written lines' link has few stages. -/
theorem link_short : recordLines.link.stages.length ≤ 64 := by decide +kernel

/-- **At a public part as at the full size**, from configure's yes on its lines and on shapes whose
sub-proofs are subproofsWith's. -/
theorem shapesFull_of_public {X : OnBytes.Model.Verify.Public} (P : PubFull X) {shapes : Shapes}
    {cfg : ByteArray} {bits : Nat} {made : Configured}
    (hc : configure X.P.frame shapes cfg bits = .ok made) {rl : List ReqLink}
    (he : shapes.sub = OnBytes.Model.Verify.subproofsWith X rl) : ShapesFull made :=
  shapesFull_of_configure (atFull_of_public P hc he) hc (by rw [P.frame]; exact link_short)

end H2K.Sizes

#print axioms H2K.Sizes.linFinish_shapes
#print axioms H2K.Sizes.shapes_of_proofSized
#print axioms H2K.Sizes.codesFew_of_proofSized
#print axioms H2K.Sizes.ioppStages_head
#print axioms H2K.Sizes.split_of_proofSized
#print axioms H2K.Sizes.heads_part
#print axioms H2K.Sizes.three_short
#print axioms H2K.Sizes.samples_at
#print axioms H2K.Sizes.link_short
#print axioms H2K.Sizes.shapesFull_of_configure
#print axioms H2K.Sizes.shapesFull_of_public
