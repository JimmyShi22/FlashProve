-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchFrontPlain.lean: THE PREMISES OF A CODE SWITCH AT ITS FRONT
(FrontPlain, Johnson/Desc/K2/Honest/Returns/SentFront.lean: sixteen fields, at the statement IN
FRONT OF the sending) AS ONE TEST WITH CODE ON SHAPES AND ONE ON VALUES. A general law; nothing is
evaluated.

What it is for. The law frontFits_sent of that file leads from FrontPlain to all that the step
behind the sending asks of what it is handed. Here FrontPlain, with its group under "there is", is
met just if two Bools accept.

  `inRangeB`: the one clause that reads what a round draws: each listed position lies in the old
    main code's range.
  `groupB`: four of the five clauses on the new group: no test has begun; it has no member; its
    main code is the target's; and each copy's. (The fifth, that it is there, is frontPlainB's own
    look-up.)
  **`frontPlainB a F old T grp poss c`**: THE SIXTEEN, in the fields' order, without TablesFit's
    comparisons of field elements: check (switchCheckS) · restMain · fits (oldFitsB) · keptPos ·
    keptAnswers · lengths · logC · logZ · inRange · group, noRun, noMember, groupCode, copiesCode
    (groupB) · tables (tablesB) · reads (readsB): the four named tests are SwitchFrontFits.lean's.
    a: the statement's shape; F: the makes of its rows; old: the make of the carried single rows; T:
    the target; grp: the new group's number; poss: the positions that the second round draws; c:
    the old main code, of which logN alone is read.
  **`frontPlain_iffB`**: (∃ G, FrontPlain x c G poss) just if frontPlainB accepts at the shapes of x
    and onesV x.st x.f.rows accepts (SwitchFrontFits.lean: at each written-out variable the pair is
    (1, 1)).
  `frontPlain_of_B`: the way from the two Bools, with the group named.
  **`frontCoreB a F old T code poss c`** | **`frontCore_iffB`**: the like for FrontCore (the same
    file: FrontPlain's sixteen less the new group's three; code: the group's main code): for a front
    that has just made the group. `frontCoreB_split`: the clause on the positions' range, taken out.

Limits. No front is shown here at which a Bool accepts.
onesV reads field elements, and inRangeB reads drawn positions: neither is a test on a shape.
Nothing on the book (ReadFits: SwitchReadFits.lean). Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.K2.Honest.Returns.SentFront
import Johnson.Desc.First.Shape.SwitchFrontFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.Ground.Sh (StSh GrpSh stSh grpSh grp_get)
open VerifiableInference.Desc.K2.Honest.Returns (FrontPlain FrontCore)
open _root_.Tw.K2 (Front)

/-- Each listed position lies in the old main code's range. -/
def inRangeB (a : StSh) (old : SingleSh) (poss : List Nat) (c : Code) : Bool :=
  (Positions.ofDraws c.logN poss).all.toList.all fun v =>
    decide (v < 2 ^ (a.codes.base.getD old.code default).logN)

/-- The new group: no test has begun; no member; its main code is the target's and each copy's. -/
def groupB (G : GrpSh) (T : SwitchTarget) : Bool :=
  !G.inRun && G.members.isEmpty && T.shape.code == G.code &&
    T.kept.toList.all fun k => k.shape.code == G.code

theorem groupB_iff (G : Group) (T : SwitchTarget) :
    groupB (grpSh G) T = true ↔ G.inRun = false ∧ G.members = #[] ∧ T.shape.code = G.code ∧
      ∀ k ∈ T.kept.toList, k.shape.code = G.code := by
  have e : (grpSh G).members.isEmpty = true ↔ G.members = #[] := by
    show G.members.toList.isEmpty = true ↔ _
    rw [List.isEmpty_iff]
    exact Array.toList_eq_nil_iff
  unfold groupB
  simp only [Bool.and_eq_true, Bool.not_eq_true', e, beq_iff_eq, List.all_eq_true]
  exact ⟨fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩

/-- **FrontPlain without TablesFit's comparisons of field elements, as one Bool.** -/
def frontPlainB (a : StSh) (F : FormsSh) (old : SingleSh) (T : SwitchTarget) (grp : Nat)
    (poss : List Nat) (c : Code) : Bool :=
  switchCheckS a old T && decide (T.rest.part = .main) && oldFitsB a F old &&
    (T.kept.toList.all fun k => decide (0 < k.shape.mainRows)) &&
    (T.kept.toList.all fun k => k.shape.answers != 0) &&
    a.codes.lengthsOk &&
    decide ((a.codes.base.getD old.code default).logN ≤ 32) &&
    decide ((a.codes.mask.getD old.maskCode default).logN ≤ 32) &&
    inRangeB a old poss c &&
    (match a.groups[grp]? with
      | some G => groupB G T
      | none => false) &&
    tablesB a F old T && readsB F old

/-- **FrontPlain, with its group under "there is", just if the test on shapes and the part on values
accept.** -/
theorem frontPlain_iffB (x : Front) (c : Code) (poss : List Nat) :
    (∃ G, FrontPlain x c G poss) ↔
      (frontPlainB (stSh x.st) (formsOf x.st) (singleSh x.f.rows) x.T x.f.group poss c &&
        onesV x.st x.f.rows) = true := by
  have eR : inRangeB (stSh x.st) (singleSh x.f.rows) poss c = true ↔
      ∀ v ∈ (Positions.ofDraws c.logN poss).all.toList,
        v < 2 ^ (x.st.codes.base.getD x.f.rows.code default).logN := by
    unfold inRangeB
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact Iff.rfl
  have eG : (match (stSh x.st).groups[x.f.group]? with
      | some G => groupB G x.T
      | none => false) = true ↔
      ∃ G, x.st.groups[x.f.group]? = some G ∧ G.inRun = false ∧ G.members = #[] ∧
        x.T.shape.code = G.code ∧ ∀ k ∈ x.T.kept.toList, k.shape.code = G.code := by
    rw [grp_get]
    cases x.st.groups[x.f.group]? with
    | none =>
      constructor
      · intro h
        exact nomatch h
      · rintro ⟨_, h, -⟩
        exact nomatch h
    | some G =>
      show groupB (grpSh G) x.T = true ↔ _
      rw [groupB_iff]
      constructor
      · intro h
        exact ⟨G, rfl, h⟩
      · rintro ⟨G', e, h⟩
        obtain rfl := Option.some.inj e
        exact h
  unfold frontPlainB
  simp only [Bool.and_eq_true, ← switchCheck_sh, oldFitsB_iff, eR, eG, readsB_iff,
    decide_eq_true_eq, List.all_eq_true, bne_iff_ne]
  constructor
  · rintro ⟨G, h⟩
    obtain ⟨t1, t2⟩ := (tablesFit_iff _ _ _).1 h.tables
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.check, h.restMain⟩, h.fits⟩, h.keptPos⟩, h.keptAnswers⟩, h.lengths⟩,
      h.logC⟩, h.logZ⟩, h.inRange⟩, G, h.group, h.noRun, h.noMember, h.groupCode,
      h.copiesCode⟩, t1⟩, h.reads⟩, t2⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, G, g1, g2, g3, g4, g5⟩, t1⟩,
      h16⟩, t2⟩
    exact ⟨G, h1, h2, h3, h4, h5, h6, h7, h8, h9, g1, g2, g3, g4, g5,
      (tablesFit_iff _ _ _).2 ⟨t1, t2⟩, h16⟩

/-- From the two Bools; the group is the one at the front's number. -/
theorem frontPlain_of_B {x : Front} {c : Code} {poss : List Nat}
    (h : frontPlainB (stSh x.st) (formsOf x.st) (singleSh x.f.rows) x.T x.f.group poss c = true)
    (hv : onesV x.st x.f.rows = true) :
    ∃ G, x.st.groups[x.f.group]? = some G ∧ FrontPlain x c G poss := by
  obtain ⟨G, F⟩ := (frontPlain_iffB x c poss).2 (by rw [h, hv]; rfl)
  exact ⟨G, F.group, F⟩

/-- **FrontCore without TablesFit's comparisons of field elements, as one Bool.** code: the new
group's main code. -/
def frontCoreB (a : StSh) (F : FormsSh) (old : SingleSh) (T : SwitchTarget) (code : Nat)
    (poss : List Nat) (c : Code) : Bool :=
  switchCheckS a old T && decide (T.rest.part = .main) && oldFitsB a F old &&
    (T.kept.toList.all fun k => decide (0 < k.shape.mainRows)) &&
    (T.kept.toList.all fun k => k.shape.answers != 0) &&
    a.codes.lengthsOk &&
    decide ((a.codes.base.getD old.code default).logN ≤ 32) &&
    decide ((a.codes.mask.getD old.maskCode default).logN ≤ 32) &&
    inRangeB a old poss c && T.shape.code == code &&
    (T.kept.toList.all fun k => k.shape.code == code) &&
    tablesB a F old T && readsB F old

/-- **FrontCore just if the test on shapes and the part on values accept.** -/
theorem frontCore_iffB (x : Front) (c : Code) (code : Nat) (poss : List Nat) :
    FrontCore x c code poss ↔
      (frontCoreB (stSh x.st) (formsOf x.st) (singleSh x.f.rows) x.T code poss c &&
        onesV x.st x.f.rows) = true := by
  have eR : inRangeB (stSh x.st) (singleSh x.f.rows) poss c = true ↔
      ∀ v ∈ (Positions.ofDraws c.logN poss).all.toList,
        v < 2 ^ (x.st.codes.base.getD x.f.rows.code default).logN := by
    unfold inRangeB
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact Iff.rfl
  unfold frontCoreB
  simp only [Bool.and_eq_true, ← switchCheck_sh, oldFitsB_iff, eR, readsB_iff,
    decide_eq_true_eq, List.all_eq_true, bne_iff_ne, beq_iff_eq]
  constructor
  · intro h
    obtain ⟨t1, t2⟩ := (tablesFit_iff _ _ _).1 h.tables
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.check, h.restMain⟩, h.fits⟩, h.keptPos⟩, h.keptAnswers⟩, h.lengths⟩,
      h.logC⟩, h.logZ⟩, h.inRange⟩, h.groupCode⟩, h.copiesCode⟩, t1⟩, h.reads⟩, t2⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, t1⟩, h13⟩, t2⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, (tablesFit_iff _ _ _).2 ⟨t1, t2⟩, h13⟩

/-- The clause on the positions' range, taken out of frontCoreB. -/
theorem frontCoreB_split (a : StSh) (F : FormsSh) (old : SingleSh) (T : SwitchTarget) (code : Nat)
    (poss : List Nat) (c : Code) :
    frontCoreB a F old T code poss c =
      (frontCoreB a F old T code [] c && inRangeB a old poss c) := by
  have e : inRangeB a old [] c = true := rfl
  unfold frontCoreB
  rw [e]
  cases inRangeB a old poss c <;> simp

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.frontCore_iffB
#print axioms VerifiableInference.Desc.First.Shape.frontCoreB_split
#print axioms VerifiableInference.Desc.First.Shape.groupB_iff
#print axioms VerifiableInference.Desc.First.Shape.frontPlain_iffB
#print axioms VerifiableInference.Desc.First.Shape.frontPlain_of_B
