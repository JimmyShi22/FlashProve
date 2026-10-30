-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/StagesFew.lean: the proximity tests in the shape of a key's test on the table
have few stages and the key's two lists of codes few codes, where the parameter file's lines are
within their ranges; so the two items of the key's shared chain, "codes" and "the test on the
table", have fewer than 2 ^ 64 bytes.

The second of a group's two lines in the parameter file, "stages", names at most 8 later stages: the
reader refuses more than 32 numbers, four for each stage (groupLines, OnBytes/Params/File.lean;
GroupCap.count, OnBytes/Params/Fit/LinesCap.lean). "solveStages" (OnBytes/Params/Group.lean) returns
one stage for each of them and the first stage. "ioppStages" (OnBytes/Params/Derive.lean) returns
one stage for each solved stage, and for each solved stage it adds at most one code to each of the
two lists. OnBytes/Params/Fit/CodesCap.lean and CodesSized.lean walk the same routines and say of
each code that its messages are short. This file counts.

Main names.
 - solveLater_length, solveStages_length, solveTest_length: as many stages as the line names, and
   the first.
 - ioppStages_length: as many stages as were solved.
 - CodesFew n codes: each of the two lists has at most n codes. CodesFew.mono, codesFew_empty,
   placeCode_size, ioppStages_few.
 - linSized_tests: the four lists of stages in the shape that linSized returns.
 - linSized_few, **keySized_few**: a key's lists have at most 36 codes each, and each of the four
   lists of stages in the shape of its test on the table has at most 9 stages.
 - size_catOf, size_listOf, size_spellRow, size_bool, size_spellCode, size_spellShape,
   size_spellStage, size_spellStages, size_spellCodes, size_spellLin: the sizes of what
   OnBytes/Params/Spell.lean spells; of "the test on the table" an upper bound.
 - **keyItems_short**: spellCodes z.codes and spellLin z.once.shape have fewer than 2 ^ 64 bytes
   each. That these two are the shared chain's items is not this file's (madeLinItems,
   configure_bytes: OnBytes/Model/ReadBackMade.lean).

Limits. The bounds are far from sharp. The key's chains alone: nothing on a proof's or an entry's.
Of the stages of the key's proof of the ranges no statement: their number is counted inside
keySized_few's proof alone. The ranges of the lines (LinesCap) are a premise here. Nothing where the
routines refuse. That keySized returns at any lines is shown by no term here. Nothing on soundness.
The program does not import this file.

-/
import OnBytes.Params.Fit.KeyCaps
import OnBytes.Params.IndexLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-! ## How many stages -/

/-- One later stage for each line. -/
theorem solveLater_length {s : Setting} {scope : Scope} :
    ∀ (choice : List StageLine) (o : GroupSize) (st : List StageSize),
    solveLater s scope o choice = some st → st.length = choice.length := by
  intro choice
  induction choice with
  | nil =>
    intro o st h
    unfold solveLater at h
    cases h
    rfl
  | cons c rest ih =>
    intro o st h
    unfold solveLater at h
    rcases ite_cases h with ⟨_, h⟩ | ⟨_, h⟩
    · cases h
    · extract_lets carried ownFold maskEll shape at h
      split at h
      · cases h
      · rename_i x hx
        cases hr : solveLater s scope x.group rest with
        | none =>
          rw [hr] at h
          cases h
        | some st' =>
          rw [hr] at h
          obtain rfl := Option.some.inj h
          simp only [List.length_cons, ih x.group st' hr]

/-- The first stage, and one stage for each line. -/
theorem solveStages_length {s : Setting} {scope : Scope} {first : GroupSize}
    {firstT : Nat} {choice : List StageLine} {st : List StageSize}
    (h : solveStages s scope first firstT choice = some st) :
    st.length = choice.length + 1 := by
  unfold solveStages at h
  rcases ite_cases h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  · cases hr : solveLater s scope first choice with
    | none =>
      rw [hr] at h
      cases h
    | some st' =>
      rw [hr] at h
      obtain rfl := Option.some.inj h
      simp only [List.length_cons, solveLater_length choice first st' hr]

/-- The same of a group that is solved and then tested. -/
theorem solveTest_length {s : Setting} {scope : Scope} {l : GroupLine} {load : GroupLoad}
    {draws : Nat → Nat} {shape : GroupSize} {t : TestSizes}
    (h : solveTest s scope l load draws shape = some t) :
    t.stages.length = l.stages.length + 1 := by
  unfold solveTest at h
  obtain ⟨x, _, h⟩ := opt_bind h
  obtain ⟨st, hs, h⟩ := opt_bind h
  cases h
  exact solveStages_length hs

/-- As many stages as were solved. -/
theorem ioppStages_length (st : List StageSize) (codes : Codes) :
    (ioppStages st codes).1.length = st.length := by
  have h := congrArg List.length (kh_of_stages st codes)
  rwa [List.length_map, List.length_map] at h

/-! ## How many codes -/

/-- Each of the two lists has at most n codes. -/
def CodesFew (n : Nat) (codes : Codes) : Prop := codes.base.size ≤ n ∧ codes.mask.size ≤ n

theorem CodesFew.mono {n m : Nat} {codes : Codes} (h : CodesFew n codes) (hnm : n ≤ m) :
    CodesFew m codes :=
  ⟨Nat.le_trans h.1 hnm, Nat.le_trans h.2 hnm⟩

theorem codesFew_empty : CodesFew 0 {} := ⟨Nat.le_of_eq rfl, Nat.le_of_eq rfl⟩

/-- At most one code more. -/
theorem placeCode_size (list : Array Code) (c : CodeSize) :
    (placeCode list c).1.size ≤ list.size + 1 := by
  unfold placeCode
  dsimp only
  split
  · exact Nat.le_succ _
  · simp only [Array.size_push, Nat.le_refl]

/-- **The codes of a list of stages**: at most one more in each list for each stage. -/
theorem ioppStages_few : ∀ (st : List StageSize) (codes : Codes) (n : Nat), CodesFew n codes →
    CodesFew (n + st.length) (ioppStages st codes).2 := by
  intro st
  induction st with
  | nil =>
    intro codes n H
    exact H
  | cons y rest ih =>
    intro codes n H
    have k := ih ⟨(placeCode codes.base y.g.main).1, (placeCode codes.mask y.g.mask).1⟩ (n + 1)
      ⟨Nat.le_trans (placeCode_size _ _) (Nat.succ_le_succ H.1),
        Nat.le_trans (placeCode_size _ _) (Nat.succ_le_succ H.2)⟩
    have e : n + (y :: rest).length = n + 1 + rest.length := by
      rw [List.length_cons]
      omega
    rw [e]
    unfold ioppStages
    dsimp only
    exact k

/-! ## The test on the table -/

/-- The four lists of stages in the shape that linSized returns. -/
theorem linSized_tests {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) :
    x.shape.testU = (ioppStages x.folded.stages codes).1 ∧
      x.shape.testOmega =
        (ioppStages x.omega.stages (ioppStages x.folded.stages codes).2).1 ∧
      x.shape.testOwn = (ioppStages x.own.stages
        (ioppStages x.omega.stages (ioppStages x.folded.stages codes).2).2).1 ∧
      x.shape.testOwnOmega = [] := by
  unfold linSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨_, h⟩ := opt_guard_not h
  obtain ⟨⟨X, Y, Z⟩, _, h⟩ := opt_bind h
  replace h := opt_guard h
  obtain ⟨stU, _, h⟩ := opt_bind h
  obtain ⟨stO, _, h⟩ := opt_either_or h
  obtain ⟨stW, _, h⟩ := opt_bind h
  repeat' split at h
  all_goals first
    | (cases h
       exact ⟨by simp only [*], by simp only [*], by simp only [*], rfl⟩)
    | cases h

/-- **The test on the table adds at most 27 codes to each list, and each of its tests has at most 9
stages.** -/
theorem linSized_few {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} {n : Nat} (h : linSized s L T codes = some (x, c)) (HF : GroupCap L.folded)
    (HO : GroupCap L.omega) (HW : GroupCap L.own) (H : CodesFew n codes) :
    CodesFew (n + 27) c ∧ x.shape.testU.length ≤ 9 ∧ x.shape.testOmega.length ≤ 9 ∧
      x.shape.testOwn.length ≤ 9 ∧ x.shape.testOwnOmega.length ≤ 9 := by
  obtain ⟨t1, t2, t3, t4⟩ := linSized_tests h
  obtain ⟨G, X, Y, Z, a, b, stU, stO, stW, _, _, _, _, hU, hO, hW, eF, eO, eW, _, _, _, _, _, _,
    _, _, ec⟩ := linSized_parts h
  have lU : stU.length ≤ 9 := by
    have k := solveStages_length hU
    have q := HF.count
    omega
  have lW : stW.length ≤ 9 := by
    have k := solveStages_length hW
    have q := HW.count
    omega
  have lO : stO.length ≤ 9 := by
    rcases hO with ⟨_, hO⟩ | rfl
    · have k := solveStages_length hO
      have q := HO.count
      omega
    · exact Nat.zero_le _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ec]
    exact (ioppStages_few stW _ _ (ioppStages_few stO _ _ (ioppStages_few stU codes n H))).mono
      (by omega)
  · rw [t1, ioppStages_length, eF]
    exact lU
  · rw [t2, ioppStages_length, eO]
    exact lO
  · rw [t3, ioppStages_length, eW]
    exact lW
  · rw [t4]
    exact Nat.zero_le _

/-- **A key's chains**: at most 36 codes in each list, and at most 9 stages in each test of the test
on the table. -/
theorem keySized_few {l : Lines} {shape : Plan.Shape} {z : Plan.KeySized}
    (h : Plan.keySized l shape = some z) (H : LinesCap l) :
    CodesFew 36 z.codes ∧ z.once.shape.testU.length ≤ 9 ∧ z.once.shape.testOmega.length ≤ 9 ∧
      z.once.shape.testOwn.length ≤ 9 ∧ z.once.shape.testOwnOmega.length ≤ 9 := by
  obtain ⟨T, L, rows, codes1, _, hL, _, hl, hR⟩ := keySized_parts h
  obtain ⟨cF, cO, cW⟩ := linLines_caps H L.matrixRows rows true
  obtain ⟨f1, tests⟩ := linSized_few hl cF cO cW codesFew_empty
  obtain ⟨load, kh, ht, ec⟩ := rangesSized_test hR
  have lR : z.ranges.test.stages.length ≤ 9 := by
    have k := solveTest_length ht
    have q : L.group.stages.length ≤ 8 := by
      rw [rangesLines_group hL]
      exact H.onceRanges.count
    omega
  refine ⟨?_, tests⟩
  rw [ec]
  exact (ioppStages_few z.ranges.test.stages codes1 (0 + 27) f1).mono (by omega)

/-! ## The sizes of what is spelled -/

/-- Spellings of k bytes each, in a row. -/
theorem size_catOf {α : Type} (sp : α → ByteArray) (k : Nat) (hk : ∀ x, (sp x).size = k) :
    ∀ l : List α, (Fmt.cat (l.map sp)).size = k * l.length
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, Fmt.cat_cons, ByteArray.size_append, hk, size_catOf sp k hk l,
      List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- A list of spellings of k bytes each: the word of its length, then the spellings. -/
theorem size_listOf {α : Type} (sp : α → ByteArray) (k : Nat) (hk : ∀ x, (sp x).size = k)
    (l : List α) : (Fmt.list sp l).size = 8 + k * l.length := by
  have e : (Fmt.u64n l.length).size = 8 := rfl
  unfold Fmt.list
  rw [ByteArray.size_append, size_catOf sp k hk l, e]

theorem size_spellRow (l : List Nat) : (spellRow l).size = 8 * l.length :=
  size_catOf spellWord 8 (fun _ => rfl) l

theorem size_bool (b : Bool) : (Fmt.bool b).size = 8 := rfl

theorem size_spellCode (c : Code) : (spellCode c).size = 24 := by
  simp [spellCode, size_spellRow]

theorem size_spellShape (o : OracleShape) : (spellShape o).size = 48 := by
  simp [spellShape, size_spellRow]

theorem size_spellStage (t : IoppStage) : (spellStage t).size = 32 := by
  simp [spellStage, size_spellRow]

theorem size_spellStages (l : List IoppStage) : (spellStages l).size = 8 + 32 * l.length :=
  size_listOf spellStage 32 size_spellStage l

/-- The item "codes". -/
theorem size_spellCodes (c : Codes) :
    (spellCodes c).size = 16 + 24 * c.base.size + 24 * c.mask.size := by
  unfold spellCodes
  rw [ByteArray.size_append, size_listOf spellCode 24 size_spellCode,
    size_listOf spellCode 24 size_spellCode, Array.length_toList, Array.length_toList]
  omega

/-- The item "the test on the table": an upper bound. -/
theorem size_spellLin (S : LinShape) :
    (spellLin S).size ≤ 1024 + 32 * (S.testU.length + S.testOmega.length + S.testOwn.length +
      S.testOwnOmega.length) := by
  unfold spellLin spellFoldeq spellChoice
  simp only [ByteArray.size_append, spellIndex_size, size_spellShape, size_spellRow,
    size_spellStages, size_bool, List.length_cons, List.length_nil]
  omega

/-- **Both items of a key's shared chain have fewer than 2 ^ 64 bytes**, where the sizing of the key
returns and the lines are within their ranges. -/
theorem keyItems_short {l : Lines} {shape : Plan.Shape} {z : Plan.KeySized}
    (h : Plan.keySized l shape = some z) (H : LinesCap l) :
    (spellCodes z.codes).size < 2 ^ 64 ∧ (spellLin z.once.shape).size < 2 ^ 64 := by
  obtain ⟨⟨b, m⟩, t1, t2, t3, t4⟩ := keySized_few h H
  constructor
  · rw [size_spellCodes]
    omega
  · have k := size_spellLin z.once.shape
    omega

end OnBytes.Params

#print axioms OnBytes.Params.solveStages_length
#print axioms OnBytes.Params.ioppStages_few
#print axioms OnBytes.Params.linSized_tests
#print axioms OnBytes.Params.keySized_few
#print axioms OnBytes.Params.size_spellLin
#print axioms OnBytes.Params.keyItems_short
