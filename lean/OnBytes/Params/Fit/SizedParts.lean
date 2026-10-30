-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/SizedParts.lean: what proofSized, keySized and rangesSized return, part by part,
and that the stages of a proof's last test and of the test of a key's proof of the ranges are in
order for the planner's routines (StageOk).

The three routines (OnBytes/Params/DeriveReq.lean, OnBytes/Plan/KeyOneTime.lean,
OnBytes/Plan/Ranges.lean) size a proof's chains, a key's chains and the key's proof of the ranges.
This file unfolds each text once and says from which calls the parts of what it returns come. Some
letters under "there is" are left free though the text fixes them: the loads; in proofSized_parts
the number K of the last group's row variables, the list codes1 and all of shape but two fields; in
keySized_parts the number of mask rows, of which only "at most 4096" is said.
The row variables of the first stage of the two tests are no numbers of the lines. They are bounded
by tests that the program runs on the finished shapes: every stage as a shape names it has at most
60 row variables (stageOk, OnBytes/Iop/Prox.lean), and ioppStages copies these numbers.

Main theorems.
 - proofSized_parts, keySized_parts, rangesSized_parts.
 - all_stageOk: what ioppOk says of each stage's row variables.
 - kh_le: stages whose shapes pass stageOk have at most 60 row variables of either kind.
 - proof_stages: the links' group and the stages of a proof's last test, from the lines' ranges and
   the test reqShapeOk on the finished request's shape.
 - ranges_stages: the stages of the test of the proof of the ranges are in order, and its oracle
   message has few rows (FewRows), from the lines' ranges alone: rangesSized runs the test itself.

What is asked: the ranges of the lines (GroupCap); for proof_stages that reqShapeOk says yes. None
is shown here. Nothing on soundness. For proofs only; the program does not import this file.

-/
import OnBytes.Params.Fit.StageCaps
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false

namespace OnBytes.Params

open OnBytes.Plan

/-- **What proofSized returns, part by part.** -/
theorem proofSized_parts {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    ∃ (load : GroupLoad) (shape : GroupSize) (K : Nat) (T : TableSize) (codes1 : Codes),
      shape.main.logN = l.link.logN ∧ shape.mask.logN = l.link.maskLogN ∧
      solveGroup (settingOf l) .request load id shape = some z.link ∧
      z.last.group = { z.link.group with k := K, slots := 1,
                                         main := { z.link.group.main with overE := true } } ∧
      solveStages (settingOf l) .request z.last.group z.link.t l.link.stages
        = some z.last.stages ∧
      z.request.last = (ioppStages z.last.stages {}).1 ∧
      deriveTable (settingOf l) l = some T ∧
      linSized (settingOf l) (linLines l sub.matrixRows
        (Send.maskRowsFor
          (sub.pendingRows + (if 1 < sub.pendingRows then Batt.masksOf l.blockLog else 0))
          (2 ^ l.own.maskLogL) l.answers) false) T codes1 = some (z.batch, z.codes) := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, hl, h⟩ := opt_bind h
  obtain ⟨stages, hs, h⟩ := opt_bind h
  obtain ⟨T, hT, h⟩ := opt_bind h
  split at h
  rename_i last codes1 he
  replace h := opt_guard h
  obtain ⟨⟨batch, codes2⟩, hb, h⟩ := opt_bind h
  cases h
  exact ⟨_, _, _, T, codes1, rfl, rfl, hl, rfl, hs, (congrArg Prod.fst he).symm, hT, hb⟩

/-- What ioppStagesOk says of each stage. -/
theorem all_stageOk_from (codes : Codes) (answers : Nat) :
    ∀ (st : List IoppStage) (before : Option IoppStage),
      ioppStagesOk codes answers before st = true → ∀ t ∈ st, stageOk t = true
  | [], _, _, _, ht => by cases ht
  | t0 :: rest, before, h, t, ht => by
    unfold ioppStagesOk at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 ht with rfl | hr
    · have h1 := h.1
      unfold ioppStageOk at h1
      split at h1
      · simp only [Bool.and_eq_true] at h1
        exact h1.1.1.2
      · cases h1
    · exact all_stageOk_from codes answers rest (some t0) h.2 t hr

/-- What ioppOk says of each stage. -/
theorem all_stageOk {codes : Codes} {st : List IoppStage} {answers : Nat}
    (h : ioppOk codes st answers = true) : ∀ t ∈ st, stageOk t = true := by
  unfold ioppOk at h
  simp only [Bool.and_eq_true] at h
  exact all_stageOk_from codes answers st none h.2

/-- Stages whose shapes pass stageOk have at most 60 row variables of either kind. -/
theorem kh_le {st : List StageSize} {codes : Codes}
    (h : ∀ t ∈ (ioppStages st codes).1, stageOk t = true) :
    ∀ y ∈ st, y.g.k ≤ 60 ∧ y.g.h ≤ 60 := by
  intro y hy
  have hm : (y.g.k, y.g.h) ∈ (ioppStages st codes).1.map fun t => (t.k, t.h) := by
    rw [kh_of_stages]
    exact List.mem_map.2 ⟨y, hy, rfl⟩
  obtain ⟨t, ht, e⟩ := List.mem_map.1 hm
  have ho := h t ht
  unfold stageOk at ho
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ho
  have e1 : t.k = y.g.k := congrArg Prod.fst e
  have e2 : t.h = y.g.h := congrArg Prod.snd e
  have hM : mostLogN = 60 := rfl
  omega

/-- Among the stages that solveStages returns is one whose group is the group that went in. -/
theorem solveStages_head {s : Setting} {scope : Scope} {first : GroupSize}
    {firstT : Nat} {choice : List StageLine} {st : List StageSize}
    (h : solveStages s scope first firstT choice = some st) :
    ∃ y ∈ st, y.g = first := by
  unfold solveStages at h
  split at h
  · cases h
  · obtain ⟨r, _, e⟩ := Option.map_eq_some_iff.1 h
    exact ⟨⟨first, firstT, 0⟩, e ▸ List.mem_cons_self, rfl⟩

/-- **The links' group and the stages of a proof's last test.** -/
theorem proof_stages {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) (C : GroupCap l.link)
    (hr : reqShapeOk z.request = true) :
    z.link.group.main.logN ≤ 64 ∧ ∀ t ∈ z.last.stages, StageOk t := by
  obtain ⟨load, shape, K, T, codes1, n1, n2, hl, eg, hs, er, _⟩ := proofSized_parts h
  have S := solveGroup_solves hl
  have hN : shape.main.logN ≤ 32 := n1 ▸ C.logN
  have hZ : shape.mask.logN ≤ 32 := n2 ▸ Nat.le_trans C.mask C.logN
  have F := fit_of_solves S hN hZ
  have F' : GroupFit z.last.group := by
    rw [eg]
    exact F
  have hall : ∀ t ∈ (ioppStages z.last.stages {}).1, stageOk t = true := by
    rw [← er]
    unfold reqShapeOk at hr
    simp only [Bool.and_eq_true, List.all_eq_true] at hr
    exact hr.1.2
  have kh := kh_le hall
  obtain ⟨y, hy, ey⟩ := solveStages_head hs
  have k0 := kh y hy
  rw [ey] at k0
  exact ⟨Nat.le_trans F.1.1 (by decide),
    stages_ok C.stages hs F' (by omega) (by omega)⟩

section
/- the search through 4096 numbers is not to be run by the unifier -/
attribute [local irreducible] Send.maskRowsFor

/-- **What rangesSized returns, part by part.** -/
theorem rangesSized_parts {s : Setting} {L : RangesLines} {codes c : Codes} {z : RangesSized}
    (h : rangesSized s L codes = some (z, c)) :
    ∃ (load : GroupLoad) (o : OracleShape),
      solveTest s .once L.group load id
        { shapeOf L.group (linGroupBits [o]).1 false with h := (linGroupBits [o]).2 } =
          some z.test ∧
      z.x.stages = (ioppStages z.test.stages codes).1 ∧
      c = (ioppStages z.test.stages codes).2 ∧ SameRows z.x.message.shape o ∧
      o.maskRows ≤ 4096 ∧ Wf.admitted c z.x z.matrix = true := by
  unfold rangesSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨last, _, h⟩ := opt_bind h
  replace h := opt_guard h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨test, ht, h⟩ := opt_bind h
  split at h
  rename_i stages codes' he
  obtain ⟨first, _, h⟩ := opt_bind h
  try extract_lets at h
  obtain ⟨ha, h⟩ := opt_guard_not h
  cases h
  refine ⟨_, _, ht, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg Prod.fst he).symm
  · exact (congrArg Prod.snd he).symm
  · exact ⟨rfl, rfl⟩
  · exact maskRowsFor_le _ _ _
  · simpa using ha

end

/-- n ≤ 2 ^ clog2 n. -/
theorem le_pow_clog2 (n : Nat) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  split
  · rename_i h
    exact Nat.le_trans h Nat.one_le_two_pow
  · rename_i h
    have h2 : n - 1 < 2 ^ (Nat.log2 (n - 1) + 1) := Nat.lt_log2_self
    omega

/-- **The stages of the test of the proof of the ranges, and the rows of its oracle message.** -/
theorem ranges_stages {s : Setting} {L : RangesLines} {codes c : Codes} {z : RangesSized}
    (h : rangesSized s L codes = some (z, c)) (C : GroupCap L.group) :
    (∀ t ∈ z.test.stages, StageOk t) ∧ FewRows z.x.message.shape := by
  obtain ⟨load, o, ht, es, _, er, hm, ha⟩ := rangesSized_parts h
  have hio : ioppOk c z.x.stages z.x.message.shape.answers = true := by
    unfold Wf.admitted at ha
    simp only [Bool.and_eq_true] at ha
    exact ha.2
  have hall : ∀ t ∈ (ioppStages z.test.stages codes).1, stageOk t = true := by
    rw [← es]
    exact all_stageOk hio
  have kh := kh_le hall
  have ht' := ht
  unfold solveTest at ht'
  obtain ⟨x, hx, ht'⟩ := opt_bind ht'
  obtain ⟨st, hst, ht'⟩ := opt_bind ht'
  have et : z.test = ⟨x.group, x.t, st⟩ := (Option.some.inj ht').symm
  have S := solveGroup_solves hx
  obtain ⟨y, hy, ey⟩ := solveStages_head hst
  have k0 := kh y (by rw [et]; exact hy)
  rw [ey, S.k, S.h] at k0
  have k1 : (linGroupBits [o]).1 ≤ 60 := k0.1
  have k2 : (linGroupBits [o]).2 ≤ 60 := k0.2
  refine ⟨solveTest_stages C ht C.logN (Nat.le_trans C.mask C.logN) (by
    show (linGroupBits [o]).1 ≤ 131
    omega) (by
    show (linGroupBits [o]).2 ≤ 131
    omega), .of_same er ⟨?_, ?_⟩⟩
  · have a : clog2 (sumT [if o.mainRows != 0 then pow2AtLeast o.mainRows else 0]) ≤ 60 :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) k1
    have b : sumT [if o.mainRows != 0 then pow2AtLeast o.mainRows else 0] =
        if o.mainRows != 0 then pow2AtLeast o.mainRows else 0 := by
      simp [sumT]
    rw [b] at a
    by_cases h0 : o.mainRows = 0
    · rw [h0]
      exact Nat.zero_le _
    · rw [if_pos (by simpa using h0)] at a
      have c1 := le_pow_clog2 (pow2AtLeast o.mainRows)
      have c2 : o.mainRows ≤ pow2AtLeast o.mainRows := le_pow_clog2 o.mainRows
      have c3 : 2 ^ clog2 (pow2AtLeast o.mainRows) ≤ 2 ^ 60 :=
        Nat.pow_le_pow_right (by decide) a
      have g : 2 ^ 60 ≤ 2 ^ 128 := by norm_num
      omega
  · have g : 4096 ≤ 2 ^ 128 := by norm_num
    omega

/-- **What keySized returns, part by part.** -/
theorem keySized_parts {l : Lines} {shape : Shape} {z : KeySized}
    (h : keySized l shape = some z) :
    ∃ (T : TableSize) (L : RangesLines) (rows : Nat) (codes1 : Codes),
      deriveTable (settingOf l) l = some T ∧
      rangesLines { shape with kCol := l.blockLog } l.onceRanges l.rangesPart = some L ∧
      rows ≤ 4096 ∧
      linSized (settingOf l) (linLines l L.matrixRows rows true) T {} = some (z.once, codes1) ∧
      rangesSized (settingOf l) L codes1 = some (z.ranges, z.codes) := by
  unfold keySized at h
  extract_lets at h
  obtain ⟨T, hT, h⟩ := opt_bind h
  obtain ⟨L, hL, h⟩ := opt_bind h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨⟨once, c1⟩, ho, h⟩ := opt_bind h
  obtain ⟨⟨ranges, c2⟩, hr, h⟩ := opt_bind h
  cases h
  exact ⟨T, L, _, c1, hT, hL, maskRowsFor_le _ _ _, ho, hr⟩

end OnBytes.Params
