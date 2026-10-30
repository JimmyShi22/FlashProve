-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchFrontFits.lean: FOUR OF THE TESTS THAT "THE STEP BEHIND A CODE
SWITCH's SENDING RETURNS" ASKS OF THE STATEMENT AND THE CARRIED SINGLE ROWS, AS TESTS WITH CODE ON
SHAPES, WITH THE ONE PART ON VALUES SPLIT OFF. At a general statement. General laws; nothing is
evaluated.

The four: the library's own test on the target (switchTargetCheck, OnBytes/Iop/Cs.lean); "what is
public of the claim in front" (OldFits, Johnson/Desc/K2/Honest/Inner/Statement.lean); "the tables'
sizes, the claim's forms and the stored sample rows" (TablesFit,
Johnson/Desc/K2/Honest/Returns/BehindAt.lean); "the kept members' stored sample rows read their
member's main table alone" (readsMainOf, Johnson/Top/H0/Tw/K2/RowsCan.lean).

What they are read off: a : the statement's shape (Ground.Sh.StSh); F : the makes of its rows
(FormsSh, Forms.lean): of these the messages' stored sample rows alone; old : the make of the
carried single rows (SingleSh, Single.lean); T : the target, which is public.

  1 `stored_all`: a test on makes at each stored sample row of a message.
  2 `switchCheckS` | **`switchCheck_sh`**: switchTargetCheck S old T = switchCheckS (stSh S)
    (singleSh old) T: an equation.
  3 `readsMainS` | `readsMain_mk`; `readsB` | **`readsB_iff`**.
  4 `oldFitsB` | **`oldFitsB_iff`**: all eight fields.
  5 `tablesB`: TablesFit's five fields without their comparisons of field elements. **`onesV`**: THE
    PART ON VALUES: at each written-out variable the pair is (1, 1): in the carried form on the main
    row, in each carried form on a kept member, and in each term of the kept members' stored sample
    rows (onesF, onesT: FoldMake.lean). **`tablesFit_iff`**: TablesFit S old T just if tablesB
    accepts at the shapes and onesV S old accepts.

Limits. No statement is shown here at which a test accepts. onesV reads field elements: it is no
test on a shape, and no law here carries it from what a
chain's steps lay. Nothing on the new messages (the carrying message, the copies, their pads).
Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.K2.Honest.Returns.BehindAt
import Johnson.Desc.First.Shape.Switch
import Johnson.Desc.First.Shape.FoldMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.Ground.Sh (StSh stSh tableBitsS tableBitsS_eq)
open VerifiableInference.Desc.K2.Honest (OldFits sizesAt)
open VerifiableInference.Desc.K2.Honest.Returns (TablesFit)
open _root_.Tw.K2 (readsMainOf)

/-! ## 1 The stored sample rows, through their makes -/

/-- A test on makes holds at each stored sample row of message o just if it holds at each make that
the makes of the statement's rows hold for o. -/
theorem stored_all (S : Statement) (o : Nat) (p : RowMk → Bool) :
    (((formsOf S).oracles[o]?).getD []).all p =
      (S.oracles.getD o default).sampleRows.toList.all fun r => p (rowMk r) := by
  rw [← samples_at, List.all_map]
  rfl

/-! ## 2 The library's test on the target -/

/-- switchTargetCheck off shapes. -/
def switchCheckS (a : StSh) (old : SingleSh) (T : SwitchTarget) : Bool :=
  let codes := a.codes
  let s := T.shape
  let ell := (codes.base.getD old.code default).ell
  let mainBlock := 2 ^ T.main.bits
  let restBlock := 2 ^ T.rest.bits
  let kept := switchKeptS old
  old.masks == 2 &&
  decide (old.code < codes.base.size) && decide (old.maskCode < codes.mask.size) &&
  decide (s.code < codes.base.size) && decide (0 < s.mainRows) && s.mainDeg == 3 &&
  decide (1 ≤ s.answers) && (Send.pad codes s).isSome &&
  T.main.part == .main &&
  powerOfTwo ell &&
  T.main.firstRow % mainBlock == 0 && T.rest.firstRow % restBlock == 0 &&
  (match T.rest.part with
   | .mask =>
     decide (s.maskCode < codes.mask.size) && T.main.firstRow == 0 && mainBlock == s.mainRows &&
       T.rest.firstRow == 0 && restBlock == s.maskRows
   | .main =>
     s.maskRows == 0 && T.main.firstRow == 0 && T.rest.firstRow == mainBlock &&
       mainBlock + restBlock == s.mainRows) &&
  decide (mainBlock ≤ ell) && decide (ell ≤ (codes.base.getD s.code default).ell * mainBlock) &&
  decide ((switchPartsS a old).length ≤ (SwitchPlaces.make codes T).size) &&
  T.kept.size == kept.size &&
  (kept.zip T.kept).all fun p =>
    let o := shapeAtS a p.1
    let n := p.2.shape
    o.maskRows == 0 && n.maskRows == 0 && decide (n.code < codes.base.size) &&
      (Send.pad codes o).isSome &&
      n.mainRows == o.mainRows && n.mainDeg == o.mainDeg && n.answers == o.answers &&
      (codes.base.getD n.code default).ell == (codes.base.getD o.code default).ell

/-- **The library's test on the target hangs on the statement's shape and the single rows' make.**
-/
theorem switchCheck_sh (S : Statement) (old : SingleRows) (T : SwitchTarget) :
    switchTargetCheck S old T = switchCheckS (stSh S) (singleSh old) T := by
  unfold switchTargetCheck switchCheckS
  simp only [← switchParts_sh, ← shapeAt_sh]
  rfl

/-! ## 3 The stored rows read their member's main table alone -/

/-- readsMainOf on a make. -/
def readsMainS (o : Nat) (row : RowMk) : Bool :=
  (row.terms.all fun t => t.oracle == o && t.part == .main) &&
    (row.units.all fun u => u.oracle == o && u.part == .main) &&
    (row.runs.all fun r => r.oracle == o && r.part == .main) &&
    row.forms.all fun f => f.oracle == o

theorem readsMain_mk (o : Nat) (row : OnBytes.Row) :
    readsMainOf o row = readsMainS o (rowMk row) := by
  unfold readsMainOf readsMainS rowMk
  simp only [List.all_map, ← Array.all_toList]
  rfl

/-- At each kept member, each stored sample row. -/
def readsB (F : FormsSh) (old : SingleSh) : Bool :=
  (switchKeptS old).toList.all fun o => ((F.oracles[o]?).getD []).all (readsMainS o)

theorem readsB_iff (S : Statement) (old : SingleRows) :
    readsB (formsOf S) (singleSh old) = true ↔
      ∀ o ∈ (switchKept old).toList,
        ∀ r ∈ (S.oracles.getD o default).sampleRows.toList, readsMainOf o r = true := by
  unfold readsB
  rw [show switchKeptS (singleSh old) = switchKept old from rfl]
  simp only [stored_all, List.all_eq_true, readsMain_mk]

/-! ## 4 What is public of the claim in front -/

/-- OldFits, with code, off shapes. -/
def oldFitsB (a : StSh) (F : FormsSh) (old : SingleSh) : Bool :=
  (old.c.tensors.all fun v => v.pairs == (a.codes.base.getD old.code default).logEll) &&
    decide (old.d.getD 0 0 ≤ (a.codes.mask.getD old.maskCode default).ell) &&
    decide (old.d.getD 1 0 ≤ (a.codes.mask.getD old.maskCode default).ell) &&
    old.keptRows == ((switchKeptS old).toList.map fun o => (shapeAtS a o).mainRows).sum &&
    (old.kept.all fun f => (switchKeptS old).toList.contains f.1) &&
    decide (switchKeptS old).toList.Nodup &&
    ((switchKeptS old).toList.all fun o => (shapeAtS a o).code == old.code) &&
    (switchKeptS old).toList.all fun o =>
      ((F.oracles[o]?).getD []).all fun r => r.runs.isEmpty && r.forms.isEmpty

theorem oldFitsB_iff (S : Statement) (old : SingleRows) :
    oldFitsB (stSh S) (formsOf S) (singleSh old) = true ↔ OldFits S old := by
  have eK : switchKeptS (singleSh old) = switchKept old := rfl
  have e1 : ((singleSh old).c.tensors.all fun v =>
      v.pairs == ((stSh S).codes.base.getD (singleSh old).code default).logEll) = true ↔
      ∀ v ∈ old.c.tensors, v.vars = (S.codes.base.getD old.code default).logEll := by
    show ((old.c.tensors.map tensorSh).all _) = true ↔ _
    rw [List.all_map, List.all_eq_true]
    exact forall_congr' fun v => imp_congr Iff.rfl beq_iff_eq
  have e5 : ((singleSh old).kept.all fun f => (switchKept old).toList.contains f.1) = true ↔
      ∀ f ∈ old.kept.toList, f.oracle ∈ (switchKept old).toList := by
    show ((old.kept.toList.map fun k => (k.oracle, formSh k.c)).all _) = true ↔ _
    rw [List.all_map, List.all_eq_true]
    exact forall_congr' fun f => imp_congr Iff.rfl List.contains_iff_mem
  have e8 : ∀ r : OnBytes.Row, ((rowMk r).runs.isEmpty && (rowMk r).forms.isEmpty) = true ↔
      r.runs.size = 0 ∧ r.forms.size = 0 := by
    intro r
    show ((r.runs.toList.map runMk).isEmpty && (r.forms.toList.map mainMk).isEmpty) = true ↔ _
    rw [Bool.and_eq_true, List.isEmpty_map, List.isEmpty_map, List.isEmpty_iff, List.isEmpty_iff,
      ← List.length_eq_zero_iff, ← List.length_eq_zero_iff, Array.length_toList,
      Array.length_toList]
  unfold oldFitsB
  rw [eK]
  simp only [Bool.and_eq_true, e1, e5, stored_all, ← d_size, ← shapeAt_sh, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, e8]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨h.mainVars, h.d0⟩, h.d1⟩, h.rows⟩, h.named⟩, h.once⟩, h.keptCode⟩, h.stored⟩

/-! ## 5 The tables' sizes, the claim's forms, the stored sample rows -/

/-- TablesFit without its comparisons of field elements, off shapes. -/
def tablesB (a : StSh) (F : FormsSh) (old : SingleSh) (T : SwitchTarget) : Bool :=
  decide (switchRowBits T .main + (a.codes.base.getD T.shape.code default).logEll ≤ 63) &&
    ((switchKeptS old).toList.all fun o =>
      decide (ceilLog2 (shapeAtS a o).mainRows +
        (a.codes.base.getD old.code default).logEll ≤ 63)) &&
    formFitsS old.c (a.codes.base.getD old.code default).logEll &&
    (old.kept.all fun f => formFitsS f.2 (tableBitsS a f.1 .main)) &&
    (switchKeptS old).toList.all fun o =>
      ((F.oracles[o]?).getD []).all fun r =>
        (r.terms.all fun t => t.v.pairs == tableBitsS a o .main && tensorOrderS t.v) &&
          r.units.all fun u => decide (u.index < 2 ^ tableBitsS a o .main)

/-- **THE PART ON VALUES**: at each written-out variable the pair is (1, 1): in the carried forms
and in the terms of the kept members' stored sample rows. -/
def onesV (S : Statement) (old : SingleRows) : Bool :=
  onesF old.c && (old.kept.toList.all fun f => onesF f.c) &&
    (switchKept old).toList.all fun o =>
      (S.oracles.getD o default).sampleRows.toList.all fun r =>
        r.terms.toList.all fun t => onesT t.v

/-- **TablesFit just if the test on shapes and the part on values accept.** -/
theorem tablesFit_iff (S : Statement) (old : SingleRows) (T : SwitchTarget) :
    TablesFit S old T ↔
      tablesB (stSh S) (formsOf S) (singleSh old) T = true ∧ onesV S old = true := by
  have eK : switchKeptS (singleSh old) = switchKept old := rfl
  have e4 : ((singleSh old).kept.all fun f => formFitsS f.2 (S.tableBits f.1 .main)) =
      old.kept.toList.all fun f => formFitsS (formSh f.c) (S.tableBits f.oracle .main) := by
    show ((old.kept.toList.map fun k => (k.oracle, formSh k.c)).all _) = _
    rw [List.all_map]
    rfl
  have e5 : ∀ (o : Nat) (r : OnBytes.Row),
      (((rowMk r).terms.all fun t => t.v.pairs == S.tableBits o .main && tensorOrderS t.v) &&
        (rowMk r).units.all fun u => decide (u.index < 2 ^ S.tableBits o .main)) =
      ((r.terms.toList.all fun t =>
          t.v.pairs.length == S.tableBits o .main && tensorOrderS (tensorSh t.v)) &&
        r.units.toList.all fun u => decide (u.index < 2 ^ S.tableBits o .main)) := by
    intro o r
    show (((r.terms.toList.map termMk).all _) && ((r.units.toList.map unitMk).all _)) = _
    rw [List.all_map, List.all_map]
    rfl
  unfold tablesB onesV
  rw [eK]
  simp only [tableBitsS_eq, e4, stored_all, e5, ← shapeAt_sh, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    have c : formFitsS (formSh old.c) (S.codes.base.getD old.code default).logEll = true ∧
        onesF old.c = true := by
      have := h.claimMain
      rw [formFits_split, Bool.and_eq_true] at this
      exact this
    have k : ∀ f ∈ old.kept.toList,
        formFitsS (formSh f.c) (S.tableBits f.oracle .main) = true ∧ onesF f.c = true :=
      fun f hf => by
        have := h.claimKept f hf
        rw [formFits_split, Bool.and_eq_true] at this
        exact this
    have st : ∀ o ∈ (switchKept old).toList,
        ∀ r ∈ (S.oracles.getD o default).sampleRows.toList, ∀ t ∈ r.terms.toList,
          tensorOrderS (tensorSh t.v) = true ∧ onesT t.v = true := fun o ho r hr t ht => by
      have := (Own.tensorInOrder_iff _).2 ((h.stored o ho r hr).1 t ht).2
      rw [tensorInOrder_split, Bool.and_eq_true] at this
      exact this
    refine ⟨⟨⟨⟨⟨h.bitsG, fun o ho => ?_⟩, c.1⟩, fun f hf => (k f hf).1⟩, fun o ho r hr =>
      ⟨fun t ht => ⟨((h.stored o ho r hr).1 t ht).1, (st o ho r hr t ht).1⟩,
        (h.stored o ho r hr).2⟩⟩, ⟨c.2, fun f hf => (k f hf).2⟩,
      fun o ho r hr t ht => (st o ho r hr t ht).2⟩
    exact h.bitsKept _ (List.mem_map.2 ⟨o, ho, rfl⟩)
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, ⟨v1, v2⟩, v3⟩
    refine ⟨h1, fun s hs => ?_, ?_, fun f hf => ?_, fun o ho r hr =>
      ⟨fun t ht => ⟨((h5 o ho r hr).1 t ht).1, ?_⟩, (h5 o ho r hr).2⟩⟩
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hs
      exact h2 o ho
    · rw [formFits_split, Bool.and_eq_true]
      exact ⟨h3, v1⟩
    · rw [formFits_split, Bool.and_eq_true]
      exact ⟨h4 f hf, v2 f hf⟩
    · refine (Own.tensorInOrder_iff _).1 ?_
      rw [tensorInOrder_split, Bool.and_eq_true]
      exact ⟨((h5 o ho r hr).1 t ht).2, v3 o ho r hr t ht⟩

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.stored_all
#print axioms VerifiableInference.Desc.First.Shape.switchCheck_sh
#print axioms VerifiableInference.Desc.First.Shape.readsMain_mk
#print axioms VerifiableInference.Desc.First.Shape.readsB_iff
#print axioms VerifiableInference.Desc.First.Shape.oldFitsB_iff
#print axioms VerifiableInference.Desc.First.Shape.tablesFit_iff
