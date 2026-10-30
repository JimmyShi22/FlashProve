-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepK2Rows.lean: the code switch (kind K2) asks two public tests (targetL,
Johnson/Top/H0/Tw/K2/Target.lean; rowsCanL, K2/RowsCan.lean) and makes the new group's rows (swRows,
Johnson/Desc/Own/SwitchRows.lean). This file shows that the tests read no row's target and none of the symbols' values,
and that targets and symbols reach the new rows only in their targets. Seven definitions with code; the rest are
theorems.

Words. The wiped copy of a statement, of a row or of the carried rows is the same value with each target set to zero
(wipeSt, wipeRow: Honest/K10/StAtZero.lean; singleRowsWithZeroTarget: Honest/K10/WipeS.lean). The two sides compared are: a statement,
the carried rows and an array of symbols; and a statement with the same wiped copy, the carried rows wiped, and an array
of symbols of the same size. A row's target is its right side; the plan's SwitchTarget (the letters T and G.target) is
another thing: the codes and shapes of the group to which a switch leads.

What is proved.
  targetL_wipe, targetL_rel   the named clauses tested before the sending are the same list on both sides, so the answer
                 and the name of the first failing clause are the same (switchGuard_rel, targetWhy_rel)
  rowsCanL_rel   so are the named clauses under which the rows can be made (rowsCan_rel, rowsWhy_rel); of the symbols
                 they read only the number
  swFrame_st, swFrame_old   the switch's frame is the same on both sides
  swCarried_old, swOldSamples_st, switchGenerators_rel   each of the three sorts of new rows differs between the two
                 sides at most in targets; the symbols go into the generator rows' targets and nowhere else
  **swRows_rel**   swRows returns nothing on both sides, or lists of rows that differ at most in their targets

By what. Each function is unfolded. What reads the statement is rewritten by the lemmas of Honest/K10/BatWipe.lean; what
reads the carried rows reads fields that singleRowsWithZeroTarget leaves as they are. The text of switchGenerators (OnBytes/Iop/Cs.lean)
is restated as three named pieces whose last step, which sets kind and target, is a parameter; switchGenerators_eq shows
by unfolding that the pieces put together are switchGenerators.

Limits. Nothing is said about any target's value. The theorems hold for all arguments, whether or not a run can reach
them. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK2Cols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E Statement Oracle Row Form Tensor Positions SingleRows SwitchTarget SwitchFrame KeptPlace zeroE ofF
  ceilLog2 switchKept switchParts padOf padPlaces switchGenerators switchAddRestF switchLift switchOnBox generatorAt
  generatorTail generatorMessage shortPosition)
open VerifiableInference.Desc.Own (swFormOn swFrame swCarried swOldSamples swRows)
open Tw.K2 (readsMainOf rowsCanL rowsCan rowsWhy targetL targetOk targetWhy switchGuard)

/-! ## 1 General laws -/

/-- `List.foldl` from start values equal under φ, with steps that keep this, ends in values equal under φ. -/
theorem foldlRel {α β γ : Type} (φ : β → γ) (f f' : β → α → β)
    (h : ∀ b b' a, φ b = φ b' → φ (f b a) = φ (f' b' a)) :
    ∀ (l : List α) (b b' : β), φ b = φ b' → φ (l.foldl f b) = φ (l.foldl f' b')
  | [], _, _, hb => hb
  | a :: l, b, b', hb => foldlRel φ f f' h l _ _ (h b b' a hb)

/-- Mapping two functions whose values are equal under φ at every entry gives lists equal under φ. -/
theorem mapMapRel {α β γ : Type} (φ : β → γ) (g g' : α → β) (h : ∀ a, φ (g a) = φ (g' a)) (l : List α) :
    (l.map g).map φ = (l.map g').map φ := by
  rw [List.map_map, List.map_map]
  exact congrArg (fun k => l.map k) (funext h)

/-- `List.mapM f` over `l.map ψ` and `List.mapM f'` over l give lists equal under φ if `f (ψ a)` and `f' a` are equal
under φ for every a. -/
theorem swMapLmap {α β γ : Type} (φ : β → γ) (ψ : α → α) (f f' : α → Option β)
    (h : ∀ a, (f (ψ a)).map φ = (f' a).map φ) :
    ∀ l : List α, ((l.map ψ).mapM f).map (List.map φ) = (l.mapM f').map (List.map φ)
  | [] => by rw [List.map_nil, List.mapM_nil, List.mapM_nil]
  | a :: l => by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons]
    refine bind_rel φ (List.map φ) (h a) fun b b' hb => ?_
    refine bind_rel (List.map φ) (List.map φ) (swMapLmap φ ψ f f' h l) fun t t' ht => ?_
    show some ((b :: t).map φ) = some ((b' :: t').map φ)
    rw [List.map_cons, List.map_cons, hb, ht]

/-- `wipeRow` gives the same row whatever the target was. -/
theorem wipeRow_target (r : Row) (t : E) : wipeRow { r with target := t } = wipeRow r := rfl

/-! ## 2 An oracle message of the wiped statement, by number, with the blank where there is none -/

/-- Wiping the default oracle message changes nothing: it has no sample row. -/
theorem wipeOr_default : wipeOr (default : Oracle) = default := by
  have e : (default : Oracle).sampleRows.map wipeRow = (default : Oracle).sampleRows := by
    show (#[] : Array Row).map wipeRow = #[]
    exact Array.map_empty
  unfold wipeOr
  rw [e]

/-- Looking up a message by number (the default where there is none) in the wiped statement gives the wiped message. -/
theorem getD_wipe (S : Statement) (o : Nat) :
    (wipeSt S).oracles.getD o default = wipeOr (S.oracles.getD o default) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, wipeSt_oracle_at]
  cases S.oracles[o]? with
  | none => exact wipeOr_default.symm
  | some x => rfl

/-- That message has the same shape in the statement and in its wiped copy. -/
theorem getD_shape (S : Statement) (o : Nat) :
    ((wipeSt S).oracles.getD o default).shape = (S.oracles.getD o default).shape := by
  rw [getD_wipe]
  rfl

/-- Its sample rows in the wiped statement are its sample rows, each wiped. -/
theorem rowsList_wipe (S : Statement) (o : Nat) :
    ((wipeSt S).oracles.getD o default).sampleRows.toList =
      (S.oracles.getD o default).sampleRows.toList.map wipeRow := by
  rw [getD_wipe]
  show ((S.oracles.getD o default).sampleRows.map wipeRow).toList = _
  rw [Array.toList_map]

/-! ## 3 The layouts that both tests and the frame call -/

/-- `switchKept` does not read the carried rows' target. -/
theorem switchKept_old (old : SingleRows) : switchKept (singleRowsWithZeroTarget old) = switchKept old := by
  unfold OnBytes.switchKept
  rfl

/-- Nor does `SingleRows.rows`. -/
theorem rows_old (old : SingleRows) : (singleRowsWithZeroTarget old).rows = old.rows := by
  unfold OnBytes.SingleRows.rows
  rfl

/-- `padOf` is the same at a statement and at its wiped copy. -/
theorem padOf_wipe (S : Statement) (o : Nat) : padOf (wipeSt S) o = padOf S o := by
  unfold OnBytes.padOf
  rw [getD_shape]
  rfl

/-- So is `switchParts`. -/
theorem switchParts_st (S : Statement) (old : SingleRows) : switchParts (wipeSt S) old = switchParts S old := by
  unfold OnBytes.switchParts
  simp only [padOf_wipe]
  rfl

/-- `switchParts` does not read the carried rows' target. -/
theorem switchParts_old (S : Statement) (old : SingleRows) : switchParts S (singleRowsWithZeroTarget old) = switchParts S old := by
  unfold OnBytes.switchParts
  simp only [switchKept_old]
  rfl

/-! ## 4 The public test in front of the sending -/

/-- **`targetL`, the list of named clauses tested before the sending, is the same list after the statement and the
carried rows are wiped.** -/
theorem targetL_wipe (S : Statement) (old : SingleRows) (T : SwitchTarget) :
    targetL (wipeSt S) (singleRowsWithZeroTarget old) T = targetL S old T := by
  unfold Tw.K2.targetL
  simp only [switchParts_st, switchParts_old, switchKept_old, getD_shape]
  rfl

/-- So it is the same list at two statements and two carried rows that have the same wiped copies. -/
theorem targetL_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') {old old' : SingleRows}
    (ho : singleRowsWithZeroTarget old = singleRowsWithZeroTarget old') (T : SwitchTarget) : targetL S old T = targetL S' old' T := by
  rw [← targetL_wipe S old T, ← targetL_wipe S' old' T, hS, ho]

/-- Hence `switchGuard` gives the same answer. -/
theorem switchGuard_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') {old old' : SingleRows}
    (ho : singleRowsWithZeroTarget old = singleRowsWithZeroTarget old') (T : SwitchTarget) : switchGuard S old T = switchGuard S' old' T := by
  unfold Tw.K2.switchGuard Tw.K2.targetOk
  rw [targetL_rel hS ho T]

/-- And `targetWhy` names the same failing clause. -/
theorem targetWhy_rel {S S' : Statement} (hS : wipeSt S = wipeSt S') {old old' : SingleRows}
    (ho : singleRowsWithZeroTarget old = singleRowsWithZeroTarget old') (T : SwitchTarget) : targetWhy S old T = targetWhy S' old' T := by
  unfold Tw.K2.targetWhy
  rw [targetL_rel hS ho T]

/-! ## 5 The conditions under which the rows can be made -/

/-- `readsMainOf` does not read a row's target. -/
theorem readsMainOf_wipe (o : Nat) (r : Row) : readsMainOf o (wipeRow r) = readsMainOf o r := by
  unfold Tw.K2.readsMainOf
  rfl

/-- Whether all sample rows of a message pass `readsMainOf` is the same at a statement and at its wiped copy. -/
theorem readsAll_wipe (S : Statement) (o k : Nat) :
    ((wipeSt S).oracles.getD o default).sampleRows.toList.all (readsMainOf k) =
      (S.oracles.getD o default).sampleRows.toList.all (readsMainOf k) := by
  rw [rowsList_wipe, List.all_map]
  exact congrArg (fun g => (S.oracles.getD o default).sampleRows.toList.all g) (funext (readsMainOf_wipe k))

/-- `rowsCanL` is the same list at a statement and at its wiped copy. -/
theorem rowsCanL_st (S : Statement) (old : SingleRows) (T : SwitchTarget) (anew : Array Nat) (pos : Positions)
    (y : Array E) : rowsCanL (wipeSt S) old T anew pos y = rowsCanL S old T anew pos y := by
  unfold Tw.K2.rowsCanL
  simp only [readsAll_wipe]
  rfl

/-- `rowsCanL` does not read the carried rows' target. -/
theorem rowsCanL_old (S : Statement) (old : SingleRows) (T : SwitchTarget) (anew : Array Nat) (pos : Positions)
    (y : Array E) : rowsCanL S (singleRowsWithZeroTarget old) T anew pos y = rowsCanL S old T anew pos y := by
  unfold Tw.K2.rowsCanL
  simp only [switchKept_old, rows_old]
  rfl

/-- Of the array of symbols `rowsCanL` reads only the size. -/
theorem rowsCanL_y (S : Statement) (old : SingleRows) (T : SwitchTarget) (anew : Array Nat) (pos : Positions)
    {y y' : Array E} (hy : y'.size = y.size) : rowsCanL S old T anew pos y' = rowsCanL S old T anew pos y := by
  unfold Tw.K2.rowsCanL
  rw [hy]

/-- **`rowsCanL`, the list of named clauses under which the new rows can be made, is the same list on both sides.** -/
theorem rowsCanL_rel {S S' : Statement} (hS : wipeSt S' = wipeSt S) (old : SingleRows) (T : SwitchTarget)
    (anew : Array Nat) (pos : Positions) {y y' : Array E} (hy : y'.size = y.size) :
    rowsCanL S' (singleRowsWithZeroTarget old) T anew pos y' = rowsCanL S old T anew pos y := by
  rw [rowsCanL_old, rowsCanL_y S' old T anew pos hy, ← rowsCanL_st S', ← rowsCanL_st S, hS]

/-- Hence `rowsCan` gives the same answer. -/
theorem rowsCan_rel {S S' : Statement} (hS : wipeSt S' = wipeSt S) (old : SingleRows) (T : SwitchTarget)
    (anew : Array Nat) (pos : Positions) {y y' : Array E} (hy : y'.size = y.size) :
    rowsCan S' (singleRowsWithZeroTarget old) T anew pos y' = rowsCan S old T anew pos y := by
  unfold Tw.K2.rowsCan
  rw [rowsCanL_rel hS old T anew pos hy]

/-- And `rowsWhy` names the same failing clause. -/
theorem rowsWhy_rel {S S' : Statement} (hS : wipeSt S' = wipeSt S) (old : SingleRows) (T : SwitchTarget)
    (anew : Array Nat) (pos : Positions) {y y' : Array E} (hy : y'.size = y.size) :
    rowsWhy S' (singleRowsWithZeroTarget old) T anew pos y' = rowsWhy S old T anew pos y := by
  unfold Tw.K2.rowsWhy
  rw [rowsCanL_rel hS old T anew pos hy]

/-! ## 6 The switch's frame -/

/-- `swFrame` is the same at a statement and at its wiped copy. -/
theorem swFrame_st (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat) (anew : Array Nat) :
    swFrame (wipeSt S) old T g anew = swFrame S old T g anew := by
  unfold VerifiableInference.Desc.Own.swFrame
  simp only [switchParts_st, tableBits_wipe, rowBits_wipe, getD_shape, padOf_wipe]
  rfl

/-- `swFrame` does not read the carried rows' target. -/
theorem swFrame_old (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat) (anew : Array Nat) :
    swFrame S (singleRowsWithZeroTarget old) T g anew = swFrame S old T g anew := by
  unfold VerifiableInference.Desc.Own.swFrame
  simp only [switchParts_old, switchKept_old]
  rfl

/-! ## 7 The old claim and the old sample rows, carried over -/

/-- **`swCarried`, with and without the carried rows' target,** returns nothing at both, or rows that differ at most in
the target. -/
theorem swCarried_old (W : SwitchFrame) (old : SingleRows) :
    (swCarried W (singleRowsWithZeroTarget old)).map wipeRow = (swCarried W old).map wipeRow := by
  unfold VerifiableInference.Desc.Own.swCarried
  refine bind_rel id wipeRow rfl fun b b' hb => ?_
  have hb' : b = b' := hb
  subst hb'
  exact congrArg some ((wipeRow_target _ _).trans (wipeRow_target _ _).symm)

/-- `swFormOn` does not read a row's target. -/
theorem swFormOn_wipe (o : Nat) (r : Row) : swFormOn o (wipeRow r) = swFormOn o r := by
  unfold VerifiableInference.Desc.Own.swFormOn
  rfl

/-- The row that `swOldSamples` makes of one sample row changes at most in its target if that sample row is wiped first.
-/
theorem oldSample_wipe (W : SwitchFrame) (k : KeptPlace) (r : Row) :
    ((swFormOn k.old (wipeRow r)).bind fun c =>
        some ({ W.addKept {} k c with target := (wipeRow r).target } : Row)).map wipeRow =
      ((swFormOn k.old r).bind fun c => some ({ W.addKept {} k c with target := r.target } : Row)).map wipeRow := by
  rw [swFormOn_wipe]
  refine obindRel id wipeRow rfl fun c c' hc => ?_
  have hc' : c = c' := hc
  subst hc'
  exact congrArg some ((wipeRow_target (W.addKept {} k c) _).trans (wipeRow_target (W.addKept {} k c) _).symm)

/-- **`swOldSamples`, at a statement and at its wiped copy,** returns nothing at both, or rows that differ at most in
their targets. -/
theorem swOldSamples_st (S : Statement) (W : SwitchFrame) :
    (swOldSamples (wipeSt S) W).map (List.map wipeRow) = (swOldSamples S W).map (List.map wipeRow) := by
  unfold VerifiableInference.Desc.Own.swOldSamples
  refine omapRel (List.map (List.map wipeRow)) (List.map wipeRow)
    (swMapL (List.map wipeRow) _ _ (fun k => ?_) W.kept) fun a a' ha => ?_
  · rw [rowsList_wipe]
    exact swMapLmap wipeRow wipeRow _ _ (fun r => oldSample_wipe W k r) _
  · rw [List.map_flatten, List.map_flatten, ha]

/-! ## 8 The generator rows -/

/-- The last step in making a generator row: it sets the kind and the target (`finish` in `switchGenerators`). -/
def genFin (symbols : Nat → E) (r : Row) (row : Nat) : Row := { r with kind := .generator, target := symbols row }

/-- With two different functions of symbols `genFin` gives rows that differ at most in the target. -/
theorem genFin_wipe (f f' : Nat → E) (r : Row) (n : Nat) : wipeRow (genFin f r n) = wipeRow (genFin f' r n) := rfl

/-- The generator row's form on a message of the old main code (`onMessage` in `switchGenerators`). -/
def genMsg (W : SwitchFrame) (x : Nat) : Form :=
  Form.ofTensor (Tensor.product ((generatorAt W.code x).f.take W.code.logEll) (ofF (generatorAt W.code x).messageScale))

/-- The main row's generator row, before `genFin`. -/
def genMain (W : SwitchFrame) (x : Nat) : Row :=
  switchAddRestF (({} : Row).addForm W.g (switchLift (genMsg W x) W.code.logEll W.mainCut W.rowBits W.tableBits))
    W.g W.restPart W.mainTail (generatorTail W.code x)

/-- One step of the loop over kept rows: one more generator row at the head of the list, and the count raised by one.
fin: the last step. -/
def genStep (fin : Row → Nat → Row) (W : SwitchFrame) (x : Nat) (k : KeptPlace) (s : List Row × Nat) (b : Nat) :
    List Row × Nat :=
  (fin (switchAddRestF (W.addKept {} k ((genMsg W x).insertChoice 0 k.rowBits b)) W.g W.restPart
      (W.keptTail.getD s.2 []) (generatorTail W.code x)) (1 + s.2) :: s.1, s.2 + 1)

/-- The generator rows of the kept rows. -/
def genKept (fin : Row → Nat → Row) (W : SwitchFrame) (x : Nat) : List Row :=
  (W.kept.foldl (fun (s : List Row × Nat) (k : KeptPlace) => (List.range k.rows).foldl (genStep fin W x k) s)
    ([], 0)).1.reverse

/-- The generator rows of the mask rows. -/
def genMasks (fin : Row → Nat → Row) (W : SwitchFrame) (masks keptRows x : Nat) : List Row :=
  (List.range masks).map fun j =>
    fin (switchAddRestF
      (match W.box.getD j none with
        | some b =>
          ({} : Row).add W.g W.restPart
            (switchOnBox b
              (Tensor.product ((generatorAt W.zk (shortPosition W.zk.logN x)).f.take (ceilLog2 W.zk.ell))
                (ofF (generatorAt W.zk (shortPosition W.zk.logN x)).messageScale))
              (ceilLog2 W.zk.ell) W.restBits)
        | none =>
          switchAddRestF {} W.g W.restPart (W.maskMessage.getD j [])
            (generatorMessage W.zk (shortPosition W.zk.logN x)))
      W.g W.restPart (W.maskTail.getD j []) (generatorTail W.zk (shortPosition W.zk.logN x))) (1 + keptRows + j)

/-- **`switchGenerators` is these three pieces put together**, with `genFin symbols` as the last step. -/
theorem switchGenerators_eq (W : SwitchFrame) (old : SingleRows) (x : Nat) (symbols : Nat → E) :
    switchGenerators W old x symbols =
      genFin symbols (genMain W x) 0 :: genKept (genFin symbols) W x ++
        genMasks (genFin symbols) W old.masks old.keptRows x := rfl

/-- What is compared of the state of the loop over kept rows: the rows with their targets wiped, and the count. -/
def shK (s : List Row × Nat) : List Row × Nat := (s.1.map wipeRow, s.2)

/-- `genStep` keeps loop states equal under `shK` if the two last steps give rows that differ at most in the target. -/
theorem genStep_rel {fin fin' : Row → Nat → Row} (h : ∀ r n, wipeRow (fin r n) = wipeRow (fin' r n))
    (W : SwitchFrame) (x : Nat) (k : KeptPlace) {s s' : List Row × Nat} (hs : shK s = shK s') (b : Nat) :
    shK (genStep fin W x k s b) = shK (genStep fin' W x k s' b) := by
  obtain ⟨l, n⟩ := s
  obtain ⟨l', n'⟩ := s'
  have h1 : l.map wipeRow = l'.map wipeRow := (congrArg (fun z : List Row × Nat => z.1) hs :)
  have h2 : n = n' := (congrArg (fun z : List Row × Nat => z.2) hs :)
  subst h2
  show (wipeRow (fin _ (1 + n)) :: l.map wipeRow, n + 1) = (wipeRow (fin' _ (1 + n)) :: l'.map wipeRow, n + 1)
  rw [h, h1]

/-- Then `genKept` gives rows that differ at most in their targets. -/
theorem genKept_rel {fin fin' : Row → Nat → Row} (h : ∀ r n, wipeRow (fin r n) = wipeRow (fin' r n))
    (W : SwitchFrame) (x : Nat) : (genKept fin W x).map wipeRow = (genKept fin' W x).map wipeRow := by
  have k : shK (W.kept.foldl
        (fun (s : List Row × Nat) (k : KeptPlace) => (List.range k.rows).foldl (genStep fin W x k) s) ([], 0)) =
      shK (W.kept.foldl
        (fun (s : List Row × Nat) (k : KeptPlace) => (List.range k.rows).foldl (genStep fin' W x k) s) ([], 0)) :=
    foldlRel shK _ _
      (fun s s' k hs => foldlRel shK _ _ (fun t t' b ht => genStep_rel h W x k ht b) (List.range k.rows) s s' hs)
      W.kept _ _ rfl
  unfold genKept
  rw [List.map_reverse, List.map_reverse]
  exact congrArg List.reverse (congrArg (fun z : List Row × Nat => z.1) k :)

/-- And so does `genMasks`. -/
theorem genMasks_rel {fin fin' : Row → Nat → Row} (h : ∀ r n, wipeRow (fin r n) = wipeRow (fin' r n))
    (W : SwitchFrame) (masks keptRows x : Nat) :
    (genMasks fin W masks keptRows x).map wipeRow = (genMasks fin' W masks keptRows x).map wipeRow := by
  unfold genMasks
  exact mapMapRel wipeRow _ _ (fun j => h _ _) _

/-- **`switchGenerators` gives rows that differ at most in their targets, whatever the symbols are**, with or without
the carried rows' target. -/
theorem switchGenerators_rel (W : SwitchFrame) (old : SingleRows) (x : Nat) (f f' : Nat → E) :
    (switchGenerators W (singleRowsWithZeroTarget old) x f').map wipeRow = (switchGenerators W old x f).map wipeRow := by
  rw [switchGenerators_eq, switchGenerators_eq, List.map_append, List.map_append, List.map_cons, List.map_cons,
    genKept_rel (genFin_wipe f' f) W x, genMasks_rel (genFin_wipe f' f) W _ _ x, genFin_wipe f' f]
  rfl

/-! ## 9 The rows of a code switch -/

/-- **`swRows`** returns nothing on both sides, or lists of rows that differ at most in their targets. -/
theorem swRows_rel {S S' : Statement} (hS : wipeSt S' = wipeSt S) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (pos : Positions) {y y' : Array E} (hy : y'.size = y.size) :
    (swRows S' (singleRowsWithZeroTarget old) T g anew pos y').map (List.map wipeRow) =
      (swRows S old T g anew pos y).map (List.map wipeRow) := by
  have hF : swFrame S' (singleRowsWithZeroTarget old) T g anew = swFrame S old T g anew := by
    rw [swFrame_old, ← swFrame_st S', ← swFrame_st S, hS]
  have hO : ∀ W, (swOldSamples S' W).map (List.map wipeRow) = (swOldSamples S W).map (List.map wipeRow) :=
    fun W => by rw [← swOldSamples_st S', ← swOldSamples_st S, hS]
  unfold VerifiableInference.Desc.Own.swRows
  rw [hF, hy, rows_old]
  refine bind_rel id _ rfl fun _ _ _ => ?_
  refine bind_rel id _ rfl fun W W' hW => ?_
  have hW' : W = W' := hW
  subst hW'
  refine bind_rel wipeRow _ (swCarried_old W old) fun c c' hc => ?_
  refine bind_rel (List.map wipeRow) _ (hO W) fun s s' hs => ?_
  refine bind_rel (List.map (List.map wipeRow)) _ (swMapL (List.map wipeRow) _ _ (fun x => ?_) _)
    fun G G' hG => ?_
  · refine bind_rel id _ rfl fun i i' hi => ?_
    have hi' : i = i' := hi
    subst hi'
    exact congrArg some (switchGenerators_rel W old x _ _)
  · show some ((c :: s ++ G.flatten).map wipeRow) = some ((c' :: s' ++ G'.flatten).map wipeRow)
    rw [List.map_append, List.map_append, List.map_cons, List.map_cons, List.map_flatten, List.map_flatten, hc, hs,
      hG]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.foldlRel
#print axioms ProofFile.Honest.K10.mapMapRel
#print axioms ProofFile.Honest.K10.swMapLmap
#print axioms ProofFile.Honest.K10.wipeRow_target
#print axioms ProofFile.Honest.K10.wipeOr_default
#print axioms ProofFile.Honest.K10.getD_wipe
#print axioms ProofFile.Honest.K10.getD_shape
#print axioms ProofFile.Honest.K10.rowsList_wipe
#print axioms ProofFile.Honest.K10.switchKept_old
#print axioms ProofFile.Honest.K10.rows_old
#print axioms ProofFile.Honest.K10.padOf_wipe
#print axioms ProofFile.Honest.K10.switchParts_st
#print axioms ProofFile.Honest.K10.switchParts_old
#print axioms ProofFile.Honest.K10.targetL_wipe
#print axioms ProofFile.Honest.K10.targetL_rel
#print axioms ProofFile.Honest.K10.switchGuard_rel
#print axioms ProofFile.Honest.K10.targetWhy_rel
#print axioms ProofFile.Honest.K10.readsMainOf_wipe
#print axioms ProofFile.Honest.K10.readsAll_wipe
#print axioms ProofFile.Honest.K10.rowsCanL_st
#print axioms ProofFile.Honest.K10.rowsCanL_old
#print axioms ProofFile.Honest.K10.rowsCanL_y
#print axioms ProofFile.Honest.K10.rowsCanL_rel
#print axioms ProofFile.Honest.K10.rowsCan_rel
#print axioms ProofFile.Honest.K10.rowsWhy_rel
#print axioms ProofFile.Honest.K10.swFrame_st
#print axioms ProofFile.Honest.K10.swFrame_old
#print axioms ProofFile.Honest.K10.swCarried_old
#print axioms ProofFile.Honest.K10.swFormOn_wipe
#print axioms ProofFile.Honest.K10.oldSample_wipe
#print axioms ProofFile.Honest.K10.swOldSamples_st
#print axioms ProofFile.Honest.K10.genFin
#print axioms ProofFile.Honest.K10.genFin_wipe
#print axioms ProofFile.Honest.K10.genMsg
#print axioms ProofFile.Honest.K10.genMain
#print axioms ProofFile.Honest.K10.genStep
#print axioms ProofFile.Honest.K10.genKept
#print axioms ProofFile.Honest.K10.genMasks
#print axioms ProofFile.Honest.K10.switchGenerators_eq
#print axioms ProofFile.Honest.K10.shK
#print axioms ProofFile.Honest.K10.genStep_rel
#print axioms ProofFile.Honest.K10.genKept_rel
#print axioms ProofFile.Honest.K10.genMasks_rel
#print axioms ProofFile.Honest.K10.switchGenerators_rel
#print axioms ProofFile.Honest.K10.swRows_rel
