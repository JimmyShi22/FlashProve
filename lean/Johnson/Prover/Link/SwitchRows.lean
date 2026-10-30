-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/SwitchRows.lean: the rows that a code switch of the proximity test makes pass
the description's tests on a new open row, at every drawn position and every target.

The rows by name (OnBytes/Slice/BlkCsRows.lean): `carriedRow` (the old claim on the new tables),
`genMain` and `genMask` (a draw's three rows of generator matrices).

Main names (namespace `Johnson.Prover.Link`).
  `RowSeat S G W`   what the statement holds of the new message and of its group while the rows are
      added: no test has begun; the new message is the one member; its two tables have the frame's
      index bits, at most 63; the five carried stretches fit the mask table; every place of the
      pad lies in the mask table, behind the carried stretches
  `runs_restE`, `runs_restF`, `units_restE`, `units_restF`   what coefficients on a stretch add to a
      row
  `pieces_side`   a stretch among the carried ones is no piece, or one piece with the step 1
  `fits_lift`   a dense form on the old message, carried to the new main table, fits the table
  `clauses_carried`, `clauses_genMain`, `clauses_genMask`   the tests on a new open row, as
      sentences (`K9L.RowClauses`, Johnson/Desc/First/Batch/Law/DoorTests.lean), at the three kinds
      of rows
  `RowSeat.withRow`   the seat rides through an added row
  `add_yes`   rows that meet the sentences at every seat are all added
  `made_add`   every row that the switch makes (`switchRows`) is added, at every list of positions
      below the old code's length and all symbols read

Limits. `FrameOK` and `RowSeat` are asked. The old claim's form is asked to be dense (`DenseForm`).
Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchOrder
import Johnson.Prover.Link.FormRow
import Johnson.Prover.Link.FormPads
import Johnson.Prover.Link.FormDoorLaws
import Johnson.Prover.Link.FormRowsLaws
import OnBytes.Slice.BlkCsPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc
open OnBytes.Slice.ProxRun (DenseForm denseForm_switchLift denseForm_of_plain)

/-- What the statement holds of the new message and of its group while the rows are added. -/
structure RowSeat (S : Statement) (G : Group) (W : SwitchFrame) : Prop where
  noTest : G.inRun = false
  member : G.members = #[W.g]
  main : S.has W.g .main = true ∧ S.tableBits W.g .main = W.tableBits
  mask : S.has W.g .mask = true ∧ S.tableBits W.g .mask = W.restBits
  small : W.tableBits ≤ 63 ∧ W.restBits ≤ 63
  room : 2 * W.zk.ell + W.code.r + 2 * W.zk.r ≤ 2 ^ W.restBits
  pads : ∀ q ∈ ((S.oracles[W.g]?).map (·.pad)).getD [], q.1 = .mask ∧
    2 * W.zk.ell + W.code.r + 2 * W.zk.r ≤ q.2 ∧ q.2 < 2 ^ W.restBits

/-! ## What coefficients on a stretch add -/

theorem runs_restE (g : ℕ) (part : Part) (coeff : Array E) : ∀ (pieces : List SwitchPiece)
    (row : Row), (switchAddRestE row g part pieces coeff).runs = row.runs ++
      (pieces.map fun p => (⟨g, part, p.first, p.step,
        .own (coeff.extract p.start p.stop)⟩ : Run)).toArray
  | [], row => by simp [switchAddRestE]
  | p :: pieces, row => by
    show (switchAddRestE (row.addRun g part p.first p.step (.own (coeff.extract p.start p.stop)))
      g part pieces coeff).runs = _
    rw [runs_restE g part coeff pieces]
    simp [Row.addRun]

theorem runs_restF (g : ℕ) (part : Part) (coeff : Array F) : ∀ (pieces : List SwitchPiece)
    (row : Row), (switchAddRestF row g part pieces coeff).runs = row.runs ++
      (pieces.map fun p => (⟨g, part, p.first, p.step,
        .stretch coeff p.start (p.stop - p.start)⟩ : Run)).toArray
  | [], row => by simp [switchAddRestF]
  | p :: pieces, row => by
    show (switchAddRestF (row.addRun g part p.first p.step
      (.stretch coeff p.start (p.stop - p.start))) g part pieces coeff).runs = _
    rw [runs_restF g part coeff pieces]
    simp [Row.addRun]

theorem units_restE (g : ℕ) (part : Part) (coeff : Array E) : ∀ (pieces : List SwitchPiece)
    (row : Row), (switchAddRestE row g part pieces coeff).units = row.units
  | [], _ => rfl
  | p :: pieces, row =>
    units_restE g part coeff pieces
      (row.addRun g part p.first p.step (.own (coeff.extract p.start p.stop)))

theorem units_restF (g : ℕ) (part : Part) (coeff : Array F) : ∀ (pieces : List SwitchPiece)
    (row : Row), (switchAddRestF row g part pieces coeff).units = row.units
  | [], _ => rfl
  | p :: pieces, row =>
    units_restF g part coeff pieces
      (row.addRun g part p.first p.step (.stretch coeff p.start (p.stop - p.start)))

variable {S : Statement} {G : Group} {W : SwitchFrame}

/-- A stretch among the carried ones: no piece, or one piece with the step 1. -/
theorem pieces_side (hW : FrameOK W) (first count : ℕ)
    (h : first + count ≤ 2 * W.zk.ell + W.code.r + 2 * W.zk.r) :
    switchPieces W.places first count = if count = 0 then [] else [⟨0, count, first, 1⟩] := by
  by_cases c : count = 0
  · subst c
    rfl
  · rw [if_neg c]
    exact switchPieces_flat W.places first count first (Nat.pos_of_ne_zero c)
      (hW.side first count h)

/-- A place on the new mask table. -/
theorem place_mask (hS : RowSeat S G W) (i : ℕ) (hi : i < 2 ^ W.restBits) :
    Blk.placeOk S G W.g .mask (S.tableBits W.g .mask) i = true :=
  (Means.placeOk_iff _ _ _ _ _ _).2 ⟨by rw [hS.member]; simp, hS.mask.1, rfl, by
    rw [hS.mask.2]
    exact hi⟩

/-- A place on the new main table. -/
theorem place_main (hS : RowSeat S G W) (i : ℕ) (hi : i < 2 ^ W.tableBits) :
    Blk.placeOk S G W.g .main (S.tableBits W.g .main) i = true :=
  (Means.placeOk_iff _ _ _ _ _ _).2 ⟨by rw [hS.member]; simp, hS.main.1, rfl, by
    rw [hS.main.2]
    exact hi⟩

/-- **A dense form on the old message, carried to the new main table, fits the table.** -/
theorem fits_lift (hW : FrameOK W) (hs : W.tableBits ≤ 63) (c : Form)
    (hc : Means.CFits W.code.logEll c) (hp : DenseForm c) :
    (switchLift c W.code.logEll W.mainCut W.rowBits W.tableBits).fits W.tableBits = true := by
  rw [Own.formFits_agrees]
  refine formFits_of_cfits ?_ (denseForm_switchLift hp _ _ _ _) hs
  unfold switchLift
  rw [hW.cut]
  show Means.CFits W.tableBits ((c.insertChoice W.rowBits (W.rowBits - W.rowBits)
    (0 / 2 ^ W.rowBits)).insertChoice (W.code.logEll + (W.rowBits - W.rowBits))
    (W.tableBits - (W.code.logEll + (W.rowBits - W.rowBits))) 0)
  rw [Nat.sub_self, Nat.add_zero]
  have e1 : W.rowBits + (W.code.logEll - W.rowBits) = W.code.logEll :=
    Nat.add_sub_cancel' hW.rowBits
  have h1 : Means.CFits (W.rowBits + 0 + (W.code.logEll - W.rowBits))
      (c.insertChoice W.rowBits 0 (0 / 2 ^ W.rowBits)) :=
    Means.CFits.insertChoice (by rw [e1]; exact hc) 0 _
  rw [Nat.add_zero, e1] at h1
  have h2 : Means.CFits (W.code.logEll + (W.tableBits - W.code.logEll) + 0)
      ((c.insertChoice W.rowBits 0 (0 / 2 ^ W.rowBits)).insertChoice W.code.logEll
        (W.tableBits - W.code.logEll) 0) :=
    Means.CFits.insertChoice (by rw [Nat.add_zero]; exact h1) _ 0
  rw [Nat.add_zero, Nat.add_sub_cancel' hW.tableBits] at h2
  exact h2

/-- The clause on a run, at one piece of a carried stretch. -/
theorem run_clause (hS : RowSeat S G W) (first count : ℕ) (c : Coeffs) (hok : c.ok = true)
    (hsz : c.size = count) (h0 : count ≠ 0)
    (h : first + count ≤ 2 * W.zk.ell + W.code.r + 2 * W.zk.r) :
    c.ok = true ∧ 0 < c.size ∧ 1 ≤ 1 ∧
      Blk.placeOk S G W.g .mask (S.tableBits W.g .mask) (first + 1 * (c.size - 1)) = true := by
  refine ⟨hok, by omega, Nat.le_refl 1, place_mask hS _ ?_⟩
  have := hS.room
  omega

/-- A coefficient that reads as 0 has the words 0. -/
theorem zero_of_coefAt (r : Row) (o : ℕ) (pt : Part) (i : ℕ) (h : coefAt r o pt i = 0) :
    isZeroE (r.coefficient o pt i) = true :=
  isZero_of_val r o pt i h

theorem cut_ge (n : ℕ) (F : ℕ → GE) (j : ℕ) (h : n ≤ j) : OnBytes.Slice.cut n F j = 0 :=
  if_neg (by omega)

theorem moved_at (o : ℕ) (F : ℕ → GE) (j : ℕ) (h : o ≤ j) : moved o F j = F (j - o) := if_pos h

theorem wM_ge (C : Fmt.M1.Code) (x j : ℕ) (h : C.l ≤ j) : wM C x j = 0 := if_neg (by omega)

theorem wT_ge (C : Fmt.M1.Code) (x j : ℕ) (h : C.r ≤ j) : wT C x j = 0 := if_neg (by omega)

/-- The clause on a run. -/
def RunOk (S : Statement) (G : Group) (w : Run) : Prop :=
  w.coeffs.ok = true ∧ 0 < w.coeffs.size ∧ 1 ≤ w.step ∧
    Blk.placeOk S G w.oracle w.part (S.tableBits w.oracle w.part)
      (w.first + w.step * (w.coeffs.size - 1)) = true

/-- The runs of a carried stretch over the extension field. -/
theorem runsE_ok (hW : FrameOK W) (hS : RowSeat S G W) (first : ℕ) (coeff : Array E)
    (h : first + coeff.size ≤ 2 * W.zk.ell + W.code.r + 2 * W.zk.r) :
    ∀ w ∈ (switchPieces W.places first coeff.size).map fun p =>
      (⟨W.g, W.restPart, p.first, p.step, .own (coeff.extract p.start p.stop)⟩ : Run),
      RunOk S G w := by
  intro w hw
  rw [pieces_side hW _ _ h] at hw
  by_cases c : coeff.size = 0
  · rw [if_pos c] at hw
    cases hw
  · rw [if_neg c] at hw
    obtain rfl := List.mem_singleton.1 hw
    unfold RunOk
    rw [hW.rest]
    exact run_clause hS first coeff.size _ rfl (by
      show (coeff.extract 0 coeff.size).size = _
      simp) c h

/-- The runs of a carried stretch over the base field. -/
theorem runsF_ok (hW : FrameOK W) (hS : RowSeat S G W) (first count : ℕ) (coeff : Array F)
    (hsz : coeff.size = count)
    (h : first + count ≤ 2 * W.zk.ell + W.code.r + 2 * W.zk.r) :
    ∀ w ∈ (switchPieces W.places first count).map fun p =>
      (⟨W.g, W.restPart, p.first, p.step, .stretch coeff p.start (p.stop - p.start)⟩ : Run),
      RunOk S G w := by
  intro w hw
  rw [pieces_side hW _ _ h] at hw
  by_cases c : count = 0
  · rw [if_pos c] at hw
    cases hw
  · rw [if_neg c] at hw
    obtain rfl := List.mem_singleton.1 hw
    unfold RunOk
    rw [hW.rest]
    exact run_clause hS first count _ (by
      show decide (0 + (count - 0) ≤ coeff.size) = true
      rw [hsz]
      simp) rfl c h

/-- The clause on the pads, from the coefficients on the new mask table. -/
theorem pads_clause (hS : RowSeat S G W) (r : Row)
    (h : ∀ i, 2 * W.zk.ell + W.code.r + 2 * W.zk.r ≤ i → i < 2 ^ W.restBits →
      coefAt r W.g .mask i = 0) :
    ∀ o ∈ G.members, ∀ q ∈ ((S.oracles[o]?).map (·.pad)).getD [],
      isZeroE (r.coefficient o q.1 q.2) = true := by
  intro o ho q hq
  rw [hS.member] at ho
  obtain rfl : o = W.g := by simpa using ho
  obtain ⟨q1, q2, q3⟩ := hS.pads q hq
  rw [q1]
  exact zero_of_coefAt r W.g .mask q.2 (h q.2 q2 q3)

/-- **The carried claim passes the tests.** -/
theorem clauses_carried (hW : FrameOK W) (hS : RowSeat S G W) (old : SingleRows)
    (hd0 : (old.d.getD 0 #[]).size = W.zk.ell) (hd1 : (old.d.getD 1 #[]).size = W.zk.ell)
    (hc : Means.CFits W.code.logEll old.c) (hp : DenseForm old.c) :
    K9L.RowClauses S G (carriedRow W old) where
  noTest := hS.noTest
  noSample := by
    rw [kind_carriedRow]
    exact fun h => by cases h
  terms := fun t ht => by
    have e : (carriedRow W old).terms = #[] :=
      (terms_restE _ _ _ _ _).trans (terms_restE _ _ _ _ _)
    rw [e] at ht
    simp at ht
  units := fun u hu => by
    have e : (carriedRow W old).units = #[] :=
      (units_restE _ _ _ _ _).trans (units_restE _ _ _ _ _)
    rw [e] at hu
    simp at hu
  runs := fun w hw => by
    have e : (carriedRow W old).runs = _ :=
      (runs_restE _ _ _ _ _).trans (congrArg (· ++ _) (runs_restE _ _ _ _ _))
    rw [e, hW.at0, hW.at1] at hw
    simp only [Array.mem_append, List.mem_toArray] at hw
    rcases hw with (hw | hw) | hw
    · simp [Row.addForm] at hw
    · exact runsE_ok hW hS 0 _ (by rw [hd0]; omega) w hw
    · exact runsE_ok hW hS W.zk.ell _ (by rw [hd1]; omega) w hw
  forms := fun f hf => by
    have e : (carriedRow W old).forms = #[⟨W.g, switchLift old.c W.code.logEll W.mainCut W.rowBits
        W.tableBits⟩] := (forms_restE _ _ _ _ _).trans (forms_restE _ _ _ _ _)
    rw [e] at hf
    obtain rfl : f = _ := by simpa using hf
    refine ⟨place_main hS 0 (Nat.two_pow_pos _), ?_⟩
    show (switchLift _ _ _ _ _).fits (S.tableBits W.g .main) = true
    rw [hS.main.2]
    exact fits_lift hW hS.small.1 old.c hc hp
  pads := pads_clause hS _ fun i hi _ => by
    rw [carried_mask hW old hd0 hd1 i]
    rw [cut_ge _ _ _ (by omega), moved_at _ _ _ (by omega), cut_ge _ _ _ (by omega), add_zero]

/-- **The main code's generator row passes the tests.** -/
theorem clauses_genMain (hW : FrameOK W) (hS : RowSeat S G W) (x : ℕ) (hx : x < 2 ^ W.code.logN)
    (t : E) : K9L.RowClauses S G (genMain W x t) where
  noTest := hS.noTest
  noSample := fun h => by cases h
  terms := fun u hu => by
    have e : (genMain W x t).terms = #[] := terms_restF _ _ _ _ _
    rw [e] at hu
    simp at hu
  units := fun u hu => by
    have e : (genMain W x t).units = #[] := units_restF _ _ _ _ _
    rw [e] at hu
    simp at hu
  runs := fun w hw => by
    have e : (genMain W x t).runs = _ := runs_restF _ _ _ _ _
    rw [e, hW.mainTail] at hw
    simp only [Array.mem_append, List.mem_toArray] at hw
    rcases hw with hw | hw
    · simp [Row.addForm] at hw
    · exact runsF_ok hW hS (2 * W.zk.ell) W.code.r _ (size_generatorTail _ _) (by omega) w hw
  forms := fun f hf => by
    have e : (genMain W x t).forms = #[⟨W.g, switchLift (Form.ofTensor (messageTensor W.code x))
        W.code.logEll W.mainCut W.rowBits W.tableBits⟩] := forms_restF _ _ _ _ _
    rw [e] at hf
    obtain rfl : f = _ := by simpa using hf
    refine ⟨place_main hS 0 (Nat.two_pow_pos _), ?_⟩
    show (switchLift _ _ _ _ _).fits (S.tableBits W.g .main) = true
    rw [hS.main.2]
    exact fits_lift hW hS.small.1 _
      ⟨fun v hv => by
        rw [List.mem_singleton.1 hv]
        exact vars_messageTensor W.code x hW.powC, fun e he => by cases he⟩
      (denseForm_of_plain (plainForm_ofTensor (plain_messageTensor W.code x)))
  pads := pads_clause hS _ fun i hi _ => by
    rw [genMain_mask hW x hx t i, moved_at _ _ _ (by omega)]
    exact wT_ge _ _ _ (by
      show W.code.r ≤ _
      omega)

/-- **A mask code's generator row passes the tests.** a: where the mask row's tail begins. -/
theorem clauses_genMask_at (hW : FrameOK W) (hS : RowSeat S G W) (x j a : ℕ) (hj2 : j < 2)
    (hj : W.parts.maskAt.getD j 0 + W.zk.ell ≤ 2 * W.zk.ell)
    (ht : W.maskTail.getD j [] = switchPieces W.places a W.zk.r)
    (ha : a + W.zk.r ≤ 2 * W.zk.ell + W.code.r + 2 * W.zk.r) (t : E) :
    K9L.RowClauses S G (genMask W x j t) := by
  have hpads : ∀ o ∈ G.members, ∀ q ∈ ((S.oracles[o]?).map (·.pad)).getD [],
      isZeroE ((genMask W x j t).coefficient o q.1 q.2) = true :=
    pads_clause hS _ fun i hi hi' => by
      rw [genMask_mask hW x j a hj2 hj ht ha t i hi', moved_at _ _ _ (by omega),
        moved_at _ _ _ (by omega), wM_ge _ _ _ (by
          show W.zk.ell ≤ _
          omega), wT_ge _ _ _ (by
          show W.zk.r ≤ _
          omega), add_zero]
  have htail : ∀ w ∈ (W.maskTail.getD j []).map fun p =>
      (⟨W.g, W.restPart, p.first, p.step, .stretch (generatorTail W.zk
        (shortPosition W.zk.logN x)) p.start (p.stop - p.start)⟩ : Run), RunOk S G w := by
    rw [ht]
    exact runsF_ok hW hS a W.zk.r _ (size_generatorTail _ _) ha
  cases hb : W.box.getD j none with
  | some b =>
    obtain ⟨hbox, hpow⟩ := hW.box j b hb
    obtain ⟨rfl, -⟩ := switchBox_some W.places _ _ b
      (fun e he => hW.side _ W.zk.ell (by omega) e (by rw [hpow]; exact he)) hbox
    have hle : W.zk.logEll + 1 ≤ W.restBits := by
      have h2 := hW.restBits
      rw [hpow, ← pow_succ'] at h2
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 h2
    have hvars : (switchOnBox ⟨0, W.parts.maskAt.getD j 0⟩
        (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll W.restBits).vars =
        W.restBits := by
      show (((messageTensor W.zk (shortPosition W.zk.logN x)).insertChoice 0 0
        (W.parts.maskAt.getD j 0 % 2 ^ 0)).insertChoice (0 + W.zk.logEll)
        (W.restBits - 0 - W.zk.logEll) (W.parts.maskAt.getD j 0 / 2 ^ (0 + W.zk.logEll))).vars = _
      have h0 := vars_messageTensor W.zk (shortPosition W.zk.logN x) hpow
      have h1 : ((messageTensor W.zk (shortPosition W.zk.logN x)).insertChoice 0 0
          (W.parts.maskAt.getD j 0 % 2 ^ 0)).vars = W.zk.logEll := by
        rw [Tensor.vars_insertChoice _ _ _ _ (Nat.zero_le _), h0]
        rfl
      rw [Tensor.vars_insertChoice _ _ _ _ (by rw [h1]; omega), h1]
      omega
    have eT : (genMask W x j t).terms = #[⟨W.g, W.restPart, switchOnBox
        ⟨0, W.parts.maskAt.getD j 0⟩ (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll
        W.restBits⟩] := by
      unfold genMask
      rw [hb]
      exact terms_restF _ _ _ _ _
    have eU : (genMask W x j t).units = #[] := by
      unfold genMask
      rw [hb]
      exact units_restF _ _ _ _ _
    have eR : (genMask W x j t).runs = (({} : Row).add W.g W.restPart (switchOnBox
        ⟨0, W.parts.maskAt.getD j 0⟩ (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll
        W.restBits)).runs ++ ((W.maskTail.getD j []).map fun p =>
          (⟨W.g, W.restPart, p.first, p.step, .stretch (generatorTail W.zk
            (shortPosition W.zk.logN x)) p.start (p.stop - p.start)⟩ : Run)).toArray := by
      unfold genMask
      rw [hb]
      exact runs_restF _ _ _ _ _
    have eF : (genMask W x j t).forms = #[] := by
      unfold genMask
      rw [hb]
      exact forms_restF _ _ _ _ _
    exact
      { noTest := hS.noTest, noSample := fun h => by cases h
        terms := fun u hu => by
          rw [eT] at hu
          obtain rfl := Array.mem_singleton.1 hu
          refine ⟨ok_of_plain (plain_switchOnBox _ (plain_messageTensor _ _) _ _) (by
            show (switchOnBox _ _ _ _).vars ≤ 63
            rw [hvars]
            exact hS.small.2), ?_⟩
          show Blk.placeOk S G W.g W.restPart (switchOnBox _ _ _ _).vars 0 = true
          rw [hvars, hW.rest, ← hS.mask.2]
          exact place_mask hS 0 (Nat.two_pow_pos _)
        units := fun u hu => by
          rw [eU] at hu
          simp at hu
        runs := fun w hw => by
          rw [eR] at hw
          simp only [Array.mem_append, List.mem_toArray] at hw
          rcases hw with hw | hw
          · simp [Row.add] at hw
          · exact htail w hw
        forms := fun f hf => by
          rw [eF] at hf
          simp at hf
        pads := hpads }
  | none =>
    have hmsg := hW.msg j hj2 hb
    have eT : (genMask W x j t).terms = #[] := by
      unfold genMask
      rw [hb]
      exact (terms_restF _ _ _ _ _).trans (terms_restF _ _ _ _ _)
    have eU : (genMask W x j t).units = #[] := by
      unfold genMask
      rw [hb]
      exact (units_restF _ _ _ _ _).trans (units_restF _ _ _ _ _)
    have eR : (genMask W x j t).runs = (({} : Row).runs ++ ((W.maskMessage.getD j []).map fun p =>
          (⟨W.g, W.restPart, p.first, p.step, .stretch (generatorMessage W.zk
            (shortPosition W.zk.logN x)) p.start (p.stop - p.start)⟩ : Run)).toArray) ++
        ((W.maskTail.getD j []).map fun p =>
          (⟨W.g, W.restPart, p.first, p.step, .stretch (generatorTail W.zk
            (shortPosition W.zk.logN x)) p.start (p.stop - p.start)⟩ : Run)).toArray := by
      unfold genMask
      rw [hb]
      exact (runs_restF _ _ _ _ _).trans (congrArg (· ++ _) (runs_restF _ _ _ _ _))
    have eF : (genMask W x j t).forms = #[] := by
      unfold genMask
      rw [hb]
      exact (forms_restF _ _ _ _ _).trans (forms_restF _ _ _ _ _)
    exact
      { noTest := hS.noTest, noSample := fun h => by cases h
        terms := fun u hu => by
          rw [eT] at hu
          simp at hu
        units := fun u hu => by
          rw [eU] at hu
          simp at hu
        runs := fun w hw => by
          rw [eR, hmsg] at hw
          simp only [Array.mem_append, List.mem_toArray] at hw
          rcases hw with (hw | hw) | hw
          · simp at hw
          · exact runsF_ok hW hS _ W.zk.ell _ (size_generatorMessage _ _) (by omega) w hw
          · exact htail w hw
        forms := fun f hf => by
          rw [eF] at hf
          simp at hf
        pads := hpads }

/-- The same at the two mask rows. -/
theorem clauses_genMask (hW : FrameOK W) (hS : RowSeat S G W) (x j : ℕ) (hj : j < 2) (t : E) :
    K9L.RowClauses S G (genMask W x j t) := by
  have h0 := hW.at0
  have h1 := hW.at1
  obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  · exact clauses_genMask_at hW hS x 0 _ hj (by omega) hW.tail0 (by omega) t
  · exact clauses_genMask_at hW hS x 1 _ hj (by omega) hW.tail1 (by omega) t

/-- **The seat rides through an added row.** -/
theorem RowSeat.withRow (hS : RowSeat S G W) (g : ℕ) (r : Row) :
    RowSeat (Slice.withRow S g r) { G with rows := G.rows.push r } W :=
  ⟨hS.noTest, hS.member, hS.main, hS.mask, hS.small, hS.room, hS.pads⟩

/-- **Rows that meet the sentences at every seat are all added.** -/
theorem add_yes (g : ℕ) : ∀ (l : List Row) (S : Statement) (G : Group),
    S.groups[g]? = some G → RowSeat S G W →
    (∀ r ∈ l, ∀ S' G', RowSeat S' G' W → K9L.RowClauses S' G' r) →
    l.foldlM (fun S r => Tw.L9.addRowS S g r) S = .ok (withRows S g l)
  | [], _, _, _, _, _ => rfl
  | r :: l, S, G, hG, hS, hl => by
    have h1 : Tw.L9.addRowS S g r = .ok (Slice.withRow S g r) :=
      (addRowS_iff S _ g r).2 ⟨by
        unfold Ground.ok
        exact List.all_eq_true.2 (rowL_of_clauses S g G r hG
          (hl r (List.mem_cons_self) S G hS)), rfl⟩
    have hG' : (Slice.withRow S g r).groups[g]? = some { G with rows := G.rows.push r } := by
      show (S.groups.modify g _)[g]? = _
      rw [Array.getElem?_modify, if_pos rfl, hG]
      rfl
    rw [List.foldlM_cons, h1]
    exact add_yes g l _ _ hG' (hS.withRow g r) fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')

/-- **Every row that the switch makes is added**, at every list of positions and all symbols. -/
theorem made_add {gp g : ℕ} {old : SingleRows} {T : SwitchTarget} {pos : Positions} {y : Array E}
    {l : List Row} (hG : S.groups[gp]? = some G) (hW0 : switchFrame S old T g #[] = some W)
    (hW : FrameOK W) (hS : RowSeat S G W) (hk : old.kept = #[]) (hm : old.masks = 2)
    (hd0 : (old.d.getD 0 #[]).size = W.zk.ell) (hd1 : (old.d.getD 1 #[]).size = W.zk.ell)
    (hc : Means.CFits W.code.logEll old.c) (hp : DenseForm old.c)
    (hx : ∀ x ∈ pos.draws.toList, x < 2 ^ W.code.logN)
    (h : switchRows S old T g #[] pos y = some l) :
    l.foldlM (fun S r => Tw.L9.addRowS S gp r) S = .ok (withRows S gp l) := by
  obtain ⟨W', hW', rfl⟩ := switchRows_eq S old T g pos y l hk hm
    (fun W1 h1 => by
      obtain rfl := Option.some.inj (hW0.symm.trans h1)
      exact hW.kept) h
  obtain rfl := Option.some.inj (hW0.symm.trans hW')
  refine add_yes gp _ S G hG hS fun r hr S' G' hS' => ?_
  rcases List.mem_cons.1 hr with rfl | hr
  · exact clauses_carried hW hS' old hd0 hd1 hc hp
  · obtain ⟨x, hx', hr⟩ := List.mem_flatMap.1 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact clauses_genMain hW hS' x (hx x hx') _
    · exact clauses_genMask hW hS' x 0 (by decide) _
    · exact clauses_genMask hW hS' x 1 (by decide) _

end Johnson.Prover.Link
