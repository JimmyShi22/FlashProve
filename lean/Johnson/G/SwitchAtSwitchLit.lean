-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchAtSwitchLit.lean: a member of the record `AtSwitch`
(Johnson/Top/H0/K2Hands/Paid.lean) at each written record of a code switch, AT VALUES MADE HERE OF
THE RECORD.

`AtSwitch` is the one record from which four records of premises of the code switch's last join
follow (`Fit`, `FrameOK`, `Names`, `NamesK`, `Slots`: `AtSwitch.fit`, `paid_frame`, `paid_names`,
`paid_namesK`, `paid_slots`). It has sixteen clauses: of the program's frame and test, of the
sending's list, of the typed stage, of the slots, of the messages' numbers. There it is a premise,
shown at no value. Here all sixteen are met together at each written record
(Johnson/Top/H0/K2Caller/Lit.lean): by one test with code that Lean's kernel evaluates, and by the
record's own promise `SwRow.OK` for the slots. Definitions, statements and proofs.
Main names:
  `stF r`, `stB r`: a statement in front of the sending and one behind it, MADE HERE: the record's
    codes; as oracle messages those of the list in front, each with its shape and one stored sample
    row (`rowAt`: the program's `Send.form` at the seed `seedAt`, target zero); in `stB` then those
    of the sending, shapes alone (so g, the first sent message, stands in it under the number
    r.lo.length). `stB_front`: the one begins with the other. The two routines are called at `stB`.
    `oldAt`, `tgtAt`, `anewAt`, `numAt`: those of Johnson/G/SwitchFitLit.lean. `plB r i`: the record
    of kept member number i in the frame at that statement.
  `atB r`: the test, fourteen clauses. `AtOK`, `atB_says`: what its yes says.
  `atB_full`, `atB_small`: it says yes at each of the 25 and the 5 written records.
  `atB_no_first`, `atB_no_swap`, `atB_no_more`: controls: it says no with the first sent message
    struck out; with two kept places in the other order (12 records keep two); with one place more
    among the kept.
  `frame_g`, `kept_of_frame`, `kept_at`: the number of g and the kept members' records of a frame.
  `slotsAll_at`: `SlotsAll` (Johnson/Top/H0/K2Hands/Numbering.lean) at the caller's slots: each slot
    has its member's record; its row is one of the member's; two slots with one member and one row
    are one; every row of every kept member has a slot.
  `atSwitch_at`: `AtSwitch` from the test's yes. **`atSwitch_full`**, `atSwitch_small`: at each
    written record, at every t₀, oM, oZ, with ids i := r.lo.length + i. `atSwitch_closed_full`,
    `atSwitch_closed_small`: the same with the record's promise H paid (`tableFullLit_ok`,
    `ok_says`): no premise is left (`AtRec`: the record's `AtSwitch` under one name). The test
    reads the stage at t₀ := 0; the stage's two codes do not hang on t₀ (by unfolding `stageOf`).
  `paid_at`: what follows there: `Fit`, `FrameOK`, and each kept member's record and `Slots`.
Limits: THE STATEMENT, THE SINGLE ROWS AND THE TARGET ARE MADE HERE, OF THE RECORD's SHAPES: THEY
ARE NO RUN's. In a run the oracle messages have the chain's running numbers, the statement holds
more than shapes, the single rows come out of a fold, and the test is asked at the statement in
front of the sending (Paid.lean's Limits). So Paid.lean's sentence "nothing here shows that a run of
the programs meets it" stands as it was. What is shown: the sixteen clauses do not shut each other
out at the written sizes. The target follows the rule of the program's `reqGroupAt` by reading. At
the last record of each table nothing is kept: the clauses on kept members ask nothing there. The
records are written numbers (Lit.lean's limits). Nothing on soundness.

-/
import Johnson.G.SwitchFitLit
import Johnson.Top.H0.K2Hands.Paid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc.First.K2Caller VerifiableInference.Desc.First.K2Hands

/-- A seed, made here: a point of 64 zeros and the factor one. -/
def seedAt : SampleSeed := ⟨List.replicate 64 zeroE, oneE⟩

/-- The sample row that the program's `Send.form` makes at that seed for the message number i of the
list in front, with the target zero. -/
def rowAt (r : SwRow) (i : ℕ) : Row :=
  { (Send.form r.cs (r.lo.getD i default).1 i seedAt 0).getD {} with target := zeroE }

/-- The record of the message number i of the list in front: its shape and that one stored sample
row. -/
def oracleAt (r : SwRow) (i : ℕ) : Oracle :=
  { shape := (r.lo.getD i default).1, sampleRows := #[rowAt r i] }

/-- A statement of the program IN FRONT OF the sending, made of the record: its codes; its oracle
messages are those of the list in front; the number of a message is its place. -/
def stF (r : SwRow) : Statement :=
  { codes := r.cs, oracles := (Array.range r.lo.length).map (oracleAt r) }

/-- The statement BEHIND the sending: the same, and then the sending's messages, with their shapes
and nothing else. -/
def stB (r : SwRow) : Statement :=
  { codes := r.cs
    oracles := (Array.range (r.lo.length + r.l.length)).map fun i =>
      if i < r.lo.length then oracleAt r i
      else ({ shape := (r.l.getD (i - r.lo.length) default).1 } : Oracle) }

/-- The statement behind holds the statement in front as its beginning. -/
theorem stB_front (r : SwRow) (i : ℕ) (h : i < r.lo.length) :
    (stB r).oracles.getD i default = (stF r).oracles.getD i default := by
  show ((Array.range _).map _).getD i default = ((Array.range _).map _).getD i default
  rw [getD_map_range, getD_map_range, if_pos h, if_pos (by omega), if_pos h]

theorem stF_size (r : SwRow) : (stF r).oracles.size = r.lo.length := by
  show ((Array.range _).map _).size = _
  simp

theorem stF_at (r : SwRow) (i : ℕ) (h : i < r.lo.length) :
    (stF r).oracles.getD i default = oracleAt r i := by
  show ((Array.range _).map _).getD i default = _
  rw [getD_map_range, if_pos h]

/-- The record of the kept member number i in the frame that the program makes at that statement. -/
def plB (r : SwRow) (i : ℕ) : KeptPlace :=
  { old := (switchKept (oldAt r)).getD i noId, anew := (anewAt r).getD i noId
    rows := ((stB r).oracles.getD ((switchKept (oldAt r)).getD i noId) default).shape.mainRows
    rowBits := (stB r).rowBits ((switchKept (oldAt r)).getD i noId) .main
    pad := padOf (stB r) ((switchKept (oldAt r)).getD i noId)
    oldPadAt := (switchParts (stB r) (oldAt r)).oldPadAt.getD i 0 }

/-- **The test.** -/
def atB (r : SwRow) : Bool :=
  switchTargetCheck (stB r) (oldAt r) (tgtAt r) &&
  (switchFrame (stB r) (oldAt r) (tgtAt r) r.lo.length (anewAt r)).isSome &&
  decide ((r.cs.base[codeIx r]?).map codeOf = some (stageOf r.g 0).C) &&
  decide ((r.cs.mask[r.rider.maskCode]?).map codeOf = some (stageOf r.g 0).Z) &&
  decide (switchKept (oldAt r) = r.kept.toArray) &&
  ((List.range r.kept.length).all fun i =>
    decide ((r.l[1 + i]?).map (·.1) = ((tgtAt r).kept[i]?).map (·.shape))) &&
  decide (r.keptRows = (((List.range r.kept.length).map (plB r)).map (·.rows)).sum) &&
  ((List.range r.kept.length).all fun i =>
    decide ((plB r i).rows = ((r.lo[r.kept.getD i 0]?).map (·.1.mainRows)).getD 0)) &&
  ((List.range r.kept.length).all fun i =>
    decide ((r.cs.base.getD ((stB r).oracles.getD (plB r i).old default).shape.code default).ell =
      (r.cs.base.getD (codeIx r) default).ell)) &&
  decide (((stB r).oracles[r.lo.length]?).map (·.shape) = some (tgtAt r).shape) &&
  decide ((r.cs.base.getD (codeIx r) default).logN ≤ 32) &&
  decide ((r.cs.mask.getD r.rider.maskCode default).logN ≤ 32) &&
  ((List.range r.kept.length).all fun i => decide (0 < (plB r i).rows)) &&
  ((List.range r.kept.length).all fun i => decide ((plB r i).anew = r.lo.length + (1 + i)))

set_option maxRecDepth 1000000 in
theorem atB_full : (tableFullLit.all atB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem atB_small : (tableSmallLit.all atB) = true := by decide +kernel

/-- What its yes says. -/
structure AtOK (r : SwRow) : Prop where
  check : switchTargetCheck (stB r) (oldAt r) (tgtAt r) = true
  frame : (switchFrame (stB r) (oldAt r) (tgtAt r) r.lo.length (anewAt r)).isSome = true
  main : (r.cs.base[codeIx r]?).map codeOf = some (stageOf r.g 0).C
  mask : (r.cs.mask[r.rider.maskCode]?).map codeOf = some (stageOf r.g 0).Z
  kept : switchKept (oldAt r) = r.kept.toArray
  copy : ∀ i, i < r.kept.length →
    (r.l[1 + i]?).map (·.1) = ((tgtAt r).kept[i]?).map (·.shape)
  sum : r.keptRows = (((List.range r.kept.length).map (plB r)).map (·.rows)).sum
  rows : ∀ i, i < r.kept.length →
    (plB r i).rows = ((r.lo[r.kept.getD i 0]?).map (·.1.mainRows)).getD 0
  ell : ∀ i, i < r.kept.length →
    (r.cs.base.getD ((stB r).oracles.getD (plB r i).old default).shape.code default).ell =
      (r.cs.base.getD (codeIx r) default).ell
  gRec : ((stB r).oracles[r.lo.length]?).map (·.shape) = some (tgtAt r).shape
  c32 : (r.cs.base.getD (codeIx r) default).logN ≤ 32
  z32 : (r.cs.mask.getD r.rider.maskCode default).logN ≤ 32
  pos : ∀ i, i < r.kept.length → 0 < (plB r i).rows
  anew : ∀ i, i < r.kept.length → (plB r i).anew = r.lo.length + (1 + i)

theorem atB_says {r : SwRow} (h : atB r = true) : AtOK r := by
  unfold atB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩, j⟩, k⟩, l⟩, m⟩, n⟩, o⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o⟩

/-- The number of g in a frame is the number that the routine was handed. -/
theorem frame_g (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ) (anew : Array ℕ)
    (W : SwitchFrame) (h : switchFrame S old T g anew = some W) : W.g = g := by
  unfold switchFrame at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨code, -, zk, -, nc, -, -, -, rfl⟩ := h
  rfl

section
variable (r : SwRow) (H : r.OK) (K : AtOK r) (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ)

set_option quotPrecheck false in
local notation "KpR" => ((rowsPort r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀)
  (H.hZ t₀)).keep r.kp).Kp
set_option quotPrecheck false in
local notation "memR" =>
  slotNum r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp (numAt r)
set_option quotPrecheck false in
local notation "rowR" =>
  slotRow r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
set_option quotPrecheck false in
local notation "plR" => slotPl r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
  fun a => plB r (numAt r a)

include K in
/-- The kept members' records of a frame that the routine returns at these values. -/
theorem kept_of_frame (W : SwitchFrame)
    (hW : switchFrame (stB r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) = some W) :
    W.kept = (List.range r.kept.length).map (plB r) := by
  obtain ⟨-, -, -, -, -, -, -, f8⟩ := frame_fields _ _ _ _ _ W hW
  have hsz : (switchKept (oldAt r)).size = r.kept.length := by rw [K.kept]; rfl
  rw [f8, hsz]
  rfl

include K in
theorem kept_at (W : SwitchFrame)
    (hW : switchFrame (stB r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) = some W) (a : ℕ)
    (k : KeptPlace) (hk : W.kept[a]? = some k) : a < r.kept.length ∧ k = plB r a := by
  rw [kept_of_frame r K W hW] at hk
  exact range_map_at _ _ _ _ hk

include K in
/-- **The slots at the record**: `SlotsAll` (Johnson/Top/H0/K2Hands/Numbering.lean). -/
theorem slotsAll_at (W : SwitchFrame)
    (hW : switchFrame (stB r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) = some W) :
    SlotsAll (KpR) W (memR) (rowR) (plR) where
  member := fun κ => by
    show W.kept[numAt r κ.1]? = some (plB r (numAt r κ.1))
    rw [kept_of_frame r K W hW, List.getElem?_map, List.getElem?_range (numAt_lt r κ.1)]
    rfl
  rowIn := fun κ => by
    show κ.2.val < (plB r (numAt r κ.1)).rows
    rw [K.rows _ (numAt_lt r κ.1), numAt_get, List.getElem?_eq_getElem κ.1.1.1.isLt]
    exact κ.2.isLt
  two := fun κ κ' hm hr => by
    obtain ⟨α, b⟩ := κ
    obtain ⟨α', b'⟩ := κ'
    obtain rfl : α = α' := numAt_inj r α α' hm
    have : b = b' := Fin.ext hr
    rw [this]
  all := fun a k b hk hb => by
    obtain ⟨ha, rfl⟩ := kept_at r K W hW a k hk
    have hin : r.kept[a] ∈ r.kept := List.getElem_mem ha
    have hx := H.kept _ hin
    obtain ⟨x, hx1, hx2⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨hl, hx3⟩ := List.getElem?_eq_some_iff.1 hx1
    have hmem : r.mem ⟨r.kept[a], hl⟩ := by
      show (r.lo.get ⟨r.kept[a], hl⟩).1.mainRows ≠ 0
      have : r.lo.get ⟨r.kept[a], hl⟩ = x := hx3
      rw [this]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hx2
      exact hx2.1
    have hnum : numAt r ⟨⟨⟨r.kept[a], hl⟩, hmem⟩, hin⟩ = a := H.nodup.idxOf_getElem a ha
    have hb' : b < (r.lo.get ⟨r.kept[a], hl⟩).1.mainRows := by
      have h := K.rows a ha
      rw [List.getD_eq_getElem _ _ ha, List.getElem?_eq_getElem hl] at h
      rw [h] at hb
      exact hb
    exact ⟨⟨⟨⟨⟨r.kept[a], hl⟩, hmem⟩, hin⟩, ⟨b, hb'⟩⟩, hnum, rfl⟩

include K in
/-- **The one record `AtSwitch` (Johnson/Top/H0/K2Hands/Paid.lean) at the record's made values.**
ids: the message number i of the sending has the number r.lo.length + i. -/
theorem atSwitch_at : ∃ W, AtSwitch (stB r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) W r.l
    (stageOf r.g t₀) (KpR) (memR) (rowR) (plR) (fun i => r.lo.length + i) := by
  obtain ⟨W, hW⟩ := Option.isSome_iff_exists.1 K.frame
  obtain ⟨f1, f2, -, -, -, -, -, -⟩ := frame_fields _ _ _ _ _ W hW
  have f1' : r.cs.base[codeIx r]? = some W.code := f1
  have f2' : r.cs.mask[r.rider.maskCode]? = some W.zk := f2
  have e1 : r.cs.base.getD (codeIx r) default = W.code := by
    rw [Array.getD_eq_getD_getElem?, f1']
    rfl
  have e2 : r.cs.mask.getD r.rider.maskCode default = W.zk := by
    rw [Array.getD_eq_getD_getElem?, f2']
    rfl
  have hg : W.g = r.lo.length := frame_g _ _ _ _ _ W hW
  have g0 : 0 < r.l.length := List.length_pos_iff.2 H.ne
  have hhead : ∀ (l : List (OracleShape × ℕ)) (g0 : 0 < l.length),
      (l.get ⟨0, g0⟩).1 = (l.headD default).1 := by
    intro l g0
    cases l with
    | nil => cases g0
    | cons x xs => rfl
  refine ⟨W, ⟨hW, K.check, ?_, e1 ▸ K.c32, e2 ▸ K.z32, ?_, ?_, ?_, ⟨g0, hhead r.l g0⟩, ?_, ?_, ?_,
    slotsAll_at r H K t₀ oM oZ W hW, ?_, ?_, ?_⟩⟩
  · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 K.gRec
    exact ⟨x, hx, e⟩
  · show r.keptRows = _
    rw [kept_of_frame r K W hW]
    exact K.sum
  · intro a k hk
    obtain ⟨ha, rfl⟩ := kept_at r K W hW a k hk
    exact K.pos a ha
  · intro a k hk
    obtain ⟨ha, rfl⟩ := kept_at r K W hW a k hk
    rw [← e1]
    exact K.ell a ha
  · intro i hi
    have hi' : i < r.kept.length := by
      have : (tgtAt r).kept.size = r.kept.length := by simp [tgtAt]
      omega
    have h := K.copy i hi'
    rw [Array.getElem?_eq_getElem hi, Option.map_some] at h
    obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hl, e2⟩ := List.getElem?_eq_some_iff.1 hx
    exact ⟨hl, by show (r.l[1 + i]).1 = _; rw [e2, e]⟩
  · have h := K.main
    rw [f1', Option.map_some] at h
    exact (Option.some.inj h).symm
  · have h := K.mask
    rw [f2', Option.map_some] at h
    exact (Option.some.inj h).symm
  · intro n
    rw [hg]
    constructor <;> intro h <;> omega
  · intro a k hk n
    obtain ⟨ha, rfl⟩ := kept_at r K W hW a k hk
    rw [K.anew a ha]
    constructor <;> intro h <;> omega
  · intro a k hk
    obtain ⟨ha, rfl⟩ := kept_at r K W hW a k hk
    rw [K.anew a ha, hg]
    omega

/-- **At each of the 25 written records of the full example `AtSwitch` has a member.** -/
theorem atSwitch_full (hr : r ∈ tableFullLit) :
    ∃ W, AtSwitch (stB r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) W r.l
      (stageOf r.g t₀) (KpR) (memR) (rowR) (plR) (fun i => r.lo.length + i) :=
  atSwitch_at r H (atB_says (List.all_eq_true.1 atB_full r hr)) t₀ oM oZ

/-- **At each of the 5 written records of the small example.** -/
theorem atSwitch_small (hr : r ∈ tableSmallLit) :
    ∃ W, AtSwitch (stB r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) W r.l
      (stageOf r.g t₀) (KpR) (memR) (rowR) (plR) (fun i => r.lo.length + i) :=
  atSwitch_at r H (atB_says (List.all_eq_true.1 atB_small r hr)) t₀ oM oZ

include K in
/-- **What the record gives there**: `Fit`; the frame's own clauses; and, for each kept member, its
record in the frame and its `Slots`. (`paid_names` and `paid_namesK` can be called alike.) -/
theorem paid_at : ∃ W, Fit r.cs r.l (stageOf r.g t₀) W (memR) (rowR) (plR) ∧
    FrameOK W W.parts.mainTailAt (W.parts.maskAt.getD 0 0) (W.parts.maskTailAt.getD 0 0)
      (W.parts.maskAt.getD 1 0) (W.parts.maskTailAt.getD 1 0) ∧
    ∀ a : {a // r.kp a}, W.kept[numAt r a]? = some (plB r (numAt r a)) ∧
      Slots (stageOf r.g t₀) (KpR) r.cs r.l W (fun i => r.lo.length + i) (memR) (rowR) (numAt r a)
        (plB r (numAt r a)) := by
  obtain ⟨W, A⟩ := atSwitch_at r H K t₀ oM oZ
  refine ⟨W, A.fit, paid_frame A, fun a => ?_⟩
  have hk : W.kept[numAt r a]? = some (plB r (numAt r a)) := by
    rw [kept_of_frame r K W A.frame, List.getElem?_map, List.getElem?_range (numAt_lt r a)]
    rfl
  exact ⟨hk, paid_slots A _ _ hk⟩

end

/-- `AtSwitch` at a record's made values, as one name with its letters. -/
abbrev AtRec (r : SwRow) (H : r.OK) (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ) (W : SwitchFrame) :
    Prop :=
  AtSwitch (stB r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) W r.l (stageOf r.g t₀)
    ((rowsPort r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀)).keep r.kp).Kp
    (slotNum r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp (numAt r))
    (slotRow r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp)
    (slotPl r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
      fun a => plB r (numAt r a))
    (fun i => r.lo.length + i)

/-- **With no premise left**: the record's promise is paid by the kernel's yes at the table
(`tableFullLit_ok`, `ok_says`). -/
theorem atSwitch_closed_full (r : SwRow) (hr : r ∈ tableFullLit) (t₀ : ℕ)
    (oM oZ : Fin r.lo.length → ℕ) : ∃ (H : r.OK) (W : SwitchFrame), AtRec r H t₀ oM oZ W :=
  ⟨SwRow.ok_says r (List.all_eq_true.1 tableFullLit_ok r hr),
    atSwitch_full r (SwRow.ok_says r (List.all_eq_true.1 tableFullLit_ok r hr)) t₀ oM oZ hr⟩

theorem atSwitch_closed_small (r : SwRow) (hr : r ∈ tableSmallLit) (t₀ : ℕ)
    (oM oZ : Fin r.lo.length → ℕ) : ∃ (H : r.OK) (W : SwitchFrame), AtRec r H t₀ oM oZ W :=
  ⟨SwRow.ok_says r (List.all_eq_true.1 tableSmallLit_ok r hr),
    atSwitch_small r (SwRow.ok_says r (List.all_eq_true.1 tableSmallLit_ok r hr)) t₀ oM oZ hr⟩

/-! ### The test can say no -/

set_option maxRecDepth 1000000 in
/-- A control: with the first sent message struck out the test says no at each record. -/
theorem atB_no_first : (tableFullLit.all fun r => !atB { r with l := r.l.tail }) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the two kept places in the other order the test says no at each record that
keeps two. There are 12 such records. -/
theorem atB_no_swap :
    ((tableFullLit.filter fun r => r.kept.length == 2).all fun r =>
      !atB { r with kept := r.kept.reverse }) = true ∧
    (tableFullLit.filter fun r => r.kept.length == 2).length = 12 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the message number 0 of the list in front laid among the kept places as well,
the test says no at each record. -/
theorem atB_no_more : (tableFullLit.all fun r =>
    !atB { r with kept := r.kept ++ [0] }) = true := by decide +kernel

end Johnson.G

#print axioms Johnson.G.stB_front
#print axioms Johnson.G.atB_says
#print axioms Johnson.G.slotsAll_at
#print axioms Johnson.G.atSwitch_at
#print axioms Johnson.G.atSwitch_full
#print axioms Johnson.G.atSwitch_small
#print axioms Johnson.G.atSwitch_closed_full
#print axioms Johnson.G.atSwitch_closed_small
#print axioms Johnson.G.paid_at
#print axioms Johnson.G.atB_no_first
#print axioms Johnson.G.atB_no_swap
#print axioms Johnson.G.atB_no_more
#print axioms Johnson.G.atB_full
#print axioms Johnson.G.atB_small
