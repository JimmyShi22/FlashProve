-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchAtRow.lean: the law of the code switch on the kept messages, at a place's own
numbers: the caller of Johnson/Top/H/SwitchKeptIs.lean IS the caller of a record of
Johnson/Top/H0/K2Caller/Row.lean, at the reading of the open word by names.

Row.lean has one plain record of numbers for a place of the code switch (`SwRow`), a test on it with
code (`SwRow.ok`), and, where the test says yes, for all letters: the block's condition and that the
plan's two rounds cover the block's two errors. One of its letters is cutN, how the open word's
message and randomness are read off the new messages. The laws on the kept messages
(Johnson/Top/H/SwitchKeeps.lean, SwitchKeptKeeps.lean) stand at cutN := `cutSel` along the names of
a switch's frame. Here the two are laid together. Definitions, statements and proofs; no new
reasoning.
Main names (r: a record; H: what its test's yes says):
  `selAt`: the caller of SwitchKeptIs.lean at the record's numbers: the codes, the list in front,
    its members with a main row, the stage of the group in front, the joint radius, the kept
    members, the sending, as many positions as the planner's `baseCount`, the rider's code.
  `selAt_is`: it is `callerAt` of Row.lean at cutN := `cutSel`, by unfolding.
  `lettersSel`, `lettersSel_caller`: the letters as one value of Member.lean's `Letters`.
  `selAt_ok`, `selAt_covers`: so the block's condition holds at it, and the plan's two rounds cover
    its two errors.
  `selAt_written`: where the planner's own test says that the two rounds hold at the target, each of
    its two counts, as a share of the round's challenges with the bits of work among them, is at
    most 2⁻¹ ^ target (LevelWritten.lean). `selAt_written_full`, `selAt_written_small`: at each of
    the 25 and the 5 written records (Lit.lean).
  `selAt_three`: the three premises on numbers of `sel_keeps_law` and `kept_keeps_law` hold: the
    library's test at the sending; the members' depths; the joint radius against the members' radii.
  `kqOf_kept`, `selAt_S0_empty`: where only the record's kept places stand under kq (`kqOf r`,
    Member.lean) no old message stays open beside the held ones (`keptSel_S0_empty`,
    Johnson/Top/H/SwitchLeast.lean).
  `keptAt_full`, `keptAt_small`: at each written record every kept member has one answer and main
    rows over the base field (`CaseF`): more than Johnson/Top/H/SwitchSampleAt.lean asks of a kept
    member.
  `copyAt_full`, `copyAt_small`: and the message 1 + n of the record's sending has the shape of its
    kept member number n.
  `more_full`, `more_small`: A CAUTION, as a theorem: at some written record the sending holds more
    messages than the first and the kept members' copies.
Limits: those of the files named. The frame W, the numbers num, the places plOf and `Fit` stay
letters and a premise; a member of it at each written record: Johnson/G/SwitchFitLit.lean.
The written records are those of a proof's first chain. A bound on each round, on numbers: that only
challenges whose bits of work are 0 help a prover is not called here, and the rounds are the typed
block's with bits of work, not a file's written rounds. Nothing on soundness.

-/
import Johnson.Top.H.SwitchLeast
import Johnson.Top.H0.K2Caller.LevelWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Cb Iop IOR Johnson.Pack
open OnBytes.Tie.Pv.Switch VerifiableInference.Desc.First.K2Caller
open scoped ENNReal

variable (r : SwRow) (H : r.OK) (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ)
  (kq : Fin r.lo.length → Prop) [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsAt r H t₀ oM oZ).G.C.J)
  (Z : Evader GE ((rowsAt r H t₀ oM oZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf r.cs r.lo).sub kq).Msg × Wp)) (W : SwitchFrame)
  (num : {a // r.kp a} → ℕ) (plOf : {a // r.kp a} → KeptPlace)
  (Ft : Fit r.cs r.l (stageOf r.g t₀) W
    (slotNum r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp num)
    (slotRow r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp)
    (slotPl r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp plOf))
  (w₀ : ((heldAt r H t₀ oM oZ kq).foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "jR" => iJ (stageOf r.g t₀) W
  (slotNum r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp num)
  (slotRow r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp)
  (slotPl r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp plOf) r.cs r.l
  Ft.nameJ
set_option quotPrecheck false in
local notation "qR" => iQ (stageOf r.g t₀) W
  (slotNum r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp num)
  (slotRow r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp) r.cs r.l
  Ft.nameQ

/-- The caller of the laws on the kept messages, at the record's numbers. -/
noncomputable abbrev selAt : Cb.Pv.SendLocRide.Size GE :=
  switchSel (heldAt r H t₀ oM oZ kq) Sb sl Z A₀ r.cs r.l (jR) (qR)
    (baseCount r.set .request r.g) w₀ (portCode r.cs r.rider)

/-- It is the record's caller at the reading by names. -/
theorem selAt_is :
    selAt r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀ =
      callerAt r H t₀ oM oZ kq Sb sl Z A₀ (cutSel r.cs r.l (jR) (qR)) w₀ := rfl

/-- The letters as one value. -/
noncomputable def lettersSel : Letters r H where
  t₀ := t₀
  oM := oM
  oZ := oZ
  kq := kq
  B := B
  Kc := Kc
  St₀ := St₀
  Wp := Wp
  Sb := Sb
  sl := sl
  Z := Z
  E₀ := E₀
  A₀ := A₀
  cutN := cutSel r.cs r.l (jR) (qR)
  w₀ := w₀

theorem lettersSel_caller :
    (lettersSel r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀).caller =
      selAt r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀ := rfl

/-- The block's condition. -/
theorem selAt_ok : Cb.Pv.SendLocRide.OK (selAt r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀) :=
  row_ok r H t₀ oM oZ kq Sb sl Z A₀ _ w₀

/-- The plan's two rounds cover the block's two errors. -/
theorem selAt_covers :
    List.Forall₂ (Cb.Pv.Covered r.set .request)
      ((Err.toList (Cb.Pv.SendLocRide.eps (selAt r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀))).zip
        (Shape.chalList
          (Cb.Pv.SendLocRide.R (selAt r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀)).shape))
      r.specs :=
  row_covers r H t₀ oM oZ kq Sb sl Z A₀ _ w₀

include H in
/-- The three premises on numbers of the laws on the kept messages. -/
theorem selAt_three :
    allMeet r.cs r.l = true ∧
      (∀ i, r.mem i → aOf r.cs (r.lo.get i).1 ≤ (stageOf r.g t₀).C.a) ∧
      ∀ i, r.mem i → r.rad ≤ 2 ^ ((stageOf r.g t₀).C.a - aOf r.cs (r.lo.get i).1) * (r.lo.get i).2 +
        (2 ^ ((stageOf r.g t₀).C.a - aOf r.cs (r.lo.get i).1) - 1) :=
  ⟨H.meets, H.hA t₀, H.he t₀⟩

/-- **The level over the block's rounds with bits of work**, where the planner's own test says that
the record's two rounds hold at the target. Wn: the type of the nonces. -/
theorem selAt_written (Wn : Type) [Inhabited Wn] (h : r.ok = true) (hL : r.levelOK = true) :
    Err.Below
      (Err.grind (W := Wn) (bitsAt (lettersSel r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀))
        (Cb.Pv.SendLocRide.eps (selAt r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀)))
      ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) :=
  Letters.written Wn h hL (lettersSel r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀)

/-- At each of the 25 written records of the full example. -/
theorem selAt_written_full (Wn : Type) [Inhabited Wn] (hr : r ∈ tableFullLit) :
    Err.Below
      (Err.grind (W := Wn) (bitsAt (lettersSel r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀))
        (Cb.Pv.SendLocRide.eps (selAt r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀)))
      ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) :=
  written_full Wn r hr (lettersSel r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀)

/-- At each of the 5 written records of the small example. -/
theorem selAt_written_small (Wn : Type) [Inhabited Wn] (hr : r ∈ tableSmallLit) :
    Err.Below
      (Err.grind (W := Wn) (bitsAt (lettersSel r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀))
        (Cb.Pv.SendLocRide.eps (selAt r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀)))
      ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) :=
  written_small Wn r hr (lettersSel r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀)

include H in
/-- A kept place of the record is a member that is kept. -/
theorem kqOf_kept (i : Fin r.lo.length) (hi : kqOf r i) : ∃ h : r.mem i, r.kp ⟨i, h⟩ := by
  have h := H.kept i.val hi
  rw [List.getElem?_eq_getElem i.isLt] at h
  simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, hi⟩

/-- Where only the record's kept places stay open, no old message stays open beside the held
ones. -/
theorem selAt_S0_empty (hkq : ∀ i, kq i → kqOf r i) :
    IsEmpty (selAt r H t₀ oM oZ kq Sb sl Z A₀ W num plOf Ft w₀).sw.S₀.O :=
  keptSel_S0_empty r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
    (fun a _ => a.2) H.h0 kq Sb sl Z A₀ r.cs r.l W num plOf Ft _ w₀ _
    fun i hi => kqOf_kept r H i (hkq i hi)

/-! ### At the written records -/

set_option maxRecDepth 1000000 in
theorem keptNum_full : ∀ r ∈ tableFullLit, ∀ i ∈ r.kept, ((r.lo[i]?).map fun x =>
    decide (x.1.answers = 1) && decide (x.1.mainDeg = 1)) = some true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem keptNum_small : ∀ r ∈ tableSmallLit, ∀ i ∈ r.kept, ((r.lo[i]?).map fun x =>
    decide (x.1.answers = 1) && decide (x.1.mainDeg = 1)) = some true := by decide +kernel

include H in
theorem keptAt_of (hn : ∀ i ∈ r.kept, ((r.lo[i]?).map fun x =>
    decide (x.1.answers = 1) && decide (x.1.mainDeg = 1)) = some true) (a : {a // r.kp a}) :
    (r.lo.get a.1.1).1.answers = 1 ∧ CaseF (r.lo.get a.1.1).1 := by
  have h := hn a.1.1.val a.2
  rw [List.getElem?_eq_getElem a.1.1.isLt] at h
  simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, H.h0 a.1 a.2, h.2⟩

include H in
/-- At a written record of the full example a kept member has one answer and main rows over the base
field. -/
theorem keptAt_full (hr : r ∈ tableFullLit) (a : {a // r.kp a}) :
    (r.lo.get a.1.1).1.answers = 1 ∧ CaseF (r.lo.get a.1.1).1 :=
  keptAt_of r H (keptNum_full r hr) a

include H in
/-- The same at the small example. -/
theorem keptAt_small (hr : r ∈ tableSmallLit) (a : {a // r.kp a}) :
    (r.lo.get a.1.1).1.answers = 1 ∧ CaseF (r.lo.get a.1.1).1 :=
  keptAt_of r H (keptNum_small r hr) a

set_option maxRecDepth 1000000 in
/-- The message 1 + n of the sending has the shape of the kept member number n. -/
theorem copyAt_full : ∀ r ∈ tableFullLit, ∀ x ∈ r.kept.zipIdx,
    (r.l[1 + x.2]?).map (·.1) = (r.lo[x.1]?).map (·.1) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The same at the small example. -/
theorem copyAt_small : ∀ r ∈ tableSmallLit, ∀ x ∈ r.kept.zipIdx,
    (r.l[1 + x.2]?).map (·.1) = (r.lo[x.1]?).map (·.1) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A caution: a sending can hold more than the first message and the copies. -/
theorem more_full : ∃ r ∈ tableFullLit, 1 + r.kept.length < r.l.length := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The same at the small example. -/
theorem more_small : ∃ r ∈ tableSmallLit, 1 + r.kept.length < r.l.length := by decide +kernel

end Johnson.Top.H

#print axioms Johnson.Top.H.keptAt_full
#print axioms Johnson.Top.H.keptAt_small
#print axioms Johnson.Top.H.copyAt_full
#print axioms Johnson.Top.H.copyAt_small
#print axioms Johnson.Top.H.more_full
#print axioms Johnson.Top.H.more_small
#print axioms Johnson.Top.H.selAt_is
#print axioms Johnson.Top.H.lettersSel_caller
#print axioms Johnson.Top.H.selAt_ok
#print axioms Johnson.Top.H.selAt_covers
#print axioms Johnson.Top.H.selAt_three
#print axioms Johnson.Top.H.selAt_written
#print axioms Johnson.Top.H.selAt_written_full
#print axioms Johnson.Top.H.selAt_written_small
#print axioms Johnson.Top.H.kqOf_kept
#print axioms Johnson.Top.H.selAt_S0_empty
