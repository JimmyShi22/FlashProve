-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryGrounds.lean: the two grounds of OnBytes/Tie/EntryGround.lean.

They are the full size with a record (the `record…` values under OnBytes/Params/) and one small
example with a record (the `smallRecord…` values there: by the head of
OnBytes/Params/EntryStagesRecordSmall.lean typed for the first 32 lines of
prover/examples/target_small_f2_roomy/policy.txt). The small ground's block «within
the limits» is that of OnBytes/Tie/EntryRecord.lean with the names swapped.

-/
import OnBytes.Tie.EntryGround
import OnBytes.Params.EntryDescRecordSmall

set_option autoImplicit false

namespace OnBytes.Tie
open _root_.Run _root_.Run.PQ

/-- **The ground at the full size with a record and with work.** -/
def recordGround : EntryGround where
  lines := Params.recordLines
  q := Params.recordRead
  rs := Params.recordRounds
  spelled := rfl
  cfg32 := recordCfg_size
  params_at := record_params_at
  read_at := record_read_at
  rounds := Params.record_rounds
  within := withinX_record

/-- At the full size the ground's equation on the lines and its bytes are those of
OnBytes/Tie/ZeroRecordLines.lean. -/
theorem recordGround_saysLines : recordGround.SaysLines = SaysRecordLines := rfl

theorem recordGround_bytesAt : recordGround.bytesAt = recordBytesAt := rfl

/-- The Lean port's description of the chain, with an empty statement. -/
abbrev SL0 : Fmt.SpecX := Params.entrySpecOf Params.smallRecordRead Params.smallRecordRounds ByteArray.empty

/-- `SL0` meets the clauses of the library's limits that look at the rounds alone, and more than the
last of them asks: it opens each tree that it sends exactly once. -/
theorem roundsSL : (SL0.base.rounds.all (·.entry.roots ≤ 1) &&
    (allOpens SL0.base).all (fun o => (ownNo o).isSome) &&
    (List.range (nRoots SL0.base)).all (fun n =>
      ((allOpens SL0.base).filter fun o => ownNo o == some n).length == 1)) = true := by
  decide +kernel

/-- `SL0` meets the library's limits on the stored tables. -/
theorem okxSL : okX (rds SL0.base) (xdOf SL0 fun _ _ => ByteArray.empty).a
    (xdOf SL0 fun _ _ => ByteArray.empty).xs = true := by
  decide +kernel

/-- `SL0` meets the clause on the tables' shapes. -/
theorem shapesSL : (SL0.stored.flatten.all fun s =>
    s.sh.a == (xdOf SL0 fun _ _ => ByteArray.empty).a && s.salt == SL0.base.plan.salt &&
      decide (s.item ≤ 1)) = true := by
  decide +kernel

/-- `SL0` opens each table at most once. -/
theorem onceSL : (SL0.stored.flatten.map (·.item == 1)).Nodup := by
  decide +kernel

/-- At an empty statement the `base` of the Lean port's description meets all clauses of
`Fmt.Spec.ok` but two, which are not stated here: the one on how the parameter bytes begin, and the
one on given random bytes. -/
theorem clausesSL : (SL0.base.small && SL0.base.plan.ok &&
    (SL0.base.rounds.map (·.entry) == SL0.base.plan.rounds) &&
    (SL0.base.rounds.all fun r => r.entry.fits r.kind SL0.base.plan.samples) &&
    (SL0.base.cfg.size == 32) && !SL0.base.rounds.isEmpty &&
    decide (SL0.base.firstTree + ((SL0.base.rounds.map (·.entry.roots)).sum) < 2 ^ 16) &&
    (SL0.base.rounds.all fun r => r.opens.all fun o => decide (o.1.tree < 2 ^ 16)) &&
    (SL0.base.ownShapes.all fun x => SL0.base.shapeOf x.1 == some x.2) &&
    Fmt.roundsOk SL0.base.plan SL0.base.rand.isNone SL0.base.firstTree false 0 SL0.base.rounds &&
    (SL0.base.rounds.all fun r => r.opens.all fun o => Fmt.depthOK o.1.a) &&
    Fmt.saltLenOK SL0.base.plan.salt) = true := by
  decide +kernel

/-- At an empty statement the `base` of the Lean port's description is in order (`Fmt.Spec.ok`). The
clause on how the parameter bytes begin is the library's `Fmt.M1.params_head`, which holds for all
bytes that `Fmt.paramsBytes` spells. The clause on given random bytes asks nothing of this
description: its random bytes are in the file. -/
theorem okSL : SL0.base.ok = true := by
  have c := clausesSL
  simp only [Bool.and_eq_true] at c
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c3⟩, c4⟩, c5⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩ := c
  have c2 : (SL0.base.params.extract 0 (Fmt.paramsBytes SL0.base.plan SL0.base.cfg []).size ==
      Fmt.paramsBytes SL0.base.plan SL0.base.cfg []) = true :=
    _root_.Fmt.M1.params_head Params.smallRecordPlan Params.smallRecordCfg Params.smallRecordItems
  unfold Fmt.Spec.ok
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, rfl⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩

/-- The `base` of the Lean port's description is in order at every statement of at most 2 ^ 32 - 232
bytes. One alone of the clauses of `Fmt.Spec.ok` reads the statement, and of it the length alone
(`Fmt.Spec.small`). Nothing here on `Fmt.SpecX.ok`, whose clause on the stored tables takes the
statement too. -/
theorem small_record_baseOk (st : ByteArray) (hs : st.size + 88 ≤ 2 ^ 32 - 144) :
    (Params.entrySpecOf Params.smallRecordRead Params.smallRecordRounds st).base.ok = true := by
  have e : (Params.entrySpecOf Params.smallRecordRead Params.smallRecordRounds st).base.ok = SL0.base.ok := by
    unfold Fmt.Spec.ok Fmt.Spec.small
    have a : decide ((Params.entrySpecOf Params.smallRecordRead Params.smallRecordRounds st).base.statement.size
        + 88 ≤ 2 ^ 32 - 144) = true := decide_eq_true hs
    have b : decide (SL0.base.statement.size + 88 ≤ 2 ^ 32 - 144) = true := by decide
    rw [a, b]
    rfl
  rw [e]
  exact okSL

/-- The Lean port's description is within the limits at every statement under which its `base` is
in order. By `small_record_baseOk` it is so at every statement of at most 2 ^ 32 - 232 bytes. -/
theorem withinX_small_record (st : ByteArray)
    (hb : (Params.entrySpecOf Params.smallRecordRead Params.smallRecordRounds st).base.ok = true) :
    withinX (Params.entrySpecOf Params.smallRecordRead Params.smallRecordRounds st) = true := by
  unfold withinX _root_.Run.PQ.XD.ok _root_.Run.PQ.ok
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have r := roundsSL
  simp only [Bool.and_eq_true] at r
  have e : rds (inFile (Params.entrySpecOf Params.smallRecordRead Params.smallRecordRounds st).base)
      = rds SL0.base := _root_.Run.rds_congr _ _ rfl rfl
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hb, r.1.1⟩, r.1.2⟩, once_le _ _ r.2⟩, rfl⟩, ?_⟩, shapesSL⟩, rfl⟩, onceSL⟩
  show okX (rds (inFile (Params.entrySpecOf Params.smallRecordRead Params.smallRecordRounds st).base))
    (xdOf SL0 fun _ _ => ByteArray.empty).a (xdOf SL0 fun _ _ => ByteArray.empty).xs = true
  rw [e]
  exact okxSL

/-- The Lean port's description is within the limits at every statement of at most 2 ^ 32 - 232
bytes. -/
theorem small_record_within (st : ByteArray) (hs : st.size + 88 ≤ 2 ^ 32 - 144) :
    withinX (Params.entrySpecOf Params.smallRecordRead Params.smallRecordRounds st) = true :=
  withinX_small_record st (small_record_baseOk st hs)

/-- For every c of 32 bytes, the bytes spelled from the small plan and items at c are read as those
of a link's chain, and what is read is `linkAtCfg Params.smallRecordRead c`. (`record_read_at`,
names swapped.) -/
theorem small_record_read_at (c : ByteArray) (hc : c.size = 32) :
    Params.Link.read (Fmt.paramsBytes Params.smallRecordPlan c Params.smallRecordItems) =
      some (linkAtCfg Params.smallRecordRead c) :=
  Params.Link.read_of
    (Params.Given.read_spelled Params.smallRecordPlan c Params.smallRecordItems
      (Params.fit_of (by decide +kernel) hc (by decide +kernel)) (by decide +kernel))
    rfl (by decide +kernel) (by decide +kernel)

/-- **The ground at the small example (target_small_f2_roomy's lines), with a record and with
work.** -/
def smallRecordGround : EntryGround where
  lines := Params.smallRecordLines
  q := Params.smallRecordRead
  rs := Params.smallRecordRounds
  spelled := rfl
  cfg32 := by decide +kernel
  params_at := Params.small_record_params
  read_at := small_record_read_at
  rounds := Params.small_record_rounds
  within := withinX_small_record

/-- **FROM THE ENTRY FUNCTION, AT THE SMALL EXAMPLE (target_small_f2_roomy's lines).**
`EntryGround.main_zero_saysLines` at `smallRecordGround`. -/
theorem main_zero_saysSmallLines {args : List String} {s s' : OnBytes.Shell.World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ w, ZeroFacts args s s' w ∧
      (smallRecordGround.SaysLines w.r.pol → smallRecordGround.TiedAt w) :=
  smallRecordGround.main_zero_saysLines h

end OnBytes.Tie

#print axioms OnBytes.Tie.recordGround
#print axioms OnBytes.Tie.withinX_small_record
#print axioms OnBytes.Tie.smallRecordGround
#print axioms OnBytes.Tie.main_zero_saysSmallLines
