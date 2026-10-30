-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryRecord.lean: at the full size with a record: the entry's description is within
the library's limits, as theorems.

First that. Then: a yes of
`Entry.check` at the typed bytes ⇒ the library's compiled verifier accepts the very chain on whose
view the check decided.

Not claimed. The decision is the block's own, at the two tables' keys (answers and seeds): of that
protocol no soundness is stated here; see the head of OnBytes/Slice/FullRecTable.lean.

-/
import Fmt.M1SpecKnownProofs
import Run.PlanPullM1
import OnBytes.Params.EntryDescRecord
import OnBytes.Tie.SpecXBase
import OnBytes.Tie.EntryWith

set_option autoImplicit false

namespace OnBytes.Tie
open _root_.Run _root_.Run.PQ

/-- The typed description of the chain (`Params.entrySpecOf`), with an empty statement. -/
abbrev RL0 : Fmt.SpecX := Params.entrySpecOf Params.recordRead Params.recordRounds ByteArray.empty

/-- `RL0` meets the clauses of the library's limits that look at the rounds alone, and more than the
last of them asks: it opens each tree that it sends exactly once. -/
theorem roundsRL : (RL0.base.rounds.all (·.entry.roots ≤ 1) &&
    (allOpens RL0.base).all (fun o => (ownNo o).isSome) &&
    (List.range (nRoots RL0.base)).all (fun n =>
      ((allOpens RL0.base).filter fun o => ownNo o == some n).length == 1)) = true := by
  decide +kernel

/-- `RL0` meets the library's limits on the stored tables. -/
theorem okxRL : okX (rds RL0.base) (xdOf RL0 fun _ _ => ByteArray.empty).a
    (xdOf RL0 fun _ _ => ByteArray.empty).xs = true := by
  decide +kernel

/-- `RL0` meets the clause on the tables' shapes. -/
theorem shapesRL : (RL0.stored.flatten.all fun s =>
    s.sh.a == (xdOf RL0 fun _ _ => ByteArray.empty).a && s.salt == RL0.base.plan.salt &&
      decide (s.item ≤ 1)) = true := by
  decide +kernel

/-- `RL0` opens each table at most once. -/
theorem onceRL : (RL0.stored.flatten.map (·.item == 1)).Nodup := by
  decide +kernel

/-- At an empty statement the `base` of the typed description meets all clauses of
`Fmt.Spec.ok` but two, which are not stated here: the one on how the parameter bytes begin, and the
one on given random bytes. -/
theorem clausesRL : (RL0.base.small && RL0.base.plan.ok &&
    (RL0.base.rounds.map (·.entry) == RL0.base.plan.rounds) &&
    (RL0.base.rounds.all fun r => r.entry.fits r.kind RL0.base.plan.samples) &&
    (RL0.base.cfg.size == 32) && !RL0.base.rounds.isEmpty &&
    decide (RL0.base.firstTree + ((RL0.base.rounds.map (·.entry.roots)).sum) < 2 ^ 16) &&
    (RL0.base.rounds.all fun r => r.opens.all fun o => decide (o.1.tree < 2 ^ 16)) &&
    (RL0.base.ownShapes.all fun x => RL0.base.shapeOf x.1 == some x.2) &&
    Fmt.roundsOk RL0.base.plan RL0.base.rand.isNone RL0.base.firstTree false 0 RL0.base.rounds &&
    (RL0.base.rounds.all fun r => r.opens.all fun o => Fmt.depthOK o.1.a) &&
    Fmt.saltLenOK RL0.base.plan.salt) = true := by
  decide +kernel

/-- At an empty statement the `base` of the typed description is in order (`Fmt.Spec.ok`). The
clause on how the parameter bytes begin is the library's `Fmt.M1.params_head`, which holds for all
bytes that `Fmt.paramsBytes` spells. The clause on given random bytes asks nothing of this
description: its random bytes are in the file. -/
theorem okRL : RL0.base.ok = true := by
  have c := clausesRL
  simp only [Bool.and_eq_true] at c
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c3⟩, c4⟩, c5⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩ := c
  have c2 : (RL0.base.params.extract 0 (Fmt.paramsBytes RL0.base.plan RL0.base.cfg []).size ==
      Fmt.paramsBytes RL0.base.plan RL0.base.cfg []) = true :=
    _root_.Fmt.M1.params_head Params.recordPlan Params.recordCfg Params.recordItems
  unfold Fmt.Spec.ok
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, rfl⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩

/-- The `base` of the typed description is in order at every statement of at most 2 ^ 32 - 232
bytes. One alone of the clauses of `Fmt.Spec.ok` reads the statement, and of it the length alone
(`Fmt.Spec.small`). Nothing here on `Fmt.SpecX.ok`, whose clause on the stored tables takes the
statement too. -/
theorem record_baseOk (st : ByteArray) (hs : st.size + 88 ≤ 2 ^ 32 - 144) :
    (Params.entrySpecOf Params.recordRead Params.recordRounds st).base.ok = true := by
  have e : (Params.entrySpecOf Params.recordRead Params.recordRounds st).base.ok = RL0.base.ok := by
    unfold Fmt.Spec.ok Fmt.Spec.small
    have a : decide ((Params.entrySpecOf Params.recordRead Params.recordRounds st).base.statement.size
        + 88 ≤ 2 ^ 32 - 144) = true := decide_eq_true hs
    have b : decide (RL0.base.statement.size + 88 ≤ 2 ^ 32 - 144) = true := by decide
    rw [a, b]
    rfl
  rw [e]
  exact okRL

/-- The typed description is within the limits at every statement under which its `base` is
in order. By `record_baseOk` it is so at every statement of at most 2 ^ 32 - 232 bytes. -/
theorem withinX_record (st : ByteArray)
    (hb : (Params.entrySpecOf Params.recordRead Params.recordRounds st).base.ok = true) :
    withinX (Params.entrySpecOf Params.recordRead Params.recordRounds st) = true := by
  unfold withinX _root_.Run.PQ.XD.ok _root_.Run.PQ.ok
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have r := roundsRL
  simp only [Bool.and_eq_true] at r
  have e : rds (inFile (Params.entrySpecOf Params.recordRead Params.recordRounds st).base)
      = rds RL0.base := _root_.Run.rds_congr _ _ rfl rfl
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hb, r.1.1⟩, r.1.2⟩, once_le _ _ r.2⟩, rfl⟩, ?_⟩, shapesRL⟩, rfl⟩, onceRL⟩
  show okX (rds (inFile (Params.entrySpecOf Params.recordRead Params.recordRounds st).base))
    (xdOf RL0 fun _ _ => ByteArray.empty).a (xdOf RL0 fun _ _ => ByteArray.empty).xs = true
  rw [e]
  exact okxRL

/-- The typed description is within the limits at every statement of at most 2 ^ 32 - 232
bytes. -/
theorem record_within (st : ByteArray) (hs : st.size + 88 ≤ 2 ^ 32 - 144) :
    withinX (Params.entrySpecOf Params.recordRead Params.recordRounds st) = true :=
  withinX_record st (record_baseOk st hs)

/-- **AT THE PARAMETER BYTES TYPED FOR THE FULL SIZE WITH A RECORD AND WITH WORK
(`Params.recordBytes`), A FIRST ROOT OF 32 BYTES AND A FILE BELOW ABOUT 2^32 BYTES: NO OTHER
HYPOTHESIS.** If `Entry.check` says yes and returns `further`, then `Entry.read` returned
some r with that further table, and `CompiledAcceptsX` holds of r's chain, THE VERY ONE ON WHOSE
VIEW THE CHECK DECIDED, under the typed description at the statement on the two tables, under the
two roots, with the decision of r's own block. That the check says yes on some file at these bytes
is not shown. -/
theorem entry_record (first further : Params.TableName) (file : ByteArray)
    (h : Entry.check Params.recordBytes first file = .ok further) (h0 : first.root.size = 32)
    (hb : file.size + 16 ≤ 2 ^ 32 - 144) :
    ∃ r : Entry.EntryRead, Entry.read Params.recordRead first file = .ok r ∧ r.further = further ∧
      r.block.decides (Entry.start Params.recordRead) r.chain.view = true ∧
      CompiledAcceptsX (Params.entrySpecOf Params.recordRead Params.recordRounds
          (Params.Link.statement first further))
        (entryStatement first further) (r.block.decides (Entry.start Params.recordRead))
        first.root further.root r.chain.out := by
  obtain ⟨q, r, hq, hr, e1, hd⟩ := (entry_check_iff _ first further file).1 h
  obtain rfl : Params.recordRead = q := Option.some.inj (Params.record_read.symm.trans hq)
  obtain ⟨j, S, s', hS, hrd, _⟩ := entry_read_spec _ first file r hr
  obtain ⟨S', hS', himp⟩ := entry_read_compiled _ first file r hr hd
  obtain rfl : S = S' := congrArg (·.2) (Option.some.inj (hS.symm.trans hS'))
  have eS := Params.record_entrySpec_all hS
  have hok := readX_ok Fmt.formatHash _ _ file j _ (readIn_read _ file j _ s' r.chain hrd).1
  subst e1
  rw [eS] at hok himp
  have hwi := withinX_record _ (specX_base _ hok)
  exact ⟨r, hr, rfl, hd, himp hwi (smallFX_of_withinX _ hok hwi file hb) h0⟩

end OnBytes.Tie

#print axioms OnBytes.Tie.record_baseOk
#print axioms OnBytes.Tie.record_within
#print axioms OnBytes.Tie.withinX_record
#print axioms OnBytes.Tie.entry_record
