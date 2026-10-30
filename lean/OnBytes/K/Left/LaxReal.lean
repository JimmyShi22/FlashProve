-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxReal.lean: what the lemmas on an entry file's view and stored openings ask of the
description at the use: at `entryXD G c` (OnBytes/TypedOracleCompiler/Slice/EntryDesc.lean), at the statement under
which the reader has read, at both grounds, at every digest c.

Main names:
  `real_ok`, `real_base_ok`: the description with the reader's statement put in meets the format's
    conditions: the reader's yes says so. At any ground and any hash.
  `real_items_full`, `real_items_small`: the stored openings, in the description's order, are of the
    statement's items 0 and 1.
  `real_item_le`, `real_items_nodup`, `real_once`: so each item is at most 1, and each table is
    opened once (`real_once_full`, `real_once_small`: the premise `honce` of `accept_view`,
    LaxView.lean).
  `real_depth_full`, `real_depth_small`: all stored tables have the depth `(entryXD G c).a`.
  `real_sto_full`, `real_sto_small`: depth and item together, as `viewX_cols_at` (LaxViewAt.lean)
    asks.
  `real_own_full`, `real_own_small`: the chain's own trees that the rounds open, in order: 0 to 4,
    at the small size 0 to 2; `real_own_nodup_full`, `real_own_nodup_small`: each once.

The facts at the grounds are the closed facts of OnBytes/Params/EntryFactsRecord.lean on the typed
rounds, carried to `entryXD` by unfolding: its rounds and stored openings do not hang on c.

Limits: values alone. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.TraceStrict
import OnBytes.TypedOracleCompiler.Slice.EntryDesc
import OnBytes.TypedOracleCompiler.Run.PageXTop
import OnBytes.Params.EntryFactsRecord

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Run (HId)

section
variable (G : EntryGround) (c : ByteArray) {h : HId} {st : ByteArray} {seen : Fmt.Seen}
  {b : ByteArray} {i : ℕ} {o : Fmt.ChainOut} {j : ℕ}
  (e : Fmt.readChainX (m := Id) h
    (TypedOracleCompiler.Run.PQ.withStatement (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) st)
    seen b i = some (o, j))

include e in
/-- The description with the reader's statement put in meets the format's conditions. -/
theorem real_ok :
    (⟨{ (entryXD G c).base with statement := st }, (entryXD G c).stored⟩ : Fmt.SpecX).ok = true :=
  (readX_trace h _ seen b i o j e).1

include e in
/-- So does its own part. -/
theorem real_base_ok : ({ (entryXD G c).base with statement := st } : Fmt.Spec).ok = true := by
  have hS := real_ok G c e
  unfold Fmt.SpecX.ok at hS
  simp only [Bool.and_eq_true] at hS
  exact hS.1.1

end

/-- The typed rounds' stored openings are of the statement's items 0 and 1, in this order. -/
theorem real_items :
    (Params.recordRounds.map (·.2)).flatten.map (·.item) = [0, 1] ∧
      (Params.smallRecordRounds.map (·.2)).flatten.map (·.item) = [0, 1] := by
  have h := Params.record_pair_places
  have e : ∀ l : List Fmt.Stored,
      l.map (·.item) = (l.map fun x => (x.item, x.lo, x.count)).map (·.1) := fun l => by
    rw [List.map_map]
    rfl
  exact ⟨by rw [e, h.1]; rfl, by rw [e, h.2]; rfl⟩

/-- At the full size, at every digest. -/
theorem real_items_full (c : ByteArray) :
    (entryXD recordGround c).stored.flatten.map (·.item) = [0, 1] := real_items.1

/-- At the small example, at every digest. -/
theorem real_items_small (c : ByteArray) :
    (entryXD smallRecordGround c).stored.flatten.map (·.item) = [0, 1] := real_items.2

/-- Each item is at most 1. -/
theorem real_item_le {D : XD} (h : D.stored.flatten.map (·.item) = [0, 1]) :
    ∀ s ∈ D.stored.flatten, s.item ≤ 1 := fun s hs => by
  have hm : s.item ∈ D.stored.flatten.map (·.item) := List.mem_map_of_mem hs
  rw [h] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  omega

/-- Each table is opened once. -/
theorem real_items_nodup {D : XD} (h : D.stored.flatten.map (·.item) = [0, 1]) :
    (D.stored.flatten.map (·.item)).Nodup := by
  rw [h]
  decide

/-- The same in the letters of `accept_view` (LaxView.lean): "is it the further table's?" is
answered
once with no and once with yes. -/
theorem real_once {D : XD} (h : D.stored.flatten.map (·.item) = [0, 1]) :
    (D.stored.flatten.map (·.item == 1)).Nodup := by
  have e : D.stored.flatten.map (·.item == 1) = (D.stored.flatten.map (·.item)).map (· == 1) := by
    rw [List.map_map]
    rfl
  rw [e, h]
  decide

/-- At the full size. -/
theorem real_once_full (c : ByteArray) :
    ((entryXD recordGround c).stored.flatten.map (·.item == 1)).Nodup :=
  real_once (real_items_full c)

/-- At the small example. -/
theorem real_once_small (c : ByteArray) :
    ((entryXD smallRecordGround c).stored.flatten.map (·.item == 1)).Nodup :=
  real_once (real_items_small c)

/-- All stored tables have the description's depth. -/
theorem real_depth_full (c : ByteArray) :
    ∀ s ∈ (entryXD recordGround c).stored.flatten, s.sh.a = (entryXD recordGround c).a :=
  fun s hs => by
    have h1 := List.all_eq_true.1 Params.record_stored_all s hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    have h2 : (entryXD recordGround c).a = 32 :=
      Params.record_depth.1.trans Params.record_depth.2
    rw [h1.1, h2]

/-- The same at the small example. -/
theorem real_depth_small (c : ByteArray) :
    ∀ s ∈ (entryXD smallRecordGround c).stored.flatten,
      s.sh.a = (entryXD smallRecordGround c).a := fun s hs => by
    have h1 := List.all_eq_true.1 Params.small_record_stored_all s hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    have h2 : (entryXD smallRecordGround c).a = 23 :=
      Params.small_record_depth.1.trans Params.small_record_depth.2
    rw [h1.1, h2]

/-- Depth and item together. -/
theorem real_sto_full (c : ByteArray) : ∀ s ∈ (entryXD recordGround c).stored.flatten,
    s.sh.a = (entryXD recordGround c).a ∧ s.item ≤ 1 := fun s hs =>
  ⟨real_depth_full c s hs, real_item_le (real_items_full c) s hs⟩

/-- The same at the small example. -/
theorem real_sto_small (c : ByteArray) : ∀ s ∈ (entryXD smallRecordGround c).stored.flatten,
    s.sh.a = (entryXD smallRecordGround c).a ∧ s.item ≤ 1 := fun s hs =>
  ⟨real_depth_small c s hs, real_item_le (real_items_small c) s hs⟩

/-- The chain's own trees that the rounds open, in order. -/
theorem real_own_full (c : ByteArray) :
    ((entryXD recordGround c).base.rounds.flatMap fun r =>
      r.opens.filterMap _root_.Run.PQ.ownNo) = [0, 1, 2, 3, 4] := by
  have h := Params.record_opens_own.1
  show ((Params.recordRounds.map (·.1)).flatMap fun r =>
    r.opens.filterMap _root_.Run.PQ.ownNo) = _
  rw [List.flatMap_map]
  exact h

/-- The same at the small example. -/
theorem real_own_small (c : ByteArray) :
    ((entryXD smallRecordGround c).base.rounds.flatMap fun r =>
      r.opens.filterMap _root_.Run.PQ.ownNo) = [0, 1, 2] := by
  have h := Params.record_opens_own.2
  show ((Params.smallRecordRounds.map (·.1)).flatMap fun r =>
    r.opens.filterMap _root_.Run.PQ.ownNo) = _
  rw [List.flatMap_map]
  exact h

/-- Each once. -/
theorem real_own_nodup_full (c : ByteArray) :
    ((entryXD recordGround c).base.rounds.flatMap fun r =>
      r.opens.filterMap _root_.Run.PQ.ownNo).Nodup := by
  rw [real_own_full]
  decide

/-- The same at the small example. -/
theorem real_own_nodup_small (c : ByteArray) :
    ((entryXD smallRecordGround c).base.rounds.flatMap fun r =>
      r.opens.filterMap _root_.Run.PQ.ownNo).Nodup := by
  rw [real_own_small]
  decide

end OnBytes.K.Left
